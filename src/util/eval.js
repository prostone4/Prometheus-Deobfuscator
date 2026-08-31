'use strict';

const { Kind } = require('../lua/ast');
const { walk, children } = require('../lua/walk');
const { Interpreter } = require('../interp/interpreter');
const V = require('../interp/values');
const ops = require('../interp/ops');
const effects = require('../interp/effects');
const C = require('./const');
const { Writes, declaredIn } = require('./writes');
const { Positions } = require('./order');
const { isLocalBinding } = require('../lua/scope');
const { soleValues, soleValueOf, copyRoots } = require('./flow');

const GLOBALS = new Set([
  'string', 'table', 'math', 'bit', 'bit32', 'utf8',
  'type', 'tostring', 'tonumber', 'select', 'unpack', 'ipairs', 'pairs', 'next',
  'rawget', 'rawset', 'rawequal', 'rawlen', 'setmetatable', 'getmetatable',
  'assert', 'pcall', '_VERSION', '_ENV',
]);

function pureEnv(rt) {
  const env = new V.LuaTable();
  for (const name of GLOBALS) {
    const value = rt.globals.get(name);
    if (value !== undefined) env.set(name, value);
  }
  const meta = new V.LuaTable();
  meta.set('__index', (_, args) => {
    const missing = new V.LuaError(`unknown global '${String(args[1])}'`);
    missing.sandbox = true;
    throw missing;
  });
  env.metatable = meta;
  return env;
}

const isScalar = (value) => value === undefined || typeof value === 'boolean'
  || typeof value === 'number' || typeof value === 'string';

const PRIME_LIMIT = 20000;

function writesIn(root, intoFunctions, copies) {
  const written = new Set();
  const noteTarget = (target) => {
    let node = target;
    while (node && node.kind === Kind.Paren) node = node.expression;
    if (!node) return;
    if (node.kind === Kind.Name) {
      if (node.binding) written.add(node.binding);
      return;
    }
    let base = node;
    while (base && (base.kind === Kind.Index || base.kind === Kind.Paren)) {
      base = base.base || base.expression;
    }
    if (!base || base.kind !== Kind.Name || !base.binding) return;
    written.add(base.binding);
    const origin = copies ? copies.get(base.binding) : undefined;
    if (origin) written.add(origin);
  };
  walk(root, {
    enter: (node) => {
      if (node !== root && node.kind === Kind.Function && !intoFunctions) return false;
      if (node.kind === Kind.Assignment) (node.targets || []).forEach(noteTarget);
      else if (node.kind === Kind.LocalDeclaration || node.kind === Kind.GenericFor
        || node.kind === Kind.Function) {
        for (const binding of node.bindings || []) if (binding) written.add(binding);
      } else if (node.kind === Kind.LocalFunction || node.kind === Kind.NumericFor) {
        if (node.binding) written.add(node.binding);
      }
      return undefined;
    },
  });
  return written;
}

function readsIn(root, intoFunctions = true) {
  const read = new Set();
  const written = new Set();
  const note = (binding, isWrite) => {
    if (!binding || read.has(binding) || written.has(binding)) return;
    if (isWrite) written.add(binding);
    else read.add(binding);
  };
  const visit = (node) => {
    if (!node || typeof node !== 'object') return;
    switch (node.kind) {
      case Kind.Name:
        note(node.binding, false);
        return;
      case Kind.Assignment:
        (node.expressions || []).forEach(visit);
        for (const slot of node.targets || []) {
          let inner = slot;
          while (inner && inner.kind === Kind.Paren) inner = inner.expression;
          if (!inner) continue;
          if (inner.kind === Kind.Name) note(inner.binding, true);
          else visit(inner);
        }
        return;
      case Kind.LocalDeclaration:
        (node.expressions || []).forEach(visit);
        for (const binding of node.bindings || []) note(binding, true);
        return;
      case Kind.NumericFor:
        visit(node.start);
        visit(node.limit);
        visit(node.step);
        note(node.binding, true);
        visit(node.body);
        return;
      case Kind.GenericFor:
        (node.expressions || []).forEach(visit);
        for (const binding of node.bindings || []) note(binding, true);
        visit(node.body);
        return;
      case Kind.Function:
        if (node !== root && !intoFunctions) return;
        for (const binding of node.bindings || []) note(binding, true);
        visit(node.body);
        return;
      case Kind.LocalFunction:
        note(node.binding, true);
        break;
      default:
        break;
    }
    for (const child of children(node)) visit(child.node);
  };
  visit(root);
  return read;
}

class Evaluator {
  constructor(chunk, options = {}) {
    this.chunk = chunk;
    this.options = options;
    this.rt = new Interpreter({ stepLimit: options.stepLimit || 40e6 });
    this.scope = this.rt.rootScope();
    this.values = new Map();
    this.declared = new Set();
    this.declarations = [];
    this.failures = [];
    this.preludeStatements = new Set();
    this.mutated = new Map();
    this.skipped = [];
    this.unfoldable = new Set();
    this.cells = new Map();
    this.tainted = new Set();
    this.lastWrite = new Map();
    this.point = 0;
    this.pointWrites = null;
    this.dirty = null;
    this.depth = 0;
    this.live = false;
    this.copying = false;
    this.impure = new Set();
    this.caches = new Set();
    this.positions = null;
    this.holders = null;
    this.parents = null;

    this.soleValues = soleValues(chunk);

    this.copies = copyRoots(this.soleValues);
    this.reading = new Set();

    this.summary = new Writes(
      chunk,
      (root, intoFunctions) => writesIn(root, intoFunctions, this.copies),
      readsIn,
    );
    const table = this.rt.globals.get('table');
    if (table) {
      for (const name of ['insert', 'remove', 'sort']) {
        const fn = table.get(name);
        if (fn) this.impure.add(fn);
      }
    }
    for (const name of ['rawset', 'setmetatable', 'collectgarbage']) {
      const fn = this.rt.globals.get(name);
      if (fn) this.impure.add(fn);
    }
    this.rt.globals.set('_ENV', pureEnv(this.rt));
  }

  usesChunkVararg(node) {
    if (!node || typeof node !== 'object') return false;
    if (node.kind === Kind.Vararg) return true;
    if (node.kind === Kind.Function) return false;
    for (const child of children(node)) {
      if (this.usesChunkVararg(child.node)) return true;
    }
    return false;
  }

  isDeterministic(statement) {
    if (this.usesChunkVararg(statement)) return false;

    const declaredHere = declaredIn(statement);
    let deterministic = true;
    walk(statement, {
      enter: (node) => {
        if (!deterministic) return false;
        if (node.kind !== Kind.Name) return undefined;
        const binding = node.binding;
        if (!binding) {
          deterministic = false;
          return false;
        }
        if (binding.kind === 'global') {
          if (!GLOBALS.has(binding.name)) deterministic = false;
          return undefined;
        }

        if (this.declared.has(binding)) return undefined;
        if (declaredHere.has(binding)) return undefined;
        deterministic = false;
        return false;
      },
    });
    return deterministic;
  }

  declaresFrom(statement) {
    if (statement.kind === Kind.LocalDeclaration && statement.bindings) {
      for (let i = 0; i < statement.bindings.length; i += 1) {
        this.note(statement.bindings[i], statement.names[i]);
      }
    } else if (statement.kind === Kind.LocalFunction && statement.binding) {
      this.note(statement.binding, statement.name);
    }
  }

  note(binding, name) {
    if (!binding) return;
    this.declarations.push({ binding, name });
    this.declared.add(binding);
    const cell = this.scope.lookup(name);
    if (cell) this.cells.set(binding, cell);
  }

  finalizeValues() {
    const seen = new Map();
    for (const { binding, name } of this.declarations) {
      const cell = this.scope.lookup(name);
      if (!cell) continue;

      const previous = seen.get(name);
      if (previous) this.unfoldable.add(previous);
      seen.set(name, binding);
      this.values.set(binding, { value: cell.value });
    }
  }

  prepare(folder) {
    const statements = this.chunk.body.statements;
    this.mapWrites(statements);
    this.live = !!folder;
    for (let index = 0; index < statements.length; index += 1) {
      const statement = statements[index];
      this.point = index;
      if (folder) {
        this.depth = 0;
        this.dirty = null;

        this.pointWrites = new Set([
          ...writesIn(statement, true),
          ...this.mayChange(statement),
        ]);
        folder(statement, index);
      }
      if (statement.kind === Kind.Return) break;
      if (!this.isDeterministic(statement)) {
        this.skipped.push(statement);
        this.loseTrack(statement);
        continue;
      }
      try {
        const swallows = this.rt.swallows || 0;
        const seen = effects.witness(() => this.rt.execStatement(statement, this.scope));
        if ((this.rt.swallows || 0) !== swallows) {
          this.skipped.push(statement);
          this.loseTrack(statement);
          continue;
        }
        this.preludeStatements.add(statement);
        if (seen.older.size) this.mutated.set(statement, seen.older);
        this.declaresFrom(statement);
        this.keepTrack(statement);
        if (seen.value) break;
      } catch (error) {
        this.skipped.push(statement);
        this.preludeStatements.delete(statement);
        this.failures.push({ statement, error });
        this.loseTrack(statement);
        continue;
      }
    }
    this.live = false;
    this.finalizeValues();
    this.markUnfoldable();

    this.primeDecoders();
    return this;
  }

  mapWrites(statements) {
    statements.forEach((statement, index) => {
      for (const binding of writesIn(statement, true)) this.lastWrite.set(binding, index);
    });
  }

  loseTrack(statement) {
    for (const binding of this.mayChange(statement)) this.tainted.add(binding);
  }

  mayChange(statement) {
    const total = this.summary.of(statement);
    for (const binding of readsIn(statement)) {
      const cell = this.cells.get(binding);
      const value = cell ? cell.value : undefined;
      if (!(value instanceof V.LuaFunction) || !value.node) continue;
      for (const written of this.summary.writesOf(value.node)) total.add(written);
    }
    return total;
  }

  keepTrack(statement) {
    const written = writesIn(statement, false);
    if (!written.size) return;
    let dirty = false;

    for (const binding of readsIn(statement, false)) {
      if (this.tainted.has(binding)) { dirty = true; break; }
    }
    for (const binding of written) {
      if (dirty) this.tainted.add(binding);
      else this.tainted.delete(binding);
    }
  }

  usable(binding) {
    if (!binding || this.tainted.has(binding)) return false;
    if (this.pointWrites && this.pointWrites.has(binding)) return false;
    if (this.depth === 0) return true;
    const last = this.lastWrite.has(binding) ? this.lastWrite.get(binding) : -1;
    return last < this.point;
  }

  markUnfoldable() {
    for (const [binding] of this.values) {
      for (const write of binding.writes) {
        if (!this.isInPrelude(write)) {
          this.unfoldable.add(binding);
          break;
        }
      }
    }
    const assignedTables = new Set();
    walk(this.chunk, {
      enter: (node) => {
        if (node.kind !== Kind.Assignment) return undefined;
        for (const target of node.targets) {
          if (target.kind !== Kind.Index) continue;
          let base = target.base;
          while (base && base.kind === Kind.Index) base = base.base;
          if (base && base.kind === Kind.Name && base.binding && !this.isInPrelude(node)) {
            assignedTables.add(base.binding);
          }
        }
        return undefined;
      },
    });
    for (const binding of assignedTables) this.unfoldable.add(binding);

    for (const [binding, slot] of this.values) {
      if (isScalar(slot.value)) continue;
      for (const read of binding.reads) {
        if (this.isInPrelude(read)) continue;
        const parent = this.parentOf(read);
        const ok = parent && ((parent.kind === Kind.Index && parent.base === read)
          || ((parent.kind === Kind.Call || parent.kind === Kind.MethodCall) && parent.base === read));
        if (!ok) {
          this.unfoldable.add(binding);
          break;
        }
      }
    }
  }

  parentOf(node) {
    if (!this.parents) {
      const parents = new Map();
      const stack = [this.chunk];
      while (stack.length) {
        const at = stack.pop();
        for (const child of children(at)) {
          parents.set(child.node, at);
          stack.push(child.node);
        }
      }
      this.parents = parents;
    }
    return this.parents.get(node);
  }

  isInPrelude(node) {
    for (let at = node; at; at = this.parentOf(at)) {
      if (this.preludeStatements.has(at)) return true;
    }
    return false;
  }

  lookup(binding) {
    if (!binding || this.unfoldable.has(binding) || this.tainted.has(binding)) return undefined;
    return this.values.get(binding);
  }

  fromWrittenValue(binding, depth) {
    if (!binding || binding.kind === 'global') return { ok: false };
    if (this.reading.has(binding) || this.unfoldable.has(binding)) return { ok: false };
    if (this.tainted.has(binding)) return { ok: false };
    const written = soleValueOf(this.soleValues, binding);
    if (!written) return { ok: false };

    const fixed = C.isConstant(written) && (binding.writes || []).length === 0;
    if (!fixed && written.kind !== Kind.Function && written.kind !== Kind.Name) {
      return { ok: false };
    }
    this.reading.add(binding);
    try {
      return this.evaluate(written, depth + 1);
    } finally {
      this.reading.delete(binding);
    }
  }

  orCopy(node, found, depth) {
    if (found.ok || !this.copying) return found;
    const binding = node.binding;
    if (!binding || this.reading.has(binding)) return found;
    const value = this.copyOf(node);
    if (!value) return found;
    this.reading.add(binding);
    try {
      return this.evaluate(value, depth + 1);
    } finally {
      this.reading.delete(binding);
    }
  }

  evaluate(node, depth = 0) {
    if (!node || depth > 64) return { ok: false };
    switch (node.kind) {
      case Kind.Nil: return { ok: true, value: undefined };
      case Kind.True: return { ok: true, value: true };
      case Kind.False: return { ok: true, value: false };
      case Kind.Number: return { ok: true, value: node.value };
      case Kind.String: return { ok: true, value: node.value };
      case Kind.Paren: return this.evaluate(node.expression, depth + 1);
      case Kind.Function:
        return this.protect(() => this.rt.eval(node, this.scope));
      case Kind.Name: {
        if (node.binding && node.binding.kind === 'global') {
          if (!GLOBALS.has(node.binding.name)) return { ok: false };
          return { ok: true, value: this.rt.globals.get(node.binding.name) };
        }
        if (this.live) {
          const cell = this.cells.get(node.binding);
          if (cell && this.usable(node.binding)) return { ok: true, value: cell.value };
          return this.orCopy(node, this.fromWrittenValue(node.binding, depth), depth);
        }
        const slot = this.lookup(node.binding);
        if (slot) return { ok: true, value: slot.value };
        return this.orCopy(node, this.fromWrittenValue(node.binding, depth), depth);
      }
      case Kind.Table: {
        const table = new V.LuaTable();
        const entries = node.entries || [];
        let slot = 1;
        for (let i = 0; i < entries.length; i += 1) {
          const entry = entries[i];
          if (entry.type === 'key') {
            const key = this.evaluate(entry.key, depth + 1);
            const value = this.evaluate(entry.value, depth + 1);
            if (!key.ok || !value.ok || key.value === undefined) return { ok: false };
            const stored = this.protect(() => table.set(key.value, value.value));
            if (!stored.ok) return { ok: false };
            continue;
          }
          const value = this.evaluate(entry.value, depth + 1);
          if (!value.ok) return { ok: false };

          const spread = i === entries.length - 1 && value.values ? value.values : [value.value];
          for (const one of spread) {
            table.set(slot, one);
            slot += 1;
          }
        }
        return { ok: true, value: table };
      }
      case Kind.Index: {
        if (this.staleTable(node.base)) return { ok: false };
        const base = this.evaluate(node.base, depth + 1);
        const key = this.evaluate(node.index, depth + 1);
        if (!base.ok || !key.ok) return { ok: false };
        if (!(base.value instanceof V.LuaTable)) return { ok: false };
        if (this.staleValue(base.value)) return { ok: false };
        return this.protect(() => ops.index(this.rt, base.value, key.value));
      }
      case Kind.Binary: {
        if (node.operator === 'and' || node.operator === 'or') {
          const lhs = this.evaluate(node.lhs, depth + 1);
          if (!lhs.ok) return { ok: false };
          const takeRhs = node.operator === 'and' ? V.truthy(lhs.value) : !V.truthy(lhs.value);
          return takeRhs ? this.evaluate(node.rhs, depth + 1) : lhs;
        }
        const lhs = this.evaluate(node.lhs, depth + 1);
        const rhs = this.evaluate(node.rhs, depth + 1);
        if (!lhs.ok || !rhs.ok) return { ok: false };
        return this.protect(() => this.applyBinary(node.operator, lhs.value, rhs.value));
      }
      case Kind.Unary: {
        const argument = this.evaluate(node.argument, depth + 1);
        if (!argument.ok) return { ok: false };
        return this.protect(() => {
          if (node.operator === '-') return ops.unaryMinus(this.rt, argument.value);
          if (node.operator === 'not') return !V.truthy(argument.value);
          return ops.length(this.rt, argument.value);
        });
      }
      case Kind.Call: {
        const callee = this.evaluate(node.base, depth + 1);
        if (!callee.ok || !V.isCallable(callee.value)) return { ok: false };
        if (this.readsStale(callee.value)) return { ok: false };
        const args = this.evaluateList(node.args, depth + 1);
        if (!args.ok) return { ok: false };
        return this.callDeterministic(callee.value, args.values);
      }
      case Kind.MethodCall: {
        if (this.staleTable(node.base)) return { ok: false };
        const self = this.evaluate(node.base, depth + 1);
        if (!self.ok || this.staleValue(self.value)) return { ok: false };
        const args = this.evaluateList(node.args, depth + 1);
        if (!args.ok) return { ok: false };
        const method = this.protect(() => ops.index(this.rt, self.value, node.method));
        if (!method.ok || !V.isCallable(method.value)) return { ok: false };
        if (this.readsStale(method.value)) return { ok: false };
        return this.callDeterministic(method.value, [self.value, ...args.values]);
      }
      default:
        return { ok: false };
    }
  }

  applyBinary(operator, a, b) {
    switch (operator) {
      case '..': return ops.concat(this.rt, a, b);
      case '==': return ops.equals(this.rt, a, b);
      case '~=': return !ops.equals(this.rt, a, b);
      case '<': return ops.lessThan(this.rt, a, b);
      case '>': return ops.lessThan(this.rt, b, a);
      case '<=': return ops.lessOrEqual(this.rt, a, b);
      case '>=': return ops.lessOrEqual(this.rt, b, a);
      default: return ops.arith(this.rt, operator, a, b);
    }
  }

  evaluateList(nodes, depth) {
    const list = nodes || [];
    const values = [];
    for (let i = 0; i < list.length; i += 1) {
      const result = this.evaluate(list[i], depth);
      if (!result.ok) return { ok: false };
      if (i === list.length - 1 && result.values) values.push(...result.values);
      else values.push(result.value);
    }
    return { ok: true, values };
  }

  callDeterministic(fn, args) {
    if (this.impure.has(fn)) return { ok: false };
    const outcome = effects.record(() => this.callStable(fn, args));

    if (outcome.value.ok) {
      for (const written of outcome.writes) {
        if (written instanceof V.LuaTable) this.caches.add(written);
      }
    }
    return outcome.value;
  }

  callStable(fn, args) {
    const swallows = this.rt.swallows || 0;
    const opening = effects.attempt(() => this.protect(() => this.rt.call(fn, args)));
    const first = opening.value;
    if (!first.ok || (this.rt.swallows || 0) !== swallows) {
      effects.undo(opening);
      return { ok: false };
    }
    const trial = effects.attempt(() => this.protect(() => this.rt.call(fn, args)));
    const second = trial.value;
    effects.undo(trial);
    let stable = second.ok && !trial.escaped && first.value.length === second.value.length;
    const same = (a, b) => a === b || (Number.isNaN(a) && Number.isNaN(b));
    for (let i = 0; stable && i < first.value.length; i += 1) {
      if (!isScalar(first.value[i]) || !same(first.value[i], second.value[i])) stable = false;
    }
    if (!stable) {
      effects.undo(opening);
      return { ok: false };
    }
    effects.commit(opening);
    return { ok: true, value: first.value[0], values: first.value };
  }

  staleValue(value) {
    return !!this.dirty && this.dirty.has(value);
  }

  staleTable(node) {
    if (!this.dirty) return false;
    let base = node;
    while (base && base.kind === Kind.Paren) base = base.expression;
    return !!base && base.kind === Kind.Name && this.dirty.has(base.binding);
  }

  readsStale(value) {
    if (!(value instanceof V.LuaFunction) || !value.node) return false;
    for (const binding of this.summary.readsOf(value.node)) {
      if (!this.usable(binding)) return true;
      if (this.dirty && this.dirty.has(binding)) return true;
    }
    return false;
  }

  protect(fn) {
    const budget = this.rt.steps;
    try {
      return { ok: true, value: fn() };
    } catch (error) {
      this.rt.steps = budget;
      return { ok: false };
    }
  }

  evaluateCopied(node) {
    const kept = this.copying;
    this.copying = true;
    try {
      let inner = node;
      for (let step = 0; step <= 8; step += 1) {
        const direct = this.evaluate(inner);
        if (direct.ok) return direct;
        const next = this.copyOf(inner);
        if (!next) return { ok: false };
        inner = next;
      }
      return { ok: false };
    } finally {
      this.copying = kept;
    }
  }

  copyOf(node) {
    let inner = node;
    while (inner && inner.kind === Kind.Paren) inner = inner.expression;
    if (!inner || inner.kind !== Kind.Name) return null;
    const binding = inner.binding;
    if (!binding || !isLocalBinding(binding)) return null;
    if ((binding.writes || []).length > 1) return null;
    const holder = this.copyHolders().get(binding);
    if (!holder) return null;
    if (!this.positions) this.positions = new Positions(this.chunk);
    if (!this.positions.precedes(holder.statement, inner)) return null;
    return holder.value;
  }

  copyHolders() {
    if (this.holders) return this.holders;
    const holders = new Map();
    const note = (binding, value, statement) => {
      if (!binding || !value) return;
      if (holders.has(binding)) holders.set(binding, null);
      else holders.set(binding, { value, statement });
    };
    walk(this.chunk, {
      enter: (node) => {
        if (node.kind === Kind.LocalDeclaration) {
          const expressions = node.expressions || [];
          if (expressions.length === (node.names || []).length) {
            (node.bindings || []).forEach((binding, at) => note(binding, expressions[at], node));
          }
        } else if (node.kind === Kind.Assignment) {
          const targets = node.targets || [];
          const expressions = node.expressions || [];
          if (targets.length === expressions.length) {
            targets.forEach((target, at) => {
              if (target.kind === Kind.Name) note(target.binding, expressions[at], node);
            });
          }
        }
        return undefined;
      },
    });
    this.holders = holders;
    return holders;
  }

  primeDecoders() {
    this.depth = 0;
    this.pointWrites = null;
    this.dirty = null;
    let made = 0;
    const disturbed = new Set();
    walk(this.chunk, {
      enter: (node) => {
        if (made >= PRIME_LIMIT) return false;
        if (node.kind !== Kind.Call) return undefined;
        const args = node.args || [];
        if (!args.length || !args.every((argument) => C.isConstant(argument)
          || argument.kind === Kind.Name)) return undefined;
        const decoder = this.decoderAt(node.base);
        if (!decoder || this.readsStale(decoder)) return undefined;
        made += 1;

        const trial = effects.record(() => {
          const given = [];
          for (const argument of args) {
            const value = this.evaluateCopied(argument);
            if (!value.ok) return { ok: false };
            given.push(value.value);
          }
          return this.callDeterministic(decoder, given);
        });
        for (const written of trial.writes) disturbed.add(written);
        if (!trial.value.ok) return undefined;
        for (const written of trial.writes) {
          if (written instanceof V.LuaTable) this.caches.add(written);
        }
        return undefined;
      },
    });
    this.distrust(disturbed);
    return made;
  }

  distrust(written) {
    const owners = new Map();
    for (const [binding, cell] of this.cells) owners.set(cell, binding);
    for (const thing of written) {
      const binding = owners.get(thing);
      if (binding) this.tainted.add(binding);
    }
    for (const [binding, slot] of this.values) {
      if (written.has(slot.value) && !this.caches.has(slot.value)) this.unfoldable.add(binding);
    }
  }

  alongCopies(node, accept) {
    let inner = node;
    for (let step = 0; step <= 8 && inner; step += 1) {
      while (inner && inner.kind === Kind.Paren) inner = inner.expression;
      if (!inner) return null;
      const direct = this.evaluate(inner);
      if (direct.ok) return accept(direct.value, null) ? direct.value : null;
      if (inner.kind !== Kind.Name || !isLocalBinding(inner.binding)) return null;
      const slot = this.values.get(inner.binding);
      if (slot && accept(slot.value, inner.binding)) return slot.value;
      inner = this.copyOf(inner);
    }
    return null;
  }

  decoderAt(node) {
    return this.alongCopies(node, (value, binding) => value instanceof V.LuaFunction
      && !!value.node
      && (!binding || (binding.writes || []).every((write) => this.isInPrelude(write))));
  }

  cacheAt(node) {
    return this.alongCopies(node, (value) => this.reachesCache(value));
  }

  reachesCache(table, depth = 0) {
    if (!(table instanceof V.LuaTable) || depth > 8) return false;
    if (this.caches.has(table)) return true;
    const meta = table.metatable;
    return meta ? this.reachesCache(meta.get('__index'), depth + 1) : false;
  }

  cacheLiteralFor(node) {
    if (!this.caches.size || !node || node.kind !== Kind.Index) return null;
    const key = this.evaluateCopied(node.index);
    if (!key.ok || key.value === undefined) return null;
    const table = this.cacheAt(node.base);
    if (!table) return null;
    const found = this.protect(() => ops.index(this.rt, table, key.value));
    if (!found.ok || !isScalar(found.value) || found.value === undefined) return null;
    return C.literalNode(found.value);
  }

  literalFor(node, expanding = false) {
    if (C.isConstant(node)) return null;
    const result = this.evaluate(node);
    if (!result.ok || !isScalar(result.value) || result.value === undefined) return null;
    if (expanding && result.values && result.values.length !== 1) return null;
    return C.literalNode(result.value);
  }
}

module.exports = { Evaluator, writesIn, readsIn };
