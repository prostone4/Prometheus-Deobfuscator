'use strict';

const { Kind, isExpression } = require('../lua/ast');
const { children, collect, walk, transform } = require('../lua/walk');
const { Evaluator, readsIn, writesIn } = require('../util/eval');
const { isLocalBinding, isGlobalName } = require('../lua/scope');
const C = require('../util/const');
const { copyRoots, soleValues, soleValueOf } = require('../util/flow');
const { Writes } = require('../util/writes');
const { LuaTable, LuaFunction } = require('../interp/values');

function preludeWrites(statement, inside, summary, copies) {
  const written = new Set();
  let escapes = false;

  const note = (binding) => {
    if (!binding) return;
    if (!isLocalBinding(binding)) {
      escapes = true;
      return;
    }
    written.add(binding);
    const origin = copies.get(binding);
    if (origin) written.add(origin);
  };

  walk(statement, {
    enter(node) {
      inside.set(node, statement);
      if (node.kind === Kind.FunctionDeclaration) escapes = true;
      return undefined;
    },
  });
  for (const binding of writesIn(statement, true, copies)) note(binding);
  for (const binding of summary.of(statement)) note(binding);
  for (const binding of readsIn(statement)) if (isLocalBinding(binding)) note(binding);
  return escapes ? null : written;
}

function readOutside(binding, going, inside) {
  for (const read of binding.reads || []) if (!going.has(inside.get(read))) return true;
  return false;
}

function liveValues(evaluator, going, inside) {
  const stack = [evaluator.rt.globals];
  for (const [binding, slot] of evaluator.values) {
    if (slot && readOutside(binding, going, inside)) stack.push(slot.value);
  }
  const live = new Set();
  while (stack.length) {
    const value = stack.pop();
    if (!(value instanceof LuaTable) || live.has(value)) continue;
    live.add(value);
    for (const [key, entry] of value.map) {
      stack.push(key);
      stack.push(entry);
    }
    if (value.metatable) stack.push(value.metatable);
  }
  return live;
}

function touchesLive(touched, live, cells, going, inside) {
  for (const owner of touched) {
    if (owner instanceof LuaTable) {
      if (live.has(owner)) return true;
      continue;
    }
    const binding = cells.get(owner);
    if (!binding || readOutside(binding, going, inside)) return true;
  }
  return false;
}

function settle(going, owned, inside) {
  for (let round = 0; round < owned.size && going.size; round += 1) {
    let dropped = false;
    for (const statement of going) {
      let needed = false;
      for (const binding of owned.get(statement)) {
        if (binding) needed = readOutside(binding, going, inside);
        if (needed) break;
      }
      if (!needed) continue;
      going.delete(statement);
      dropped = true;
    }
    if (!dropped) break;
  }
}

function keepMutators(evaluator, going, owned, inside) {
  if (!evaluator.mutated.size) return;
  const cells = new Map();
  for (const [binding, cell] of evaluator.cells) cells.set(cell, binding);
  for (let round = 0; round < owned.size && going.size; round += 1) {
    const live = liveValues(evaluator, going, inside);
    let dropped = false;
    for (const statement of going) {
      const touched = evaluator.mutated.get(statement);
      if (!touched || !touchesLive(touched, live, cells, going, inside)) continue;
      going.delete(statement);
      dropped = true;
    }
    if (!dropped) break;
    settle(going, owned, inside);
  }
}

function dropPrelude(context, evaluator) {
  const prelude = evaluator.preludeStatements;
  if (!prelude.size) return 0;
  const copies = copyRoots(soleValues(context.chunk));
  const summary = new Writes(context.chunk, (root, into) => writesIn(root, into, copies), readsIn);
  const inside = new Map();
  const owned = new Map();
  for (const statement of prelude) {
    const written = preludeWrites(statement, inside, summary, copies);
    if (written) owned.set(statement, written);
  }
  const going = new Set(owned.keys());
  settle(going, owned, inside);
  keepMutators(evaluator, going, owned, inside);
  if (!going.size) return 0;
  const body = context.chunk.body;
  const before = body.statements.length;
  body.statements = body.statements.filter((statement) => !going.has(statement));
  return before - body.statements.length;
}

function guardedChildren(node) {
  const blocked = new Set();
  if (node.kind === Kind.CallStatement) blocked.add(node.expression);
  if (node.kind === Kind.Assignment) for (const t of node.targets) blocked.add(t);
  if (node.kind === Kind.FunctionDeclaration) blocked.add(node.target);
  return blocked;
}

function openChildren(node) {
  const expanding = new Set();
  const last = (list) => (list && list.length ? list[list.length - 1] : null);
  const mark = (child) => { if (child) expanding.add(child); };
  if (node.kind === Kind.Call || node.kind === Kind.MethodCall) mark(last(node.args));
  else if (node.kind === Kind.Return) mark(last(node.expressions));
  else if (node.kind === Kind.LocalDeclaration || node.kind === Kind.Assignment) {
    mark(last(node.expressions));
  } else if (node.kind === Kind.GenericFor) mark(last(node.expressions));
  else if (node.kind === Kind.Table) {
    const entry = last(node.entries);
    if (entry && entry.type === 'item') mark(entry.value);
  }
  return expanding;
}

function rootName(node) {
  let base = node;
  for (;;) {
    if (!base) return null;
    if (base.kind === Kind.Paren) { base = base.expression; continue; }
    if (base.kind === Kind.Index) { base = base.base; continue; }
    return base.kind === Kind.Name ? base : null;
  }
}

function isData(node) {
  if (!node) return false;
  if (C.isConstant(node)) return true;
  if (node.kind === Kind.Paren) return isData(node.expression);
  if (node.kind !== Kind.Table) return false;
  return (node.entries || []).every((entry) => {
    if (entry.type === 'item') return isData(entry.value);
    if (entry.type === 'key') return C.isConstant(entry.key) && isData(entry.value);
    return false;
  });
}

function isOwned(node) {
  if (spelledOut(node)) return true;
  const root = rootName(node);
  return !!root && !isGlobalName(root);
}

function peel(node) {
  let base = node;
  while (base && base.kind === Kind.Paren) base = base.expression;
  return base;
}

function spelledOut(node) {
  const base = peel(node);
  return !!base && (base.kind === Kind.Function || base.kind === Kind.Table);
}

function heldValue(evaluator, node) {
  if (!evaluator) return undefined;
  const seen = evaluator.evaluate(node);
  return seen && seen.ok ? seen.value : undefined;
}

function isOwn(node, values, seen = new Set()) {
  const base = peel(node);
  if (!base || seen.has(base)) return false;
  seen.add(base);
  if (base.kind === Kind.Function || base.kind === Kind.Table) return true;
  if (base.kind === Kind.Name) {
    if (isGlobalName(base)) return false;
    return isOwn(soleValueOf(values, base.binding), values, seen);
  }
  if (base.kind === Kind.Index) return isOwn(base.base, values, seen);
  return false;
}

function holdsOwn(node, sort, ctx) {
  if (isOwn(node, ctx.values)) return true;
  return heldValue(ctx.evaluator, node) instanceof sort;
}

function isRawRead(node, ctx) {
  const table = heldValue(ctx.evaluator, node.base);
  if (!(table instanceof LuaTable)) return false;
  const key = heldValue(ctx.evaluator, node.index);
  if (key === undefined || key === null) return false;
  return filed(table, key, new Set());
}

function filed(table, key, seen) {
  let at = table;
  while (at instanceof LuaTable && !seen.has(at)) {
    seen.add(at);
    if (at.get(key) !== undefined) return true;
    const meta = at.metatable;
    at = meta instanceof LuaTable ? meta.get('__index') : undefined;
  }
  return false;
}

function isAccessor(node, ctx) {
  if (node.kind === Kind.Index) {
    if (node.index && node.index.kind === Kind.String) return false;
    if (!isOwned(node.base)) return false;
    if (!holdsOwn(node.base, LuaTable, ctx)) return false;
    return isRawRead(node, ctx);
  }
  if (node.kind === Kind.Call) {
    if (!isOwned(node.base)) return false;
    if (!holdsOwn(node.base, LuaFunction, ctx)) return false;
    return (node.args || []).every((argument) => isData(argument));
  }
  return false;
}

const LOOPS = new Set([Kind.While, Kind.Repeat, Kind.NumericFor, Kind.GenericFor]);

function tablesPassed(evaluator, root) {
  const found = new Set();
  const note = (node) => {
    const base = peel(node);
    if (!base) return;
    if (base.kind === Kind.Name) {
      if (!base.binding) return;
      const cell = evaluator.cells.get(base.binding);
      if (cell && cell.value instanceof LuaTable) {
        found.add(base.binding);
        found.add(cell.value);
      }
      return;
    }
    const held = heldValue(evaluator, node);
    if (held instanceof LuaTable) found.add(held);
  };
  walk(root, {
    enter: (node) => {
      if (node.kind === Kind.Call) (node.args || []).forEach(note);
      else if (node.kind === Kind.MethodCall) {
        note(node.base);
        (node.args || []).forEach(note);
      }
      return undefined;
    },
  });
  return found;
}

function foldValues(evaluator, root, options = {}) {
  const skip = options.skip || new Set();
  const ctx = { evaluator, values: options.values || new Map() };
  const anyExpression = options.anyExpression === true;
  const counts = { folded: 0, strings: 0 };

  const visit = (node) => {
    const kept = evaluator.dirty;
    if (LOOPS.has(node.kind)) {
      const passed = tablesPassed(evaluator, node);
      if (passed.size) evaluator.dirty = kept ? new Set([...kept, ...passed]) : passed;
    }
    const blocked = guardedChildren(node);
    const expanding = openChildren(node);
    for (const child of children(node)) {
      const target = child.node;
      if (!target || skip.has(target)) continue;
      if (isExpression(target) && !blocked.has(target)
        && (anyExpression || isAccessor(target, ctx))) {
        const literal = evaluator.literalFor(target, expanding.has(target));
        if (literal) {
          if (child.index === null) child.parent[child.key] = literal;
          else child.parent[child.key][child.index] = literal;
          counts.folded += 1;
          if (literal.kind === Kind.String) counts.strings += 1;
          continue;
        }
      }
      const nested = target.kind === Kind.Function;
      if (nested) evaluator.depth += 1;
      visit(target);
      if (nested) evaluator.depth -= 1;
    }
    evaluator.dirty = kept;
  };

  visit(root);
  return counts;
}

function writeTargets(root) {
  const blocked = new Set();
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        for (const target of node.targets || []) blocked.add(target);
      } else if (node.kind === Kind.FunctionDeclaration && node.target) {
        blocked.add(node.target);
      }
      return undefined;
    },
  });
  return blocked;
}

function foldLookups(evaluator, root, context) {
  const counts = { folded: 0, strings: 0 };
  const blocked = writeTargets(root);
  transform(root, (node) => {
    if (blocked.has(node)) return node;
    const literal = evaluator.cacheLiteralFor(node);
    if (!literal) return node;
    counts.folded += 1;
    if (literal.kind === Kind.String) {
      counts.strings += 1;
      if (context && (counts.strings % 25 === 0 || counts.strings === 1)) {
        context.reportProgress('progress', { step: '03-strings', strings: counts.strings, folded: counts.folded });
      }
    }
    return literal;
  });
  return counts;
}

function run(context) {
  context.resolve();
  const counts = { folded: 0, strings: 0 };
  const evaluator = new Evaluator(context.chunk, context.options);

  const values = soleValues(context.chunk);

  evaluator.prepare((statement) => {
    const step = foldValues(evaluator, statement, { values });
    counts.folded += step.folded;
    counts.strings += step.strings;
    if (counts.strings > 0 && (counts.strings % 25 === 0 || counts.folded % 50 === 0)) {
      context.reportProgress('progress', { step: '03-strings', strings: counts.strings, folded: counts.folded });
    }
  });
  const cached = foldLookups(evaluator, context.chunk, context);
  counts.folded += cached.folded;
  counts.strings += cached.strings;
  context.evaluator = evaluator;
  context.reportProgress('progress', { step: '03-strings', strings: counts.strings, folded: counts.folded });
  if (counts.folded) {
    context.note(
      `resolved ${counts.folded} hidden constant(s), ${counts.strings} string(s)`,
      counts.folded,
    );
    context.bump('decrypt.constants', counts.folded);
    context.bump('decrypt.strings', counts.strings);
  }
  if (evaluator.skipped.length) {
    context.bump('decrypt.skippedStatements', evaluator.skipped.length);
  }
  context.resolve();
  const dropped = dropPrelude(context, evaluator);
  if (dropped) {
    context.note(`removed the ${dropped}-statement decoder prelude`, dropped);
    context.bump('decrypt.preludeRemoved', dropped);
    context.resolve();
  }
}

module.exports = { name: '03-str', run, Evaluator, C };
