'use strict';

const { Kind } = require('../lua/ast');
const V = require('./values');
const ops = require('./ops');
const effects = require('./effects');

const { LuaError, LuaTable, LuaFunction, luaType, truthy } = V;

const BREAK = { signal: 'break' };
const CONTINUE = { signal: 'continue' };

class LuaLimitError extends Error {
  constructor(message) {
    super(message);
    this.name = 'LuaLimitError';
  }
}

class Scope {
  constructor(parent) {
    this.parent = parent;
    this.cells = new Map();
  }

  declare(name, value) {
    const cell = { value, stamp: effects.fresh() };
    this.cells.set(name, cell);
    return cell;
  }

  lookup(name) {
    let scope = this;
    while (scope) {
      const cell = scope.cells.get(name);
      if (cell) return cell;
      scope = scope.parent;
    }
    return null;
  }
}

class Interpreter {
  constructor(options = {}) {
    this.stepLimit = options.stepLimit === undefined ? 20e6 : options.stepLimit;
    this.callDepth = 0;
    this.lenient = options.lenient === true;
    this.maxCallDepth = options.maxCallDepth || 200;
    this.steps = 0;
    this.addresses = new WeakMap();
    this.nextAddress = 0x1000;
    this.stringMeta = undefined;
    this.globals = new LuaTable();
    this.output = [];
    require('./stdlib').install(this);
  }

  addressOf(value) {
    let address = this.addresses.get(value);
    if (address === undefined) {
      this.nextAddress += 0x30;
      address = this.nextAddress.toString(16);
      this.addresses.set(value, address);
    }
    return address;
  }

  metamethod(value, event) {
    let metatable;
    if (value instanceof LuaTable) metatable = value.metatable;
    else if (typeof value === 'string') metatable = this.stringMeta;
    else if (value && value.__metatable) metatable = value.__metatable;
    if (!metatable) return undefined;
    return metatable.get(event);
  }

  tick(count = 1) {
    this.steps += count;
    if (this.stepLimit && this.steps > this.stepLimit) {
      throw new LuaLimitError(`step limit exceeded (${this.stepLimit})`);
    }
  }

  call(fn, args) {
    if (typeof fn === 'function') {
      this.tick();
      return fn(this, args) || [];
    }
    if (!(fn instanceof LuaFunction)) {
      const handler = this.metamethod(fn, '__call');
      if (handler) return this.call(handler, [fn, ...args]);
      if (this.lenient && (fn === undefined || fn === null)) return [];
      throw new LuaError(`cannot call ${luaType(fn)}`);
    }
    if (this.callDepth >= this.maxCallDepth) throw new LuaError('stack overflow');
    this.callDepth += 1;
    try {
      return this.invoke(fn, args);
    } finally {
      this.callDepth -= 1;
    }
  }

  invoke(fn, args) {
    const node = fn.node;
    const scope = new Scope(fn.closure);
    const params = node.params || [];
    for (let i = 0; i < params.length; i += 1) scope.declare(params[i], args[i]);
    const frame = { varargs: node.isVararg ? args.slice(params.length) : [] };
    scope.frame = frame;
    const result = this.execBlock(node.body, scope);
    if (result && result.signal === 'return') return result.values;
    return [];
  }

  runChunk(chunk, args = []) {
    const fn = new LuaFunction(
      { kind: Kind.Function, params: [], body: chunk.kind === Kind.Chunk ? chunk.body : chunk, isVararg: true },
      this.rootScope(),
      'main chunk',
    );
    return this.call(fn, args);
  }

  rootScope() {
    if (!this.root) {
      this.root = new Scope(null);
      this.root.frame = { varargs: [] };
    }
    return this.root;
  }

  execBlock(block, parentScope) {
    const scope = new Scope(parentScope);
    scope.frame = parentScope.frame;
    return this.execStatements(block.statements, scope);
  }

  execStatements(statements, scope) {
    let index = 0;
    while (index < statements.length) {
      const signal = this.execStatement(statements[index], scope);
      if (signal) {
        if (signal.signal === 'goto') {
          const target = statements.findIndex(
            (s) => s.kind === Kind.Label && s.name === signal.label,
          );
          if (target !== -1) {
            index = target + 1;
            continue;
          }
        }
        return signal;
      }
      index += 1;
    }
    return undefined;
  }

  execStatement(node, scope) {
    this.tick();
    switch (node.kind) {
      case Kind.LocalDeclaration: {
        const values = this.evalExpressionList(node.expressions, scope, node.names.length);
        for (let i = 0; i < node.names.length; i += 1) scope.declare(node.names[i], values[i]);
        return undefined;
      }
      case Kind.LocalFunction: {
        const cell = scope.declare(node.name, undefined);
        cell.value = new LuaFunction(node.body, scope, node.name);
        return undefined;
      }
      case Kind.FunctionDeclaration: {
        const fn = new LuaFunction(node.body, scope, 'declared');
        this.assign(node.target, fn, scope);
        return undefined;
      }
      case Kind.Assignment: {
        const values = this.evalExpressionList(node.expressions, scope, node.targets.length);
        const slots = node.targets.map((target) => this.slotFor(target, scope));
        for (let i = slots.length - 1; i >= 0; i -= 1) this.store(slots[i], values[i]);
        return undefined;
      }
      case Kind.CallStatement:
        this.evalMulti(node.expression, scope);
        return undefined;
      case Kind.Return:
        return { signal: 'return', values: this.evalExpressionList(node.expressions, scope, -1) };
      case Kind.Break:
        return BREAK;
      case Kind.Continue:
        return CONTINUE;
      case Kind.Goto:
        return { signal: 'goto', label: node.label };
      case Kind.Label:
        return undefined;
      case Kind.Do:
        return this.execBlock(node.body, scope);
      case Kind.If:
        return this.execIf(node, scope);
      case Kind.While:
        return this.execWhile(node, scope);
      case Kind.Repeat:
        return this.execRepeat(node, scope);
      case Kind.NumericFor:
        return this.execNumericFor(node, scope);
      case Kind.GenericFor:
        return this.execGenericFor(node, scope);
      default:
        throw new LuaError(`unsupported statement: ${node.kind}`);
    }
  }

  execIf(node, scope) {
    if (truthy(this.eval(node.condition, scope))) return this.execBlock(node.body, scope);
    for (const clause of node.elseIfs || []) {
      if (truthy(this.eval(clause.condition, scope))) return this.execBlock(clause.body, scope);
    }
    if (node.elseBody) return this.execBlock(node.elseBody, scope);
    return undefined;
  }

  static loopSignal(signal) {
    if (!signal) return null;
    if (signal === BREAK) return 'stop';
    if (signal === CONTINUE) return null;
    return signal;
  }

  execWhile(node, scope) {
    for (;;) {
      this.tick();
      if (!truthy(this.eval(node.condition, scope))) return undefined;
      const result = Interpreter.loopSignal(this.execBlock(node.body, scope));
      if (result === 'stop') return undefined;
      if (result) return result;
    }
  }

  execRepeat(node, scope) {
    for (;;) {
      this.tick();

      const bodyScope = new Scope(scope);
      bodyScope.frame = scope.frame;
      const raw = this.execStatements(node.body.statements, bodyScope);
      const result = Interpreter.loopSignal(raw);
      if (result === 'stop') return undefined;
      if (result) return result;
      if (truthy(this.eval(node.condition, bodyScope))) return undefined;
    }
  }

  execNumericFor(node, scope) {
    const start = V.toNumber(this.eval(node.start, scope));
    const limit = V.toNumber(this.eval(node.limit, scope));
    const step = node.step ? V.toNumber(this.eval(node.step, scope)) : 1;
    if (start === undefined || limit === undefined || step === undefined) {
      throw new LuaError("'for' bounds must be numbers");
    }
    for (let i = start; step > 0 ? i <= limit : i >= limit; i += step) {
      this.tick();
      const bodyScope = new Scope(scope);
      bodyScope.frame = scope.frame;
      bodyScope.declare(node.variable, i);
      const result = Interpreter.loopSignal(this.execStatements(node.body.statements, bodyScope));
      if (result === 'stop') return undefined;
      if (result) return result;
    }
    return undefined;
  }

  execGenericFor(node, scope) {
    const values = this.evalExpressionList(node.expressions, scope, 3);
    let [iterator, state, control] = values;
    for (;;) {
      this.tick();
      const results = this.call(iterator, [state, control]);
      if (results[0] === undefined || results[0] === null) return undefined;
      control = results[0];
      const bodyScope = new Scope(scope);
      bodyScope.frame = scope.frame;
      for (let i = 0; i < node.variables.length; i += 1) {
        bodyScope.declare(node.variables[i], results[i]);
      }
      const result = Interpreter.loopSignal(this.execStatements(node.body.statements, bodyScope));
      if (result === 'stop') return undefined;
      if (result) return result;
    }
  }

  slotFor(target, scope) {
    if (target.kind === Kind.Name) {
      const cell = scope.lookup(target.name);
      if (cell) return { cell };
      return { base: this.globals, key: target.name };
    }
    if (target.kind === Kind.Index) {
      return { base: this.eval(target.base, scope), key: this.eval(target.index, scope) };
    }
    throw new LuaError('invalid assignment target');
  }

  store(slot, value) {
    if (slot.cell) {
      effects.touch(slot.cell.stamp, slot.cell);
      slot.cell.value = value;
      return;
    }
    ops.setIndex(this, slot.base, slot.key, value);
  }

  assign(target, value, scope) {
    if (target.kind === Kind.Name) {
      const cell = scope.lookup(target.name);
      if (cell) {
        effects.touch(cell.stamp, cell);
        cell.value = value;
        return;
      }
      ops.setIndex(this, this.globals, target.name, value);
      return;
    }
    if (target.kind === Kind.Index) {
      const base = this.eval(target.base, scope);
      ops.setIndex(this, base, this.eval(target.index, scope), value);
      return;
    }
    throw new LuaError('invalid assignment target');
  }

  evalExpressionList(expressions, scope, want) {
    const values = [];
    if (expressions) {
      for (let i = 0; i < expressions.length; i += 1) {
        if (i === expressions.length - 1) {
          const tail = this.evalMulti(expressions[i], scope);
          for (const value of tail) values.push(value);
        } else {
          values.push(this.eval(expressions[i], scope));
        }
      }
    }
    if (want >= 0) {
      while (values.length < want) values.push(undefined);
      values.length = want;
    }
    return values;
  }

  evalMulti(node, scope) {
    switch (node.kind) {
      case Kind.Call: {
        const fn = this.eval(node.base, scope);
        return this.call(fn, this.evalExpressionList(node.args, scope, -1));
      }
      case Kind.MethodCall: {
        const self = this.eval(node.base, scope);
        const fn = ops.index(this, self, node.method);
        return this.call(fn, [self, ...this.evalExpressionList(node.args, scope, -1)]);
      }
      case Kind.Vararg:
        return (scope.frame ? scope.frame.varargs : []).slice();
      default:
        return [this.eval(node, scope)];
    }
  }

  eval(node, scope) {
    this.tick();
    switch (node.kind) {
      case Kind.Nil: return undefined;
      case Kind.True: return true;
      case Kind.False: return false;
      case Kind.Number: return node.value;
      case Kind.String: return node.value;
      case Kind.Vararg: return this.evalMulti(node, scope)[0];
      case Kind.Name: {
        const cell = scope.lookup(node.name);
        if (cell) return cell.value;
        return ops.index(this, this.globals, node.name);
      }
      case Kind.Paren: return this.eval(node.expression, scope);
      case Kind.Function: return new LuaFunction(node, scope, null);
      case Kind.Index:
        return ops.index(this, this.eval(node.base, scope), this.eval(node.index, scope));
      case Kind.Call:
      case Kind.MethodCall:
        return this.evalMulti(node, scope)[0];
      case Kind.Table: return this.evalTable(node, scope);
      case Kind.Unary: return this.evalUnary(node, scope);
      case Kind.Binary: return this.evalBinary(node, scope);
      default:
        throw new LuaError(`unsupported expression: ${node.kind}`);
    }
  }

  evalTable(node, scope) {
    const table = new LuaTable();
    let arrayIndex = 1;
    const entries = node.entries || [];
    for (let i = 0; i < entries.length; i += 1) {
      const entry = entries[i];
      if (entry.type === 'key') {
        table.set(this.eval(entry.key, scope), this.eval(entry.value, scope));
        continue;
      }
      if (i === entries.length - 1) {
        for (const value of this.evalMulti(entry.value, scope)) {
          table.set(arrayIndex, value);
          arrayIndex += 1;
        }
      } else {
        table.set(arrayIndex, this.eval(entry.value, scope));
        arrayIndex += 1;
      }
    }
    return table;
  }

  evalUnary(node, scope) {
    const value = this.eval(node.argument, scope);
    switch (node.operator) {
      case '-': return ops.unaryMinus(this, value);
      case 'not': return !truthy(value);
      case '#': return ops.length(this, value);
      default: throw new LuaError(`unknown unary operator '${node.operator}'`);
    }
  }

  evalBinary(node, scope) {
    const op = node.operator;
    if (op === 'and') {
      const lhs = this.eval(node.lhs, scope);
      return truthy(lhs) ? this.eval(node.rhs, scope) : lhs;
    }
    if (op === 'or') {
      const lhs = this.eval(node.lhs, scope);
      return truthy(lhs) ? lhs : this.eval(node.rhs, scope);
    }
    const a = this.eval(node.lhs, scope);
    const b = this.eval(node.rhs, scope);
    switch (op) {
      case '..': return ops.concat(this, a, b);
      case '==': return ops.equals(this, a, b);
      case '~=': return !ops.equals(this, a, b);
      case '<': return ops.lessThan(this, a, b);
      case '>': return ops.lessThan(this, b, a);
      case '<=': return ops.lessOrEqual(this, a, b);
      case '>=': return ops.lessOrEqual(this, b, a);
      default: return ops.arith(this, op, a, b);
    }
  }
}

module.exports = { Interpreter, Scope, LuaLimitError };
