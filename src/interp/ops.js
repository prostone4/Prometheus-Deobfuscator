'use strict';

const V = require('./values');

const { LuaError, LuaTable, luaType, truthy, toNumber } = V;

const EVENTS = {
  '+': '__add', '-': '__sub', '*': '__mul', '/': '__div',
  '%': '__mod', '^': '__pow', '..': '__concat',
};

function typeError(operation, value) {
  throw new LuaError(`cannot perform ${operation} on ${luaType(value)}`);
}

function arithMeta(rt, op, a, b) {
  const event = EVENTS[op];
  const handler = rt.metamethod(a, event) || rt.metamethod(b, event);
  if (handler) return rt.call(handler, [a, b])[0];
  const culprit = toNumber(a) === undefined ? a : b;
  return typeError(`arithmetic (${op})`, culprit);
}

function arith(rt, op, a, b) {
  const x = toNumber(a);
  const y = toNumber(b);
  if (x === undefined || y === undefined) return arithMeta(rt, op, a, b);
  switch (op) {
    case '+': return x + y;
    case '-': return x - y;
    case '*': return x * y;
    case '/': return x / y;
    case '%': return x - Math.floor(x / y) * y;
    case '^': return x ** y;
    case '//': return Math.floor(x / y);
    default: throw new LuaError(`unknown operator '${op}'`);
  }
}

function unaryMinus(rt, a) {
  const x = toNumber(a);
  if (x !== undefined) return -x;
  const handler = rt.metamethod(a, '__unm');
  if (handler) return rt.call(handler, [a, a])[0];
  return typeError('arithmetic (-)', a);
}

function length(rt, a) {
  if (typeof a === 'string') return a.length;
  const handler = rt.metamethod(a, '__len');
  if (handler) return rt.call(handler, [a])[0];
  if (a instanceof LuaTable) return a.length();
  return typeError('get length of', a);
}

function concat(rt, a, b) {
  const okA = typeof a === 'string' || typeof a === 'number';
  const okB = typeof b === 'string' || typeof b === 'number';
  if (okA && okB) return stringify(a) + stringify(b);
  const handler = rt.metamethod(a, '__concat') || rt.metamethod(b, '__concat');
  if (handler) return rt.call(handler, [a, b])[0];
  return typeError('concatenation', okA ? b : a);
}

function stringify(value) {
  return typeof value === 'number' ? V.numberToString(value) : value;
}

function rawEquals(a, b) {
  if (a === undefined || a === null) return b === undefined || b === null;
  return a === b;
}

function equals(rt, a, b) {
  if (rawEquals(a, b)) return true;
  if (luaType(a) !== luaType(b)) return false;
  if (!(a instanceof LuaTable) && luaType(a) !== 'userdata') return false;
  const handler = rt.metamethod(a, '__eq') || rt.metamethod(b, '__eq');
  if (!handler) return false;
  return truthy(rt.call(handler, [a, b])[0]);
}

function lessThan(rt, a, b) {
  if (typeof a === 'number' && typeof b === 'number') return a < b;
  if (typeof a === 'string' && typeof b === 'string') return a < b;
  const handler = rt.metamethod(a, '__lt') || rt.metamethod(b, '__lt');
  if (handler) return truthy(rt.call(handler, [a, b])[0]);
  throw new LuaError(`cannot compare ${luaType(a)} with ${luaType(b)}`);
}

function lessOrEqual(rt, a, b) {
  if (typeof a === 'number' && typeof b === 'number') return a <= b;
  if (typeof a === 'string' && typeof b === 'string') return a <= b;
  const handler = rt.metamethod(a, '__le') || rt.metamethod(b, '__le');
  if (handler) return truthy(rt.call(handler, [a, b])[0]);
  const flipped = rt.metamethod(a, '__lt') || rt.metamethod(b, '__lt');
  if (flipped) return !truthy(rt.call(flipped, [b, a])[0]);
  throw new LuaError(`cannot compare ${luaType(a)} with ${luaType(b)}`);
}

function index(rt, base, key) {
  if (base instanceof LuaTable) {
    const value = base.get(key);
    if (value !== undefined && value !== null) return value;
    const handler = rt.metamethod(base, '__index');
    if (!handler) return undefined;
    if (V.isCallable(handler)) return rt.call(handler, [base, key])[0];
    return index(rt, handler, key);
  }
  const handler = rt.metamethod(base, '__index');
  if (!handler) return typeError(`index (key '${stringify(key)}')`, base);
  if (V.isCallable(handler)) return rt.call(handler, [base, key])[0];
  return index(rt, handler, key);
}

function setIndex(rt, base, key, value) {
  if (base instanceof LuaTable) {
    if (base.get(key) === undefined) {
      const handler = rt.metamethod(base, '__newindex');
      if (handler) {
        if (V.isCallable(handler)) {
          rt.call(handler, [base, key, value]);
          return;
        }
        setIndex(rt, handler, key, value);
        return;
      }
    }
    if (key === undefined || key === null) throw new LuaError('table index is nil');
    if (typeof key === 'number' && Number.isNaN(key)) throw new LuaError('table index is NaN');
    base.set(key, value);
    return;
  }
  const handler = rt.metamethod(base, '__newindex');
  if (!handler) {
    typeError(`index (key '${stringify(key)}')`, base);
    return;
  }
  if (V.isCallable(handler)) rt.call(handler, [base, key, value]);
  else setIndex(rt, handler, key, value);
}

function tostring(rt, value) {
  const handler = rt.metamethod(value, '__tostring');
  if (handler) return rt.call(handler, [value])[0];
  const type = luaType(value);
  switch (type) {
    case 'nil': return 'nil';
    case 'boolean': return value ? 'true' : 'false';
    case 'number': return V.numberToString(value);
    case 'string': return value;
    default: return `${type}: 0x${rt.addressOf(value)}`;
  }
}

module.exports = {
  arith,
  unaryMinus,
  length,
  concat,
  equals,
  rawEquals,
  lessThan,
  lessOrEqual,
  index,
  setIndex,
  tostring,
  stringify,
};
