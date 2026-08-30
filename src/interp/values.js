'use strict';

const effects = require('./effects');

class LuaError extends Error {
  constructor(value, traceback) {
    super(typeof value === 'string' ? value : '(error object)');
    this.name = 'LuaError';
    this.value = value;
    this.luaTraceback = traceback;
  }
}

class LuaTable {
  constructor() {
    this.map = new Map();
    this.metatable = undefined;

    this.stamp = effects.fresh();
  }

  static from(values) {
    const t = new LuaTable();
    for (let i = 0; i < values.length; i += 1) t.set(i + 1, values[i]);
    return t;
  }

  static fromPairs(pairs) {
    const t = new LuaTable();
    for (const [key, value] of pairs) t.set(key, value);
    return t;
  }

  get(key) {
    if (typeof key === 'number' && Object.is(key, -0)) return this.map.get(0);
    return this.map.get(key);
  }

  set(key, value) {
    const k = typeof key === 'number' && Object.is(key, -0) ? 0 : key;
    effects.touch(this.stamp, this, k);
    if (value === undefined) this.map.delete(k);
    else this.map.set(k, value);
  }

  setMetatable(metatable) {
    effects.touch(this.stamp, this, effects.META);
    this.metatable = metatable;
  }

  length() {
    let n = 0;
    while (this.map.get(n + 1) !== undefined) n += 1;
    return n;
  }

  toArray() {
    const out = [];
    const n = this.length();
    for (let i = 1; i <= n; i += 1) out.push(this.map.get(i));
    return out;
  }

  keys() {
    return [...this.map.keys()];
  }
}

class LuaFunction {
  constructor(node, closure, name) {
    this.node = node;
    this.closure = closure;
    this.name = name || null;
  }
}

const isCallable = (v) => typeof v === 'function' || v instanceof LuaFunction;

function luaType(value) {
  if (value === undefined || value === null) return 'nil';
  switch (typeof value) {
    case 'boolean': return 'boolean';
    case 'number': return 'number';
    case 'string': return 'string';
    case 'function': return 'function';
    default: break;
  }
  if (value instanceof LuaTable) return 'table';
  if (value instanceof LuaFunction) return 'function';
  return 'userdata';
}

const truthy = (value) => value !== undefined && value !== null && value !== false;

function formatFloat(value, precision = 14) {
  if (Number.isNaN(value)) return 'nan';
  if (value === Infinity) return 'inf';
  if (value === -Infinity) return '-inf';
  if (value === 0) return Object.is(value, -0) ? '-0' : '0';
  const exponent = Math.floor(Math.log10(Math.abs(value)));
  if (exponent < -4 || exponent >= precision) {
    let mantissa = (value / 10 ** exponent).toPrecision(precision);
    if (mantissa.includes('.')) mantissa = mantissa.replace(/0+$/, '').replace(/\.$/, '');
    const sign = exponent < 0 ? '-' : '+';
    const digits = String(Math.abs(exponent)).padStart(2, '0');
    return `${mantissa}e${sign}${digits}`;
  }
  let text = value.toFixed(Math.max(0, precision - 1 - exponent));
  if (text.includes('.')) text = text.replace(/0+$/, '').replace(/\.$/, '');
  return text;
}

function numberToString(value) {
  if (Number.isInteger(value) && Math.abs(value) < 1e15) return String(value);
  return formatFloat(value);
}

function stringToNumber(text) {
  const trimmed = text.replace(/^[\s\f]+|[\s\f]+$/g, '');
  if (trimmed === '') return undefined;
  if (/^[-+]?0[xX][0-9a-fA-F]+$/.test(trimmed)) {
    const negative = trimmed[0] === '-';
    const body = trimmed.replace(/^[-+]/, '');
    const value = parseInt(body.slice(2), 16);
    return negative ? -value : value;
  }
  if (!/^[-+]?(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?$/.test(trimmed)) return undefined;
  const value = Number(trimmed);
  return Number.isNaN(value) ? undefined : value;
}

function toNumber(value) {
  if (typeof value === 'number') return value;
  if (typeof value === 'string') return stringToNumber(value);
  return undefined;
}

module.exports = {
  LuaError,
  LuaTable,
  LuaFunction,
  isCallable,
  luaType,
  truthy,
  formatFloat,
  numberToString,
  toNumber,
};
