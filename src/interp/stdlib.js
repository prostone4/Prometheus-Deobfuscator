'use strict';

const V = require('./values');
const ops = require('./ops');
const strlib = require('./strlib');

const { LuaError, LuaTable, LuaFunction, luaType, truthy } = V;

function installBase(rt) {
  const g = rt.globals;
  g.set('_VERSION', 'Lua 5.1');
  g.set('_G', g);

  g.set('print', (i, args) => {
    const parts = args.map((value) => ops.tostring(i, value));
    i.output.push(parts.join('\t'));
    return [];
  });
  g.set('type', (i, args) => [luaType(args[0])]);
  g.set('tostring', (i, args) => [ops.tostring(i, args[0])]);
  g.set('tonumber', (i, args) => {
    if (args[1] === undefined || args[1] === null) return [V.toNumber(args[0])];
    const base = Math.floor(V.toNumber(args[1]));
    const text = typeof args[0] === 'string' ? args[0].trim() : undefined;
    if (text === undefined) return [undefined];
    const value = parseInt(text, base);
    return [Number.isNaN(value) ? undefined : value];
  });
  g.set('rawget', (i, args) => [args[0] instanceof LuaTable ? args[0].get(args[1]) : undefined]);
  g.set('rawset', (i, args) => {
    if (args[0] instanceof LuaTable) args[0].set(args[1], args[2]);
    return [args[0]];
  });
  g.set('rawequal', (i, args) => [ops.rawEquals(args[0], args[1])]);
  g.set('rawlen', (i, args) => [ops.length(i, args[0])]);
  g.set('setmetatable', (i, args) => {
    if (!(args[0] instanceof LuaTable)) {
      throw new LuaError("setmetatable: expected table");
    }
    args[0].setMetatable(args[1] === undefined || args[1] === null ? undefined : args[1]);
    return [args[0]];
  });
  g.set('getmetatable', (i, args) => {
    const value = args[0];
    const metatable = value instanceof LuaTable ? value.metatable
      : (typeof value === 'string' ? i.stringMeta : (value && value.__metatable));
    if (!metatable) return [undefined];
    const guard = metatable.get('__metatable');
    return [guard === undefined ? metatable : guard];
  });
  g.set('assert', (i, args) => {
    if (!truthy(args[0])) {
      throw new LuaError(args[1] === undefined ? 'assertion failed!' : args[1]);
    }
    return args;
  });
  g.set('error', (i, args) => {
    const value = args[0];
    const level = args[1] === undefined ? 1 : V.toNumber(args[1]);
    if (typeof value === 'string' && level !== 0) {
      throw new LuaError(`deobf:0: ${value}`);
    }
    throw new LuaError(value);
  });
  g.set('select', (i, args) => {
    const selector = args[0];
    const rest = args.slice(1);
    if (selector === '#') return [rest.length];
    const n = Math.floor(V.toNumber(selector));
    if (n < 0) return rest.slice(rest.length + n);
    return rest.slice(n - 1);
  });
  g.set('unpack', (i, args) => {
    const table = args[0];
    if (!(table instanceof LuaTable)) return [];
    const from = args[1] === undefined ? 1 : Math.floor(V.toNumber(args[1]));
    const to = args[2] === undefined ? table.length() : Math.floor(V.toNumber(args[2]));
    const out = [];
    for (let k = from; k <= to; k += 1) out.push(table.get(k));
    return out;
  });
  g.set('next', (i, args) => nextImpl(args[0], args[1]));
  g.set('pairs', (i, args) => {
    const table = args[0];
    const handler = i.metamethod(table, '__pairs');
    if (handler) return i.call(handler, [table]);
    return [g.get('next'), table, undefined];
  });
  g.set('ipairs', (i, args) => {
    const table = args[0];
    const iterator = (inner, iargs) => {
      const index = Math.floor(V.toNumber(iargs[1])) + 1;
      const value = ops.index(inner, iargs[0], index);
      if (value === undefined || value === null) return [undefined];
      return [index, value];
    };
    return [iterator, table, 0];
  });
  g.set('pcall', (i, args) => {
    const fn = args[0];
    try {
      return [true, ...i.call(fn, args.slice(1))];
    } catch (error) {
      if (error && error.sandbox) throw error;
      if (error && error.name === 'LuaLimitError') throw error;
      i.swallows = (i.swallows || 0) + 1;
      if (error instanceof LuaError) return [false, error.value];
      return [false, String(error && error.message ? error.message : error)];
    }
  });
  g.set('xpcall', (i, args) => {
    const [fn, handler] = args;
    try {
      return [true, ...i.call(fn, args.slice(2))];
    } catch (error) {
      if (error && error.sandbox) throw error;
      if (!(error instanceof LuaError) && error && error.name === 'LuaLimitError') throw error;
      i.swallows = (i.swallows || 0) + 1;
      const value = error instanceof LuaError ? error.value : String(error.message || error);
      return [false, ...i.call(handler, [value])];
    }
  });
  g.set('getfenv', (i) => [i.globals]);
  g.set('setfenv', (i, args) => [args[0]]);
  g.set('collectgarbage', () => [0]);
  g.set('require', () => []);
  g.set('newproxy', (i, args) => {
    const proxy = { userdata: true, __metatable: undefined };
    if (truthy(args[0])) proxy.__metatable = new LuaTable();
    return [proxy];
  });
}

function nextImpl(table, key) {
  if (!(table instanceof LuaTable)) throw new LuaError("next: expected table");
  const keys = table.keys();
  if (key === undefined || key === null) {
    if (keys.length === 0) return [undefined];
    return [keys[0], table.get(keys[0])];
  }
  const at = keys.indexOf(typeof key === 'number' && Object.is(key, -0) ? 0 : key);
  if (at === -1 || at === keys.length - 1) return [undefined];
  const nextKey = keys[at + 1];
  return [nextKey, table.get(nextKey)];
}

function installTable(rt) {
  const table = new LuaTable();
  table.set('insert', (i, args) => {
    const t = args[0];
    if (!(t instanceof LuaTable)) throw new LuaError("table.insert: expected table");
    if (args.length <= 2) {
      t.set(t.length() + 1, args[1]);
      return [];
    }
    const position = Math.floor(V.toNumber(args[1]));
    const size = t.length();
    for (let k = size; k >= position; k -= 1) t.set(k + 1, t.get(k));
    t.set(position, args[2]);
    return [];
  });
  table.set('remove', (i, args) => {
    const t = args[0];
    if (!(t instanceof LuaTable)) throw new LuaError("table.remove: expected table");
    const size = t.length();
    const position = args[1] === undefined ? size : Math.floor(V.toNumber(args[1]));
    if (size === 0) return [undefined];
    const removed = t.get(position);
    for (let k = position; k < size; k += 1) t.set(k, t.get(k + 1));
    t.set(size, undefined);
    return [removed];
  });
  table.set('concat', (i, args) => {
    const t = args[0];
    const separator = args[1] === undefined ? '' : ops.stringify(args[1]);
    const from = args[2] === undefined ? 1 : Math.floor(V.toNumber(args[2]));
    const to = args[3] === undefined ? t.length() : Math.floor(V.toNumber(args[3]));
    const parts = [];
    for (let k = from; k <= to; k += 1) {
      const value = t.get(k);
      if (typeof value !== 'string' && typeof value !== 'number') {
        throw new LuaError(`table.concat: invalid value at index ${k}`);
      }
      parts.push(ops.stringify(value));
    }
    return [parts.join(separator)];
  });
  table.set('unpack', rt.globals.get('unpack'));
  table.set('pack', (i, args) => {
    const t = LuaTable.from(args);
    t.set('n', args.length);
    return [t];
  });
  table.set('sort', (i, args) => {
    const t = args[0];
    const comparator = args[1];
    const values = t.toArray();
    const compare = comparator
      ? (a, b) => (truthy(i.call(comparator, [a, b])[0]) ? -1 : (truthy(i.call(comparator, [b, a])[0]) ? 1 : 0))
      : (a, b) => (ops.lessThan(i, a, b) ? -1 : (ops.lessThan(i, b, a) ? 1 : 0));
    values.sort(compare);
    for (let k = 0; k < values.length; k += 1) t.set(k + 1, values[k]);
    return [];
  });
  table.set('getn', (i, args) => [args[0].length()]);
  rt.globals.set('table', table);
}

function installMath(rt) {
  const math = new LuaTable();
  const unary = (fn) => (i, args) => [fn(strlib.checkNumber(args, 0, 'math'))];
  math.set('floor', unary(Math.floor));
  math.set('ceil', unary(Math.ceil));
  math.set('abs', unary(Math.abs));
  math.set('sqrt', unary(Math.sqrt));
  math.set('sin', unary(Math.sin));
  math.set('cos', unary(Math.cos));
  math.set('tan', unary(Math.tan));
  math.set('asin', unary(Math.asin));
  math.set('acos', unary(Math.acos));
  math.set('atan', unary(Math.atan));
  math.set('exp', unary(Math.exp));
  math.set('log', (i, args) => {
    const x = strlib.checkNumber(args, 0, 'log');
    if (args[1] === undefined) return [Math.log(x)];
    return [Math.log(x) / Math.log(strlib.checkNumber(args, 1, 'log'))];
  });
  math.set('log10', unary(Math.log10));
  math.set('pow', (i, args) => [strlib.checkNumber(args, 0, 'pow') ** strlib.checkNumber(args, 1, 'pow')]);
  math.set('fmod', (i, args) => {
    const a = strlib.checkNumber(args, 0, 'fmod');
    const b = strlib.checkNumber(args, 1, 'fmod');
    return [a % b];
  });
  math.set('modf', (i, args) => {
    const x = strlib.checkNumber(args, 0, 'modf');
    const integral = x >= 0 ? Math.floor(x) : Math.ceil(x);
    return [integral, x - integral];
  });
  math.set('max', (i, args) => [Math.max(...args.map((v) => V.toNumber(v)))]);
  math.set('min', (i, args) => [Math.min(...args.map((v) => V.toNumber(v)))]);
  math.set('huge', Infinity);
  math.set('pi', Math.PI);
  math.set('random', (i, args) => {
    const value = i.random();
    if (args.length === 0) return [value];
    const lower = args.length === 1 ? 1 : Math.floor(V.toNumber(args[0]));
    const upper = args.length === 1 ? Math.floor(V.toNumber(args[0])) : Math.floor(V.toNumber(args[1]));
    return [lower + Math.floor(value * (upper - lower + 1))];
  });
  math.set('randomseed', (i, args) => {
    i.seedRandom(V.toNumber(args[0]) || 0);
    return [];
  });
  rt.globals.set('math', math);
}

function installMisc(rt) {
  const os = new LuaTable();
  os.set('time', () => [1600000000]);
  os.set('clock', (i) => [i.steps / 1e6]);
  os.set('date', (i, args) => [typeof args[0] === 'string' ? args[0] : 'Mon Jan  1 00:00:00 2020']);
  os.set('getenv', () => [undefined]);
  os.set('exit', () => {
    throw new LuaError('os.exit called');
  });
  rt.globals.set('os', os);

  const debug = new LuaTable();
  debug.set('getinfo', (i, args) => {
    const info = new LuaTable();
    info.set('currentline', 1);
    info.set('source', '@deobf');
    info.set('short_src', 'deobf');
    info.set('what', 'Lua');
    info.set('func', args[0]);
    info.set('linedefined', 1);
    return [info];
  });
  debug.set('sethook', () => []);
  debug.set('gethook', () => [undefined]);
  debug.set('traceback', (i, args) => [typeof args[0] === 'string' ? args[0] : 'stack traceback:']);
  debug.set('getlocal', () => [undefined]);
  debug.set('getupvalue', () => [undefined]);
  debug.set('setupvalue', () => [undefined]);
  debug.set('getmetatable', (i, args) => [args[0] instanceof LuaTable ? args[0].metatable : undefined]);
  debug.set('setmetatable', (i, args) => {
    if (args[0] instanceof LuaTable) args[0].setMetatable(args[1]);
    return [args[0]];
  });
  rt.globals.set('debug', debug);

  const io = new LuaTable();
  io.set('write', (i, args) => {
    i.output.push(args.map((v) => ops.stringify(v)).join(''));
    return [];
  });
  io.set('read', () => [undefined]);
  rt.globals.set('io', io);

  const coroutine = new LuaTable();
  coroutine.set('create', (i, args) => [args[0]]);
  coroutine.set('wrap', (i, args) => [args[0]]);
  coroutine.set('resume', (i, args) => [true, ...i.call(args[0], args.slice(1))]);
  coroutine.set('yield', () => []);
  coroutine.set('status', () => ['dead']);
  rt.globals.set('coroutine', coroutine);

  const bit = new LuaTable();
  const toInt = (v) => Math.trunc(V.toNumber(v)) | 0;
  bit.set('band', (i, args) => [args.map(toInt).reduce((a, b) => a & b)]);
  bit.set('bor', (i, args) => [args.map(toInt).reduce((a, b) => a | b)]);
  bit.set('bxor', (i, args) => [args.map(toInt).reduce((a, b) => a ^ b)]);
  bit.set('bnot', (i, args) => [~toInt(args[0])]);
  bit.set('lshift', (i, args) => [toInt(args[0]) << toInt(args[1])]);
  bit.set('rshift', (i, args) => [toInt(args[0]) >>> toInt(args[1])]);
  bit.set('arshift', (i, args) => [toInt(args[0]) >> toInt(args[1])]);
  bit.set('tobit', (i, args) => [toInt(args[0])]);
  rt.globals.set('bit', bit);
  rt.globals.set('bit32', bit);
}

function installRandom(rt) {
  let state = 0x2545f491;
  rt.seedRandom = (seed) => {
    state = (Math.floor(seed) >>> 0) || 1;
  };
  rt.random = () => {
    state ^= state << 13;
    state >>>= 0;
    state ^= state >>> 17;
    state ^= state << 5;
    state >>>= 0;
    return state / 0x100000000;
  };
}

function install(rt) {
  installRandom(rt);
  installBase(rt);
  strlib.install(rt);
  installTable(rt);
  installMath(rt);
  installMisc(rt);
}

module.exports = { install };
