'use strict';

const V = require('./values');
const ops = require('./ops');
const patterns = require('./patterns');

const { LuaError, LuaTable, luaType } = V;

const argError = (n, fname, expected, got) => {
  throw new LuaError(`${fname}: arg #${n} expected ${expected}, got ${luaType(got)}`);
};

function checkString(args, i, fname) {
  const value = args[i];
  if (typeof value === 'string') return value;
  if (typeof value === 'number') return V.numberToString(value);
  return argError(i + 1, fname, 'string', value);
}

function checkNumber(args, i, fname) {
  const value = V.toNumber(args[i]);
  if (value === undefined) return argError(i + 1, fname, 'number', args[i]);
  return value;
}

function optNumber(args, i, fallback) {
  if (args[i] === undefined || args[i] === null) return fallback;
  const value = V.toNumber(args[i]);
  return value === undefined ? fallback : value;
}

function relative(position, length) {
  if (position >= 0) return position;
  if (-position > length) return 0;
  return length + position + 1;
}

function formatValue(rt, spec, value) {
  const conversion = spec[spec.length - 1];
  const flags = spec.slice(1, -1);
  const widthMatch = /^([-+ #0]*)(\d*)(?:\.(\d+))?$/.exec(flags) || ['', '', '', undefined];
  const [, modifiers, widthText, precisionText] = widthMatch;
  const width = widthText ? Number(widthText) : 0;
  const precision = precisionText === undefined ? undefined : Number(precisionText);
  let text;
  switch (conversion) {
    case 'd': case 'i': {
      const n = Math.trunc(checkNumber([value], 0, 'format'));
      text = String(Math.abs(n));
      if (precision !== undefined) text = text.padStart(precision, '0');
      if (n < 0) text = `-${text}`;
      else if (modifiers.includes('+')) text = `+${text}`;
      break;
    }
    case 'u': text = String(Math.trunc(Math.abs(checkNumber([value], 0, 'format')))); break;
    case 'c': text = String.fromCharCode(checkNumber([value], 0, 'format')); break;
    case 'x': case 'X': {
      const n = Math.trunc(checkNumber([value], 0, 'format'));
      text = (n < 0 ? n >>> 0 : n).toString(16);
      if (precision !== undefined) text = text.padStart(precision, '0');
      if (conversion === 'X') text = text.toUpperCase();
      if (modifiers.includes('#')) text = `0${conversion}${text}`;
      break;
    }
    case 'o': text = Math.trunc(checkNumber([value], 0, 'format')).toString(8); break;
    case 'f': case 'F':
      text = checkNumber([value], 0, 'format').toFixed(precision === undefined ? 6 : precision);
      break;
    case 'e': case 'E': {
      text = checkNumber([value], 0, 'format').toExponential(precision === undefined ? 6 : precision);
      text = text.replace(/e([-+])(\d)$/, 'e$10$2');
      if (conversion === 'E') text = text.toUpperCase();
      break;
    }
    case 'g': case 'G': {
      text = V.formatFloat(checkNumber([value], 0, 'format'), precision === undefined ? 6 : precision);
      if (conversion === 'G') text = text.toUpperCase();
      break;
    }
    case 's': {
      text = ops.tostring(rt, value);
      if (precision !== undefined) text = text.slice(0, precision);
      break;
    }
    case 'q': {
      const raw = typeof value === 'string' ? value : ops.tostring(rt, value);
      let quoted = '"';
      for (let i = 0; i < raw.length; i += 1) {
        const c = raw[i];
        const code = raw.charCodeAt(i);
        if (c === '"' || c === '\\' || c === '\n') quoted += `\\${c === '\n' ? 'n' : c}`;
        else if (code === 0) quoted += '\\0';
        else if (code < 32 || code === 127) quoted += `\\${code}`;
        else quoted += c;
      }
      text = `${quoted}"`;
      break;
    }
    default:
      throw new LuaError(`format: invalid option '%${conversion}'`);
  }
  if (width > text.length) {
    text = modifiers.includes('-')
      ? text.padEnd(width, ' ')
      : text.padStart(width, modifiers.includes('0') && 'dioxXufFeEgG'.includes(conversion) ? '0' : ' ');
  }
  return text;
}

function format(rt, args) {
  const spec = checkString(args, 0, 'format');
  let out = '';
  let argIndex = 1;
  let i = 0;
  while (i < spec.length) {
    const c = spec[i];
    if (c !== '%') {
      out += c;
      i += 1;
      continue;
    }
    if (spec[i + 1] === '%') {
      out += '%';
      i += 2;
      continue;
    }
    let j = i + 1;
    while (j < spec.length && '-+ #0'.includes(spec[j])) j += 1;
    while (j < spec.length && spec[j] >= '0' && spec[j] <= '9') j += 1;
    if (spec[j] === '.') {
      j += 1;
      while (j < spec.length && spec[j] >= '0' && spec[j] <= '9') j += 1;
    }
    const directive = spec.slice(i, j + 1);
    out += formatValue(rt, directive, args[argIndex]);
    argIndex += 1;
    i = j + 1;
  }
  return [out];
}

function expandReplacement(template, whole, captures) {
  let out = '';
  for (let i = 0; i < template.length; i += 1) {
    const c = template[i];
    if (c !== '%') {
      out += c;
      continue;
    }
    const next = template[i + 1];
    i += 1;
    if (next === '%') {
      out += '%';
      continue;
    }
    if (next >= '0' && next <= '9') {
      if (next === '0') out += whole;
      else {
        const value = captures[Number(next) - 1];
        out += typeof value === 'number' ? V.numberToString(value) : value;
      }
      continue;
    }
    throw new LuaError('gsub: invalid \'%\' in replacement');
  }
  return out;
}

function gsub(rt, args) {
  const source = checkString(args, 0, 'gsub');
  const pattern = checkString(args, 1, 'gsub');
  const replacement = args[2];
  const maxCount = optNumber(args, 3, Infinity);
  let out = '';
  let position = 0;
  let count = 0;
  const anchored = pattern[0] === '^';
  while (count < maxCount) {
    const matcher = new patterns.Matcher(source, pattern);
    const end = matcher.match(position, anchored ? 1 : 0);
    if (end !== -1) {
      count += 1;
      const whole = source.slice(position, end);
      const captures = matcher.captures(position, end);
      let value;
      if (typeof replacement === 'string' || typeof replacement === 'number') {
        value = expandReplacement(String(replacement), whole, captures);
      } else if (replacement instanceof LuaTable) {
        value = replacement.get(captures[0]);
      } else if (V.isCallable(replacement)) {
        value = rt.call(replacement, captures)[0];
      } else {
        throw new LuaError('gsub: invalid replacement type');
      }
      if (value === undefined || value === null || value === false) out += whole;
      else if (typeof value === 'number') out += V.numberToString(value);
      else if (typeof value === 'string') out += value;
      else throw new LuaError('gsub: invalid replacement value');
      if (end > position) {
        position = end;
      } else {
        if (position < source.length) out += source[position];
        position += 1;
      }
    } else {
      if (position < source.length) out += source[position];
      position += 1;
    }
    if (position > source.length || anchored) break;
  }
  out += source.slice(Math.min(position, source.length));
  return [out, count];
}

function find(rt, args, wantCaptures) {
  const source = checkString(args, 0, 'find');
  const pattern = checkString(args, 1, 'find');
  const init = relative(optNumber(args, 2, 1), source.length);
  const plain = V.truthy(args[3]);
  const start = Math.max(0, init - 1);
  if (start > source.length) return [undefined];
  if (!wantCaptures && plain) {
    const at = source.indexOf(pattern, start);
    return at === -1 ? [undefined] : [at + 1, at + pattern.length];
  }
  const result = patterns.find(source, pattern, start);
  if (!result) return [undefined];
  if (wantCaptures) return result.captures;
  return [result.start + 1, result.end, ...result.matcher.captures(result.start, result.end, false)];
}

function gmatch(rt, args) {
  const source = checkString(args, 0, 'gmatch');
  const pattern = checkString(args, 1, 'gmatch');
  let position = 0;
  const iterator = () => {
    while (position <= source.length) {
      const matcher = new patterns.Matcher(source, pattern);
      const end = matcher.match(position, 0);
      if (end !== -1) {
        const captures = matcher.captures(position, end);
        position = end > position ? end : position + 1;
        return captures;
      }
      position += 1;
    }
    return [undefined];
  };
  return [iterator];
}

function install(rt) {
  const string = new LuaTable();
  const set = (name, fn) => string.set(name, fn);

  set('len', (i, args) => [checkString(args, 0, 'len').length]);
  set('sub', (i, args) => {
    const s = checkString(args, 0, 'sub');
    let start = relative(optNumber(args, 1, 1), s.length);
    let end = relative(optNumber(args, 2, -1), s.length);
    if (start < 1) start = 1;
    if (end > s.length) end = s.length;
    return [start > end ? '' : s.slice(start - 1, end)];
  });
  set('upper', (i, args) => [checkString(args, 0, 'upper').toUpperCase()]);
  set('lower', (i, args) => [checkString(args, 0, 'lower').toLowerCase()]);
  set('reverse', (i, args) => [[...checkString(args, 0, 'reverse')].reverse().join('')]);
  set('rep', (i, args) => {
    const s = checkString(args, 0, 'rep');
    const n = Math.floor(checkNumber(args, 1, 'rep'));
    const separator = args[2] === undefined ? '' : checkString(args, 2, 'rep');
    if (n <= 0) return [''];
    const parts = new Array(n).fill(s);
    return [parts.join(separator)];
  });
  set('byte', (i, args) => {
    const s = checkString(args, 0, 'byte');
    let start = relative(optNumber(args, 1, 1), s.length);
    let end = relative(optNumber(args, 2, start), s.length);
    if (start < 1) start = 1;
    if (end > s.length) end = s.length;
    const out = [];
    for (let k = start; k <= end; k += 1) out.push(s.charCodeAt(k - 1));
    return out;
  });
  set('char', (i, args) => {
    let out = '';
    for (let k = 0; k < args.length; k += 1) {
      out += String.fromCharCode(Math.floor(checkNumber(args, k, 'char')) & 0xff);
    }
    return [out];
  });
  set('format', format);
  set('gsub', gsub);
  set('find', (i, args) => find(i, args, false));
  set('match', (i, args) => find(i, args, true));
  set('gmatch', gmatch);

  rt.globals.set('string', string);

  const meta = new LuaTable();
  meta.set('__index', string);
  rt.stringMeta = meta;
  return string;
}

module.exports = { install, checkNumber };
