'use strict';

const { Kind } = require('./ast');
const { KEYWORDS } = require('./tokens');

const BINARY = {
  or: [1, 'left'],
  and: [2, 'left'],
  '<': [3, 'left'], '>': [3, 'left'], '<=': [3, 'left'],
  '>=': [3, 'left'], '~=': [3, 'left'], '==': [3, 'left'],
  '|': [4, 'left'], '~': [5, 'left'], '&': [6, 'left'],
  '<<': [7, 'left'], '>>': [7, 'left'],
  '..': [8, 'right'],
  '+': [9, 'left'], '-': [9, 'left'],
  '*': [10, 'left'], '/': [10, 'left'], '//': [10, 'left'], '%': [10, 'left'],
  '^': [12, 'right'],
};

const UNARY_PREC = 11;
const ATOM_PREC = 100;

const PREFIXES = new Set([Kind.Name, Kind.Index, Kind.Call, Kind.MethodCall, Kind.Paren]);

const ID_START = /[A-Za-z_]/;
const ID_BODY = /[A-Za-z0-9_]/;

function isIdentifier(text) {
  if (typeof text !== 'string' || text.length === 0) return false;
  if (!ID_START.test(text[0])) return false;
  for (let i = 1; i < text.length; i += 1) {
    if (!ID_BODY.test(text[i])) return false;
  }
  return !KEYWORDS.has(text);
}

function formatNumber(value) {
  if (typeof value !== 'number') return String(value);
  if (Number.isNaN(value)) return '(0 / 0)';
  if (value === Infinity) return 'math.huge';
  if (value === -Infinity) return '-math.huge';
  if (Object.is(value, -0)) return '0';
  if (Number.isInteger(value) && Math.abs(value) < 1e15) return String(value);
  return String(value);
}

const ESCAPES = { '\n': '\\n', '\r': '\\r', '\t': '\\t', '\\': '\\\\', '"': '\\"' };

const UNPRINTABLE = new Set([0x00a0, 0x00ad, 0x2028, 0x2029, 0xfeff]);

function utf8Length(value, at) {
  const lead = value.charCodeAt(at);
  const second = value.charCodeAt(at + 1);
  const continues = (count) => {
    for (let i = 1; i <= count; i += 1) {
      const code = value.charCodeAt(at + i);
      if (!(code >= 0x80 && code <= 0xbf)) return false;
    }
    return true;
  };
  let length = 0;
  let point = 0;
  if (lead >= 0xc2 && lead <= 0xdf && continues(1)) {
    length = 2;
    point = ((lead & 0x1f) << 6) | (second & 0x3f);
  } else if (lead >= 0xe0 && lead <= 0xef && continues(2)) {
    length = 3;
    point = ((lead & 0x0f) << 12) | ((second & 0x3f) << 6)
      | (value.charCodeAt(at + 2) & 0x3f);
    if (point < 0x800 || (point >= 0xd800 && point <= 0xdfff)) return 0;
  } else if (lead >= 0xf0 && lead <= 0xf4 && continues(3)) {
    length = 4;
    point = ((lead & 0x07) << 18) | ((second & 0x3f) << 12)
      | ((value.charCodeAt(at + 2) & 0x3f) << 6) | (value.charCodeAt(at + 3) & 0x3f);
    if (point < 0x10000 || point > 0x10ffff) return 0;
  } else return 0;
  if (point <= 0x9f || UNPRINTABLE_POINTS.has(point)) return 0;
  return length;
}

function quoteString(value) {
  let out = '"';
  for (let i = 0; i < value.length; i += 1) {
    const c = value[i];
    const short = ESCAPES[c];
    if (short !== undefined) {
      out += short;
      continue;
    }
    const code = value.charCodeAt(i);
    if (code >= 0x20 && code <= 0x7e) {
      out += c;
      continue;
    }
    if (code >= 0xc2 && code <= 0xf4) {
      const spelled = utf8Length(value, i);
      if (spelled) {
        out += value.slice(i, i + spelled);
        i += spelled - 1;
        continue;
      }
    }
    const next = value[i + 1];
    const needsPadding = next !== undefined && next >= '0' && next <= '9';
    out += `\\${needsPadding ? String(code).padStart(3, '0') : String(code)}`;
  }
  return `${out}"`;
}

function canUseLongBracket(value) {
  if (!value.includes('\n')) return false;
  if (value.includes(']]') || value.startsWith('\n') || value.endsWith(']')) return false;
  for (let i = 0; i < value.length; i += 1) {
    const code = value.charCodeAt(i);
    const printable = (code >= 0x20 && code <= 0x7e) || code === 0x0a || code === 0x09;
    if (!printable) return false;
  }
  return true;
}

function formatString(value) {
  if (canUseLongBracket(value)) return `[[\n${value}]]`;
  return quoteString(value);
}

module.exports = {
  BINARY,
  UNARY_PREC,
  ATOM_PREC,
  PREFIXES,
  isIdentifier,
  formatNumber,
  formatString,
};
