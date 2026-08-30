'use strict';

const isDigit = (c) => c >= '0' && c <= '9';
const isHex = (c) => (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
const isLower = (c) => c >= 'a' && c <= 'z';
const isUpper = (c) => c >= 'A' && c <= 'Z';
const isAlpha = (c) => isLower(c) || isUpper(c) || c === '_';
const isAlnum = (c) => isAlpha(c) || isDigit(c);
const isSpace = (c) => c === ' ' || c === '\t' || c === '\r' || c === '\n' || c === '\v' || c === '\f';
const isNewline = (c) => c === '\n' || c === '\r';

const ESCAPES = {
  a: '\x07',
  b: '\b',
  f: '\f',
  n: '\n',
  r: '\r',
  t: '\t',
  v: '\v',
  '\\': '\\',
  '"': '"',
  "'": "'",
};

function parseHexNumber(text) {
  const body = text.slice(2);
  const pIndex = body.search(/[pP]/);
  const mantissa = pIndex === -1 ? body : body.slice(0, pIndex);
  const exponent = pIndex === -1 ? undefined : body.slice(pIndex + 1);
  const dot = mantissa.indexOf('.');
  const intPart = dot === -1 ? mantissa : mantissa.slice(0, dot);
  const fracPart = dot === -1 ? '' : mantissa.slice(dot + 1);
  let value = intPart ? parseInt(intPart, 16) : 0;
  for (let i = 0; i < fracPart.length; i += 1) {
    value += parseInt(fracPart[i], 16) / 16 ** (i + 1);
  }
  if (exponent !== undefined && exponent !== '') value *= 2 ** Number(exponent);
  return value;
}

function utf8Encode(code) {
  if (code < 0x80) return String.fromCharCode(code);
  if (code < 0x800) {
    return String.fromCharCode(0xc0 | (code >> 6), 0x80 | (code & 0x3f));
  }
  if (code < 0x10000) {
    return String.fromCharCode(
      0xe0 | (code >> 12),
      0x80 | ((code >> 6) & 0x3f),
      0x80 | (code & 0x3f),
    );
  }
  return String.fromCharCode(
    0xf0 | (code >> 18),
    0x80 | ((code >> 12) & 0x3f),
    0x80 | ((code >> 6) & 0x3f),
    0x80 | (code & 0x3f),
  );
}

module.exports = {
  isDigit,
  isHex,
  isLower,
  isUpper,
  isAlpha,
  isAlnum,
  isSpace,
  isNewline,
  ESCAPES,
  parseHexNumber,
  utf8Encode,
};
