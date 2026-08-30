'use strict';

const TokenKind = {
  Eof: 'Eof',
  Name: 'Name',
  Keyword: 'Keyword',
  Number: 'Number',
  String: 'String',
  Symbol: 'Symbol',
};

const KEYWORDS = new Set([
  'and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function',
  'goto', 'if', 'in', 'local', 'nil', 'not', 'or', 'repeat', 'return',
  'then', 'true', 'until', 'while', 'continue',
]);

const SYMBOLS = [
  '...', '..=',
  '==', '~=', '<=', '>=', '..', '::', '->', '//', '<<', '>>',
  '+=', '-=', '*=', '/=', '%=', '^=',
  '+', '-', '*', '/', '%', '^', '#', '=', '<', '>',
  '(', ')', '{', '}', '[', ']', ';', ':', ',', '.', '?', '|', '&', '~',
];

module.exports = { TokenKind, KEYWORDS, SYMBOLS };
