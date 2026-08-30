'use strict';

const { TokenKind, KEYWORDS, SYMBOLS } = require('./tokens');
const C = require('./chars');

class LuaSyntaxError extends Error {
  constructor(message, line, column) {
    super(`${message} (line ${line}, col ${column})`);
    this.name = 'LuaSyntaxError';
    this.line = line;
    this.column = column;
  }
}

class Lexer {
  constructor(source) {
    this.src = source;
    this.len = source.length;
    this.pos = 0;
    this.line = 1;
    this.lineStart = 0;
  }

  error(message) {
    throw new LuaSyntaxError(message, this.line, this.pos - this.lineStart + 1);
  }

  peek(offset = 0) {
    const i = this.pos + offset;
    return i < this.len ? this.src[i] : '';
  }

  newline() {
    const c = this.src[this.pos];
    this.pos += 1;
    const n = this.src[this.pos];
    if ((n === '\n' || n === '\r') && n !== c) this.pos += 1;
    this.line += 1;
    this.lineStart = this.pos;
  }

  skipTrivia() {
    for (;;) {
      const c = this.peek();
      if (c === '') return;
      if (C.isNewline(c)) {
        this.newline();
        continue;
      }
      if (C.isSpace(c)) {
        this.pos += 1;
        continue;
      }
      if (c === '-' && this.peek(1) === '-') {
        this.pos += 2;
        const level = this.longBracketLevel();
        if (level !== null) {
          this.readLongBracket(level);
          continue;
        }
        while (this.pos < this.len && !C.isNewline(this.src[this.pos])) this.pos += 1;
        continue;
      }
      return;
    }
  }

  longBracketLevel() {
    if (this.peek() !== '[') return null;
    let i = this.pos + 1;
    let level = 0;
    while (i < this.len && this.src[i] === '=') {
      level += 1;
      i += 1;
    }
    if (this.src[i] !== '[') return null;
    this.pos = i + 1;
    return level;
  }

  readLongBracket(level) {
    if (C.isNewline(this.peek())) this.newline();
    const closer = `]${'='.repeat(level)}]`;
    let out = '';
    for (;;) {
      if (this.pos >= this.len) this.error('unterminated long string/comment');
      if (this.src.startsWith(closer, this.pos)) {
        this.pos += closer.length;
        return out;
      }
      const c = this.src[this.pos];
      if (C.isNewline(c)) {
        this.newline();
        out += '\n';
        continue;
      }
      out += c;
      this.pos += 1;
    }
  }

  readShortString(quote) {
    this.pos += 1;
    let out = '';
    for (;;) {
      if (this.pos >= this.len) this.error('unterminated string');
      const c = this.src[this.pos];
      if (c === quote) {
        this.pos += 1;
        return out;
      }
      if (C.isNewline(c)) this.error('unterminated string');
      if (c !== '\\') {
        out += c;
        this.pos += 1;
        continue;
      }
      this.pos += 1;
      out += this.readEscape();
    }
  }

  readEscape() {
    const e = this.peek();
    if (e === '') this.error('unterminated escape sequence');
    if (C.isNewline(e)) {
      this.newline();
      return '\n';
    }
    if (Object.prototype.hasOwnProperty.call(C.ESCAPES, e)) {
      this.pos += 1;
      return C.ESCAPES[e];
    }
    if (e === 'x' || e === 'X') {
      this.pos += 1;
      let hex = '';
      while (hex.length < 2 && C.isHex(this.peek())) {
        hex += this.src[this.pos];
        this.pos += 1;
      }
      if (hex.length === 0) this.error('hex digit expected');
      return String.fromCharCode(parseInt(hex, 16));
    }
    if (e === 'z') {
      this.pos += 1;
      while (this.pos < this.len && C.isSpace(this.src[this.pos])) {
        if (C.isNewline(this.src[this.pos])) this.newline();
        else this.pos += 1;
      }
      return '';
    }
    if (e === 'u') {
      this.pos += 1;
      if (this.peek() !== '{') this.error("expected '{' after \\u");
      this.pos += 1;
      let hex = '';
      while (C.isHex(this.peek())) {
        hex += this.src[this.pos];
        this.pos += 1;
      }
      if (this.peek() !== '}') this.error("expected '}'");
      this.pos += 1;
      return C.utf8Encode(parseInt(hex, 16));
    }
    if (C.isDigit(e)) {
      let dec = '';
      while (dec.length < 3 && C.isDigit(this.peek())) {
        dec += this.src[this.pos];
        this.pos += 1;
      }
      const value = parseInt(dec, 10);
      if (value > 255) this.error('decimal escape out of range');
      return String.fromCharCode(value);
    }
    return this.error(`invalid escape '\\${e}'`);
  }

  readNumber() {
    const start = this.pos;
    if (this.peek() === '0' && (this.peek(1) === 'x' || this.peek(1) === 'X')) {
      this.pos += 2;
      while (C.isHex(this.peek()) || this.peek() === '.') this.pos += 1;
      if (this.peek() === 'p' || this.peek() === 'P') {
        this.pos += 1;
        if (this.peek() === '+' || this.peek() === '-') this.pos += 1;
        while (C.isDigit(this.peek())) this.pos += 1;
      }
      const text = this.src.slice(start, this.pos);
      return { text, value: C.parseHexNumber(text) };
    }
    if (this.peek() === '0' && (this.peek(1) === 'b' || this.peek(1) === 'B')) {
      this.pos += 2;
      while (this.peek() === '0' || this.peek() === '1') this.pos += 1;
      const text = this.src.slice(start, this.pos);
      return { text, value: parseInt(text.slice(2), 2) };
    }
    while (C.isDigit(this.peek())) this.pos += 1;
    if (this.peek() === '.') {
      this.pos += 1;
      while (C.isDigit(this.peek())) this.pos += 1;
    }
    if (this.peek() === 'e' || this.peek() === 'E') {
      this.pos += 1;
      if (this.peek() === '+' || this.peek() === '-') this.pos += 1;
      while (C.isDigit(this.peek())) this.pos += 1;
    }
    const text = this.src.slice(start, this.pos);
    const value = Number(text);
    if (Number.isNaN(value)) this.error(`malformed number '${text}'`);
    return { text, value };
  }

  next() {
    this.skipTrivia();
    const line = this.line;
    const column = this.pos - this.lineStart + 1;
    const offset = this.pos;
    if (this.pos >= this.len) {
      return { kind: TokenKind.Eof, value: null, line, column, offset };
    }
    const c = this.src[this.pos];

    if (C.isAlpha(c)) {
      let i = this.pos;
      while (i < this.len && C.isAlnum(this.src[i])) i += 1;
      const word = this.src.slice(this.pos, i);
      this.pos = i;
      const kind = KEYWORDS.has(word) ? TokenKind.Keyword : TokenKind.Name;
      return { kind, value: word, line, column, offset };
    }

    if (C.isDigit(c) || (c === '.' && C.isDigit(this.peek(1)))) {
      const num = this.readNumber();
      return { kind: TokenKind.Number, value: num.value, text: num.text, line, column, offset };
    }

    if (c === '"' || c === "'") {
      return { kind: TokenKind.String, value: this.readShortString(c), line, column, offset };
    }

    if (c === '[') {
      const level = this.longBracketLevel();
      if (level !== null) {
        const value = this.readLongBracket(level);
        return { kind: TokenKind.String, value, long: true, level, line, column, offset };
      }
    }

    for (let i = 0; i < SYMBOLS.length; i += 1) {
      const sym = SYMBOLS[i];
      if (this.src.startsWith(sym, this.pos)) {
        this.pos += sym.length;
        return { kind: TokenKind.Symbol, value: sym, line, column, offset };
      }
    }

    return this.error(`unexpected char '${c}'`);
  }

  tokenize() {
    const tokens = [];
    for (;;) {
      const token = this.next();
      tokens.push(token);
      if (token.kind === TokenKind.Eof) return tokens;
    }
  }
}

function tokenize(source) {
  return new Lexer(source).tokenize();
}

module.exports = { Lexer, tokenize, LuaSyntaxError, TokenKind };
