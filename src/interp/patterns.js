'use strict';

const { LuaError } = require('./values');

const L_ESC = '%';
const MAX_CAPS = 32;
const UNFINISHED = -1;
const POSITION = -2;

const isDigitCode = (c) => c >= 48 && c <= 57;
const isAlphaCode = (c) => (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
const isLowerCode = (c) => c >= 97 && c <= 122;
const isUpperCode = (c) => c >= 65 && c <= 90;
const isSpaceCode = (c) => c === 32 || (c >= 9 && c <= 13);
const isControlCode = (c) => c < 32 || c === 127;
const isPunctCode = (c) => (c >= 33 && c <= 47) || (c >= 58 && c <= 64)
  || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
const isHexCode = (c) => isDigitCode(c) || (c >= 97 && c <= 102) || (c >= 65 && c <= 70);

function matchClass(code, classChar) {
  let result;
  switch (classChar.toLowerCase()) {
    case 'a': result = isAlphaCode(code); break;
    case 'c': result = isControlCode(code); break;
    case 'd': result = isDigitCode(code); break;
    case 'l': result = isLowerCode(code); break;
    case 'p': result = isPunctCode(code); break;
    case 's': result = isSpaceCode(code); break;
    case 'u': result = isUpperCode(code); break;
    case 'w': result = isAlphaCode(code) || isDigitCode(code); break;
    case 'x': result = isHexCode(code); break;
    case 'z': result = code === 0; break;
    default: return classChar.charCodeAt(0) === code;
  }
  return classChar >= 'A' && classChar <= 'Z' ? !result : result;
}

class Matcher {
  constructor(source, pattern) {
    this.src = source;
    this.pattern = pattern;
    this.level = 0;
    this.captureStart = new Array(MAX_CAPS).fill(0);
    this.captureLen = new Array(MAX_CAPS).fill(0);
    this.depth = 0;
  }

  error(message) {
    throw new LuaError(message);
  }

  classEnd(pi) {
    const p = this.pattern;
    const c = p[pi];
    pi += 1;
    if (c === L_ESC) {
      if (pi >= p.length) this.error("pattern ends with '%'");
      return pi + 1;
    }
    if (c === '[') {
      if (p[pi] === '^') pi += 1;
      do {
        if (pi >= p.length) this.error("missing ']' in pattern");
        const cc = p[pi];
        pi += 1;
        if (cc === L_ESC) {
          if (pi >= p.length) this.error("pattern ends with '%'");
          pi += 1;
        }
      } while (p[pi] !== ']');
      return pi + 1;
    }
    return pi;
  }

  matchBracketClass(code, pi, ecl) {
    const p = this.pattern;
    let negate = false;
    pi += 1;
    if (p[pi] === '^') {
      negate = true;
      pi += 1;
    }
    while (pi < ecl) {
      if (p[pi] === L_ESC) {
        pi += 1;
        if (matchClass(code, p[pi])) return !negate;
        pi += 1;
      } else if (p[pi + 1] === '-' && pi + 2 < ecl) {
        if (p.charCodeAt(pi) <= code && code <= p.charCodeAt(pi + 2)) return !negate;
        pi += 3;
      } else {
        if (p.charCodeAt(pi) === code) return !negate;
        pi += 1;
      }
    }
    return negate;
  }

  singleMatch(si, pi, ep) {
    if (si >= this.src.length) return false;
    const code = this.src.charCodeAt(si);
    const pc = this.pattern[pi];
    if (pc === '.') return true;
    if (pc === L_ESC) return matchClass(code, this.pattern[pi + 1]);
    if (pc === '[') return this.matchBracketClass(code, pi, ep - 1);
    return this.pattern.charCodeAt(pi) === code;
  }

  matchBalance(si, pi) {
    if (pi + 1 >= this.pattern.length) this.error("missing '%b' arguments");
    if (this.src[si] !== this.pattern[pi]) return -1;
    const begin = this.pattern[pi];
    const end = this.pattern[pi + 1];
    let count = 1;
    let i = si + 1;
    while (i < this.src.length) {
      const c = this.src[i];
      if (c === end) {
        count -= 1;
        if (count === 0) return i + 1;
      } else if (c === begin) {
        count += 1;
      }
      i += 1;
    }
    return -1;
  }

  maxExpand(si, pi, ep) {
    let i = 0;
    while (this.singleMatch(si + i, pi, ep)) i += 1;
    while (i >= 0) {
      const result = this.match(si + i, ep + 1);
      if (result !== -1) return result;
      i -= 1;
    }
    return -1;
  }

  minExpand(si, pi, ep) {
    for (;;) {
      const result = this.match(si, ep + 1);
      if (result !== -1) return result;
      if (this.singleMatch(si, pi, ep)) si += 1;
      else return -1;
    }
  }

  startCapture(si, pi, what) {
    const level = this.level;
    if (level >= MAX_CAPTURES) this.error('too many captures');
    this.captureStart[level] = si;
    this.captureLen[level] = what;
    this.level = level + 1;
    const result = this.match(si, pi);
    if (result === -1) this.level -= 1;
    return result;
  }

  endCapture(si, pi) {
    const level = this.captureToClose();
    this.captureLen[level] = si - this.captureStart[level];
    const result = this.match(si, pi);
    if (result === -1) this.captureLen[level] = CAP_UNFINISHED;
    return result;
  }

  captureToClose() {
    for (let level = this.level - 1; level >= 0; level -= 1) {
      if (this.captureLen[level] === CAP_UNFINISHED) return level;
    }
    return this.error('invalid capture');
  }

  matchCapture(si, index) {
    const level = index - 49;
    if (level < 0 || level >= this.level || this.captureLen[level] === CAP_UNFINISHED) {
      this.error(`invalid capture index %${level + 1}`);
    }
    const len = this.captureLen[level];
    const captured = this.src.substr(this.captureStart[level], len);
    if (this.src.substr(si, len) === captured) return si + len;
    return -1;
  }

  match(si, pi) {
    this.depth += 1;
    if (this.depth > 220) this.error('pattern too complex');
    try {
      return this.matchInner(si, pi);
    } finally {
      this.depth -= 1;
    }
  }

  matchInner(si, pi) {
    const p = this.pattern;
    for (;;) {
      if (pi >= p.length) return si;
      switch (p[pi]) {
        case '(':
          return p[pi + 1] === ')'
            ? this.startCapture(si, pi + 2, POSITION)
            : this.startCapture(si, pi + 1, UNFINISHED);
        case ')':
          return this.endCapture(si, pi + 1);
        case '$':
          if (pi + 1 === p.length) return si === this.src.length ? si : -1;
          break;
        case L_ESC:
          switch (p[pi + 1]) {
            case 'b': {
              const result = this.matchBalance(si, pi + 2);
              if (result === -1) return -1;
              si = result;
              pi += 4;
              continue;
            }
            case 'f': {
              pi += 2;
              if (p[pi] !== '[') this.error("expected '[' after '%f'");
              const ep = this.classEnd(pi);
              const previous = si === 0 ? 0 : this.src.charCodeAt(si - 1);
              const current = si < this.src.length ? this.src.charCodeAt(si) : 0;
              if (!this.matchBracketClass(previous, pi, ep - 1)
                && this.matchBracketClass(current, pi, ep - 1)) {
                pi = ep;
                continue;
              }
              return -1;
            }
            default:
              if (isDigitCode(p.charCodeAt(pi + 1))) {
                const result = this.matchCapture(si, p.charCodeAt(pi + 1));
                if (result === -1) return -1;
                si = result;
                pi += 2;
                continue;
              }
              break;
          }
          break;
        default:
          break;
      }
      const ep = this.classEnd(pi);
      const matches = this.singleMatch(si, pi, ep);
      const suffix = ep < p.length ? p[ep] : '';
      if (suffix === '?') {
        if (matches) {
          const result = this.match(si + 1, ep + 1);
          if (result !== -1) return result;
        }
        pi = ep + 1;
        continue;
      }
      if (suffix === '+') return matches ? this.maxExpand(si + 1, pi, ep) : -1;
      if (suffix === '*') return this.maxExpand(si, pi, ep);
      if (suffix === '-') return this.minExpand(si, pi, ep);
      if (!matches) return -1;
      si += 1;
      pi = ep;
    }
  }

  captures(start, end, wholeIfNone = true) {
    if (this.level === 0 && wholeIfNone) return [this.src.slice(start, end)];
    const out = [];
    for (let i = 0; i < this.level; i += 1) {
      if (this.captureLen[i] === POSITION) out.push(this.captureStart[i] + 1);
      else out.push(this.src.substr(this.captureStart[i], this.captureLen[i]));
    }
    return out;
  }
}

function find(source, pattern, init = 0) {
  const anchored = pattern[0] === '^';
  const p = anchored ? 1 : 0;
  let si = init;
  do {
    const matcher = new Matcher(source, pattern);
    matcher.level = 0;
    const end = matcher.match(si, p);
    if (end !== -1) {
      return { start: si, end, captures: matcher.captures(si, end), matcher };
    }
    si += 1;
  } while (si <= source.length && !anchored);
  return null;
}

module.exports = { find, Matcher };
