'use strict';

const { Lexer, TokenKind, LuaSyntaxError } = require('../lua/lexer');
const { Kind } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');

const isIdentChar = (ch) => ch !== undefined && ch !== ''
  && ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
    || (ch >= '0' && ch <= '9') || ch === '_');

const isDigit = (ch) => ch >= '0' && ch <= '9';

const ESC = String.fromCharCode(92);

const LF = String.fromCharCode(10);
const CR = String.fromCharCode(13);
const HT = String.fromCharCode(9);

const ESCAPES = new Set(['n', 'r', 't', 'a', 'b', 'v', '"', "'"]);

const NON_NUM = new Set([7, 8, 9, 10, 11, 13, 32, 34, 39, 45, 126]);

const LITERALS = new Set([' ', '-', '~']);

const RAW_ESCAPES = new Set([ESC, 'n', 'r', '"', "'"]);

const RAW_KEPT = new Set([ESC, '"', "'"]);

const STYLES = [
  {
    literal: (ch) => LITERALS.has(ch),
    named: ESCAPES,
    numeric: (value) => !NON_NUM.has(value),
  },
  {
    literal: (ch) => {
      const code = ch.charCodeAt(0);
      return code >= 32 && code <= 126 && !RAW_KEPT.has(ch);
    },
    named: RAW_ESCAPES,
    numeric: (value) => (value < 32 ? value !== 10 && value !== 13 : value > 126),
  },
];

function readString(raw, style, tally) {
  const end = raw.length - 1;
  let at = 1;
  while (at < end) {
    const ch = raw[at];
    if (ch !== ESC) {
      if (!style.literal(ch)) {
        return { at, message: `unescaped ${describeChar(ch)} in string` };
      }
      tally.literalExempt += 1;
      at += 1;
      continue;
    }
    const next = raw[at + 1];
    if (style.named.has(next)) {
      tally.namedEscapes += 1;
      at += 2;
      continue;
    }
    if (!isDigit(next)) return { at, message: `invalid escape \\${next}` };
    if (!isDigit(raw[at + 2]) || !isDigit(raw[at + 3])) {
      return { at, message: 'short decimal escape' };
    }
    const value = Number(raw.slice(at + 1, at + 4));
    if (value > 255) {
      return { at, message: `decimal escape > 255 (\\${raw.slice(at + 1, at + 4)})` };
    }
    if (!style.numeric(value)) {
      return {
        at,
        message: `redundant byte escape \\${raw.slice(at + 1, at + 4)}`,
      };
    }
    tally.numericEscapes += 1;
    at += 4;
  }
  return null;
}

function checkStringLiteral(raw, report, counts) {
  if (raw[0] !== '"') {
    report(raw.startsWith('[') ? 'bracket string' : 'single-quoted string');
    return;
  }
  let furthest = null;
  for (const style of STYLES) {
    const tally = { literalExempt: 0, namedEscapes: 0, numericEscapes: 0 };
    const failure = readString(raw, style, tally);
    if (failure) {
      if (!furthest || failure.at > furthest.at) furthest = failure;
      continue;
    }
    counts.literalExempt += tally.literalExempt;
    counts.namedEscapes += tally.namedEscapes;
    counts.numericEscapes += tally.numericEscapes;
    if (tally.numericEscapes > 0) counts.escapedText += 1;
    return;
  }
  report(furthest.message);
}

function describeChar(ch) {
  if (ch === undefined) return 'EOF';
  const code = ch.charCodeAt(0);
  if (code < 0x20 || code > 0x7e) return `byte ${code}`;
  return `'${ch}'`;
}

function checkNumberLiteral(text, previous, report, counts) {
  const lower = text.toLowerCase();
  if (lower.startsWith('0x')) {
    if (text !== lower && text !== text.toUpperCase()) counts.mixedHex += 1;
    return;
  }
  if (lower.startsWith('0b')) {
    report('binary literal');
    return;
  }
  if (text !== lower) {
    report(`uppercase in number ${text}`);
    return;
  }
  if (text.endsWith('.')) {
    report(`trailing decimal point in ${text}`);
    return;
  }
  if (text.length > 1 && text[0] === '0' && isDigit(text[1])) {
    report(`zero-padded number ${text}`);
    return;
  }

  if (text.startsWith('0.') && !(previous && previous.kind === TokenKind.Symbol && previous.value === '-')) {
    report(`leading zero in ${text}`);
  }
}

const MAX_ERRORS = 12;

function checkGap(gap, before, token, raw, report) {
  if (gap === '') return;
  if (gap !== ' ') {
    if (gap.includes('--')) report('comment');
    else if (gap.includes(LF) || gap.includes(CR)) report('newline');
    else if (gap.includes(HT)) report('tab character');
    else report('excess whitespace');
    return;
  }

  const left = before[before.length - 1];
  const right = raw[0];
  if (isIdentChar(left) || isIdentChar(right)) return;
  report(`unexpected space between ${describeChar(left)} and ${describeChar(right)}`);
}

function scanTokens(source) {
  const violations = [];
  const report = (message) => {
    if (violations.length < MAX_ERRORS) violations.push(message);
  };
  const counts = {
    tokens: 0,
    strings: 0,
    numbers: 0,
    tableSeparators: 0,
    mixedSeparators: 0,
    escapedText: 0,
    mixedHex: 0,
    namedEscapes: 0,
    numericEscapes: 0,
    literalExempt: 0,
    banner: 0,
  };
  const lexer = new Lexer(source);
  const brackets = [];
  let previous = null;
  let previousRaw = '';
  let previousEnd = 0;
  let semicolon = null;
  for (;;) {
    let token;
    try {
      token = lexer.next();
    } catch (error) {
      if (!(error instanceof LuaSyntaxError)) throw error;
      report(`lexer error: ${error.message}`);
      return { violations, counts, truncated: true };
    }
    const raw = token.kind === TokenKind.Eof ? '' : source.slice(token.offset, lexer.pos);
    const gap = source.slice(previousEnd, token.offset);
    if (previous === null || token.kind === TokenKind.Eof) {
      counts.banner += gap.length;
    } else {
      checkGap(gap, previousRaw, token, raw, report);
    }
    if (semicolon) {
      if (!(token.kind === TokenKind.Symbol && token.value === '(')) {
        const frame = semicolon.frame;
        if (frame && frame.ch === '{') {
          counts.tableSeparators += 1;
          frame.semi = true;
          if (frame.comma && !frame.mixed) {
            frame.mixed = true;
            counts.mixedSeparators += 1;
          }
        } else {
          report("unexpected ';'");
        }
      }
      semicolon = null;
    }
    if (token.kind === TokenKind.Eof) break;
    counts.tokens += 1;
    if (token.kind === TokenKind.String) {
      counts.strings += 1;
      checkStringLiteral(raw, report, counts);
    } else if (token.kind === TokenKind.Number) {
      counts.numbers += 1;
      checkNumberLiteral(token.text, previous, report, counts);
    } else if (token.kind === TokenKind.Symbol) {
      if (token.value === '(' || token.value === '[' || token.value === '{') {
        brackets.push({ ch: token.value, comma: false, semi: false, mixed: false });
      } else if (token.value === ')' || token.value === ']' || token.value === '}') {
        brackets.pop();
      } else if (token.value === ';') {
        semicolon = { frame: brackets[brackets.length - 1] || null };
      } else if (token.value === ',') {
        const frame = brackets[brackets.length - 1];
        if (frame && frame.ch === '{') {
          frame.comma = true;
          if (frame.semi && !frame.mixed) {
            frame.mixed = true;
            counts.mixedSeparators += 1;
          }
        }
      }
    }
    if (violations.length >= MAX_ERRORS) return { violations, counts, truncated: true };
    previous = token;
    previousRaw = raw;
    previousEnd = lexer.pos;
  }
  return { violations, counts, truncated: false };
}

function nameSignal(chunk) {
  const stack = [new Set()];
  const letters = new Set();
  let declared = 0;
  let letterStart = 0;
  let short = 0;
  let shadowed = 0;
  const isLetter = (ch) => (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z');
  const add = (name) => {
    if (typeof name !== 'string' || name.length === 0) return;
    declared += 1;
    if (isLetter(name[0])) letterStart += 1;
    if (name.length <= 2) short += 1;
    if (name.length === 1) letters.add(name);
    for (let i = 0; i < stack.length; i += 1) {
      if (stack[i].has(name)) { shadowed += 1; break; }
    }
    stack[stack.length - 1].add(name);
  };
  const SCOPED = new Set([
    Kind.Function, Kind.Block, Kind.NumericFor, Kind.GenericFor, Kind.Repeat,
  ]);
  walk(chunk, {
    enter: (node) => {
      if (SCOPED.has(node.kind)) stack.push(new Set());
      switch (node.kind) {
        case Kind.Function:
          for (const param of node.params || []) add(param);
          break;
        case Kind.LocalDeclaration:
          for (const name of node.names || []) add(name);
          break;
        case Kind.LocalFunction: add(node.name); break;
        case Kind.NumericFor: add(node.variable); break;
        case Kind.GenericFor:
          for (const name of node.variables || []) add(name);
          break;
        default: break;
      }
      return undefined;
    },
    leave: (node) => {
      if (SCOPED.has(node.kind)) stack.pop();
    },
  });
  return {
    declared,
    letterStart,
    short,
    shadowed,
    breadth: letters.size,
  };
}

const bare = (node) => {
  let at = node;
  while (at && at.kind === Kind.Paren) at = at.expression;
  return at;
};

const isNumber = (node, value) => !!node && node.kind === Kind.Number && node.value === value;

function wrapperSignal(node) {
  if (node.kind !== Kind.Return || node.expressions.length !== 1) return false;
  const call = bare(node.expressions[0]);
  if (!call || call.kind !== Kind.Call || call.args.length !== 1) return false;
  if (bare(call.args[0]).kind !== Kind.Vararg) return false;
  const target = bare(call.base);
  if (!target || target.kind !== Kind.Function) return false;
  return target.isVararg === true && (target.params || []).length === 0;
}

function rotateSignal(node) {
  if (node.kind !== Kind.GenericFor || node.expressions.length !== 1) return false;
  if ((node.variables || []).length !== 2) return false;
  const call = bare(node.expressions[0]);
  if (!call || call.kind !== Kind.Call || call.args.length !== 1) return false;
  const base = bare(call.base);
  if (!base || base.kind !== Kind.Name || base.name !== 'ipairs') return false;
  const table = bare(call.args[0]);
  if (!table || table.kind !== Kind.Table || table.entries.length !== 3) return false;
  for (const entry of table.entries) {
    if (entry.key) return false;
    const pair = bare(entry.value);
    if (!pair || pair.kind !== Kind.Table || pair.entries.length !== 2) return false;
    if (pair.entries[0].key || pair.entries[1].key) return false;
  }
  const body = node.body ? node.body.statements : [];
  if (body.length !== 1 || body[0].kind !== Kind.While) return false;
  const inner = body[0].body ? body[0].body.statements : [];
  if (inner.length !== 1 || inner[0].kind !== Kind.Assignment) return false;
  return inner[0].targets.length === 4 && inner[0].expressions.length === 4;
}

const PROXY_METAMETHODS = new Set(['__add', '__sub', '__index', '__mul', '__div', '__pow', '__concat']);

function proxySignal(node) {
  if (node.kind !== Kind.Table || node.entries.length !== 3) return false;
  for (const entry of node.entries) {
    const key = entry.key;
    if (!key || key.kind !== Kind.String || !PROXY_METAMETHODS.has(key.value)) return false;
  }
  return true;
}

const STREAM_MODULUS = 35184372088832;
const STREAM_PRIME = 257;

const ORDERING = new Set(['<', '>', '<=', '>=']);

function dispatchFrame(node) {
  const condition = bare(node.condition);
  if (!condition || condition.kind !== Kind.Name) return null;
  return { name: condition.name, ifs: 0, assigns: false, compares: false };
}

const isDispatch = (frame) => frame.ifs >= 2 && frame.assigns && frame.compares;

function shapeSignals(chunk) {
  const found = {
    wrapper: false,
    rotate: false,
    proxy: false,
    dispatcher: false,
    streamModulus: false,
    streamPrime: false,
    forStep: false,
    stepless: false,
  };

  const open = [];
  walk(chunk, {
    enter: (node) => {
      switch (node.kind) {
        case Kind.While:
          open.push(dispatchFrame(node));
          break;
        case Kind.If:
          for (const frame of open) if (frame) frame.ifs += 1;
          break;
        case Kind.Assignment:
          for (const frame of open) {
            if (!frame || frame.assigns) continue;
            for (const target of node.targets) {
              const at = bare(target);
              if (at && at.kind === Kind.Name && at.name === frame.name) frame.assigns = true;
            }
          }
          break;
        case Kind.Binary:
          if (ORDERING.has(node.operator)) {
            const lhs = bare(node.lhs);
            const rhs = bare(node.rhs);
            for (const frame of open) {
              if (!frame || frame.compares) continue;
              if ((lhs && lhs.kind === Kind.Name && lhs.name === frame.name)
                || (rhs && rhs.kind === Kind.Name && rhs.name === frame.name)) {
                frame.compares = true;
              }
            }
          }
          break;
        case Kind.Return:
          if (!found.wrapper && wrapperSignal(node)) found.wrapper = true;
          break;
        case Kind.Number:
          if (node.value === STREAM_MODULUS) found.streamModulus = true;
          else if (node.value === STREAM_PRIME) found.streamPrime = true;
          break;
        case Kind.Table:
          if (!found.proxy && proxySignal(node)) found.proxy = true;
          break;
        case Kind.GenericFor:
          if (!found.rotate && rotateSignal(node)) found.rotate = true;
          break;
        case Kind.NumericFor:
          if (!node.step) found.stepless = true;
          else if (isNumber(bare(node.step), 1)) found.forStep = true;
          break;
        default: break;
      }
      return undefined;
    },
    leave: (node) => {
      if (node.kind !== Kind.While) return;
      const frame = open.pop();
      if (frame && isDispatch(frame)) found.dispatcher = true;
    },
  });
  return found;
}

const NO_NAMES = { declared: 0, letterStart: 0, short: 0, shadowed: 0, breadth: 0 };
const NO_SHAPES = {
  wrapper: false,
  rotate: false,
  proxy: false,
  dispatcher: false,
  streamModulus: false,
  streamPrime: false,
  forStep: false,
  stepless: false,
};

function weigh(scan, names, shapes) {
  const evidence = [];
  const add = (weight, label) => evidence.push({ weight, label });
  const counts = scan.counts;
  if (shapes.dispatcher) add(2, 'a register machine dispatch loop');
  if (shapes.streamModulus && shapes.streamPrime) {
    add(2, "the string cipher's 2^45 modulus and 257 prime");
  }
  if (shapes.rotate) add(2, "the constant table's rotation loop");
  if (counts.escapedText > 0) {
    add(2, `${counts.escapedText} string(s) carrying numeric escapes for printable text`);
  }
  if (counts.mixedHex > 0) {
    add(counts.mixedHex > 1 ? 2 : 1, `${counts.mixedHex} hexadecimal number(s) in mixed case`);
  }
  if (shapes.wrapper) add(1, 'the vararg wrapper around the whole program');
  if (counts.mixedSeparators > 0) {
    add(1, `${counts.mixedSeparators} table(s) separated by both ',' and ';'`);
  } else if (counts.tableSeparators > 0) {
    add(1, `${counts.tableSeparators} table entries separated by ';'`);
  }
  if (shapes.proxy) add(1, 'a three metamethod proxy metatable');
  if (shapes.forStep) add(1, "a numeric for loop with its default step written out");
  if (names.breadth >= 12) {
    add(1, `${names.breadth} distinct single letter local names`);
  }
  if (names.shadowed > 0) {
    add(1, `${names.shadowed} local name(s) shadowing a name already in scope`);
  }
  if (names.declared >= 2 && names.short === names.declared
    && names.letterStart === names.declared) {
    add(1, `${names.declared} local names, all one or two letters`);
  }
  return evidence;
}

function requiredWeight(tokens) {
  if (tokens >= 2000) return 4;
  if (tokens >= 300) return 2;
  return 1;
}

function identify(source, chunk) {
  const body = source.trim();
  const scan = scanTokens(body);
  const names = chunk ? nameSignal(chunk) : NO_NAMES;
  const shapes = chunk ? shapeSignals(chunk) : NO_SHAPES;
  const evidence = weigh(scan, names, shapes);
  const weight = evidence.reduce((sum, item) => sum + item.weight, 0);
  const required = requiredWeight(scan.counts.tokens);
  const reasons = scan.violations.slice();
  if (!reasons.length && shapes.stepless) {
    reasons.push('for loop without step');
  }
  if (!reasons.length && weight < required) {
    reasons.push('insufficient Prometheus signatures'
      + (evidence.length ? ` (${evidence.map((item) => item.label).join(', ')})` : ''));
  }
  return {
    prometheus: reasons.length === 0,
    reasons,
    evidence,
    weight,
    required,
    names,
    shapes,
    counts: scan.counts,
  };
}

module.exports = { identify };
