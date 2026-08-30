'use strict';

const { tokenize, LuaSyntaxError } = require('./lexer');
const { TokenKind } = require('./tokens');
const A = require('./ast');

const { Kind } = A;

const BIN_PRIO = {
  or: [1, 1],
  and: [2, 2],
  '<': [3, 3], '>': [3, 3], '<=': [3, 3], '>=': [3, 3], '~=': [3, 3], '==': [3, 3],
  '|': [4, 4], '~': [5, 5], '&': [6, 6],
  '<<': [7, 7], '>>': [7, 7],
  '..': [9, 8],
  '+': [10, 10], '-': [10, 10],
  '*': [11, 11], '/': [11, 11], '//': [11, 11], '%': [11, 11],
  '^': [14, 13],
};

const UN_PRIO = 12;
const UNARY_OPS = new Set(['-', 'not', '#', '~']);

const COMPOUND_OPS = {
  '+=': '+', '-=': '-', '*=': '*', '/=': '/', '%=': '%', '^=': '^', '..=': '..',
};

const TERMINATORS = new Set(['end', 'else', 'elseif', 'until']);

class Parser {
  constructor(source) {
    this.tokens = tokenize(source);
    this.index = 0;
  }

  get token() {
    return this.tokens[this.index];
  }

  peek(offset = 1) {
    const i = this.index + offset;
    return i < this.tokens.length ? this.tokens[i] : this.tokens[this.tokens.length - 1];
  }

  advance() {
    const token = this.tokens[this.index];
    if (this.index < this.tokens.length - 1) this.index += 1;
    return token;
  }

  error(message, token = this.token) {
    throw new LuaSyntaxError(message, token.line, token.column);
  }

  at(value) {
    const t = this.token;
    return (t.kind === TokenKind.Symbol || t.kind === TokenKind.Keyword) && t.value === value;
  }

  accept(value) {
    if (!this.at(value)) return false;
    this.advance();
    return true;
  }

  expect(value) {
    if (!this.at(value)) this.error(`expected '${value}', got '${describe(this.token)}'`);
    return this.advance();
  }

  expectName() {
    if (this.token.kind !== TokenKind.Name) {
      this.error(`expected identifier, got '${describe(this.token)}'`);
    }
    return this.advance().value;
  }

  parseChunk() {
    const body = this.parseBlock();
    if (this.token.kind !== TokenKind.Eof) {
      this.error(`expected EOF, got '${describe(this.token)}'`);
    }
    return A.chunk(body);
  }

  parseBlock() {
    const statements = [];
    while (this.token.kind !== TokenKind.Eof) {
      if (this.token.kind === TokenKind.Keyword && TERMINATORS.has(this.token.value)) break;
      if (this.accept(';')) continue;
      if (this.token.kind === TokenKind.Keyword && this.token.value === 'return') {
        statements.push(this.parseReturn());
        this.accept(';');
        break;
      }
      statements.push(this.parseStatement());
    }
    return A.block(statements);
  }

  parseReturn() {
    this.expect('return');
    const expressions = this.blockEnds() || this.at(';') ? [] : this.parseExpressionList();
    return A.returnStatement(expressions);
  }

  blockEnds() {
    const t = this.token;
    if (t.kind === TokenKind.Eof) return true;
    return t.kind === TokenKind.Keyword && BLOCK_TERMINATORS.has(t.value);
  }

  parseStatement() {
    const t = this.token;
    if (t.kind === TokenKind.Keyword) {
      switch (t.value) {
        case 'local': return this.parseLocal();
        case 'if': return this.parseIf();
        case 'while': return this.parseWhile();
        case 'do': {
          this.advance();
          const body = this.parseBlock();
          this.expect('end');
          return A.doStatement(body);
        }
        case 'for': return this.parseFor();
        case 'repeat': return this.parseRepeat();
        case 'function': return this.parseFunctionDeclaration();
        case 'break': this.advance(); return A.breakStatement();
        case 'continue': this.advance(); return { kind: Kind.Continue };
        case 'goto': this.advance(); return { kind: Kind.Goto, label: this.expectName() };
        default: break;
      }
    }
    if (this.at('::')) {
      this.advance();
      const label = this.expectName();
      this.expect('::');
      return { kind: Kind.Label, name: label };
    }
    return this.parseExpressionStatement();
  }

  parseLocal() {
    this.expect('local');
    if (this.accept('function')) {
      const id = this.expectName();
      const body = this.parseFunctionBody();
      return { kind: Kind.LocalFunction, name: id, body };
    }
    const names = [this.parseAttributedName()];
    while (this.accept(',')) names.push(this.parseAttributedName());
    const expressions = this.accept('=') ? this.parseExpressionList() : [];
    return A.localDecl(names, expressions);
  }

  parseAttributedName() {
    const id = this.expectName();
    if (this.at('<')) {
      this.advance();
      this.expectName();
      this.expect('>');
    } else if (this.at(':')) {
      this.advance();
      this.skipTypeAnnotation();
    }
    return id;
  }

  skipTypeAnnotation() {
    let depth = 0;
    for (;;) {
      const t = this.token;
      if (t.kind === TokenKind.Eof) return;
      if (t.kind === TokenKind.Symbol) {
        if (t.value === '(' || t.value === '{' || t.value === '<') depth += 1;
        else if (t.value === ')' || t.value === '}' || t.value === '>') {
          if (depth === 0) return;
          depth -= 1;
        } else if (depth === 0 && (t.value === ',' || t.value === '=' || t.value === ';')) {
          return;
        }
      } else if (t.kind === TokenKind.Keyword && depth === 0 && t.value !== 'nil') {
        return;
      }
      this.advance();
    }
  }

  parseIf() {
    this.expect('if');
    const condition = this.parseExpression();
    this.expect('then');
    const body = this.parseBlock();
    const elseIfs = [];
    let elseBody = null;
    for (;;) {
      if (this.accept('elseif')) {
        const cond = this.parseExpression();
        this.expect('then');
        elseIfs.push({ condition: cond, body: this.parseBlock() });
        continue;
      }
      if (this.accept('else')) elseBody = this.parseBlock();
      break;
    }
    this.expect('end');
    return A.ifStatement(condition, body, elseIfs, elseBody);
  }

  parseWhile() {
    this.expect('while');
    const condition = this.parseExpression();
    this.expect('do');
    const body = this.parseBlock();
    this.expect('end');
    return A.whileStatement(condition, body);
  }

  parseRepeat() {
    this.expect('repeat');
    const body = this.parseBlock();
    this.expect('until');
    return A.repeatStatement(body, this.parseExpression());
  }

  parseFor() {
    this.expect('for');
    const first = this.parseAttributedName();
    if (this.accept('=')) {
      const start = this.parseExpression();
      this.expect(',');
      const limit = this.parseExpression();
      const step = this.accept(',') ? this.parseExpression() : null;
      this.expect('do');
      const body = this.parseBlock();
      this.expect('end');
      return A.numericFor(first, start, limit, step, body);
    }
    const variables = [first];
    while (this.accept(',')) variables.push(this.parseAttributedName());
    this.expect('in');
    const expressions = this.parseExpressionList();
    this.expect('do');
    const body = this.parseBlock();
    this.expect('end');
    return A.genericFor(variables, expressions, body);
  }

  parseFunctionDeclaration() {
    this.expect('function');
    let target = A.name(this.expectName());
    let isMethod = false;
    for (;;) {
      if (this.accept('.')) {
        target = A.index(target, A.string(this.expectName()));
        continue;
      }
      if (this.accept(':')) {
        target = A.index(target, A.string(this.expectName()));
        isMethod = true;
      }
      break;
    }
    const body = this.parseFunctionBody(isMethod);
    return { kind: Kind.FunctionDeclaration, target, isMethod, body };
  }

  parseFunctionBody(isMethod = false) {
    if (this.at('<')) this.skipGenericParams();
    this.expect('(');
    const params = isMethod ? ['self'] : [];
    let isVararg = false;
    if (!this.at(')')) {
      do {
        if (this.accept('...')) {
          isVararg = true;
          if (this.accept(':')) this.skipTypeAnnotation();
          break;
        }
        params.push(this.parseAttributedName());
      } while (this.accept(','));
    }
    this.expect(')');
    if (this.accept(':')) this.skipTypeAnnotation();
    const body = this.parseBlock();
    this.expect('end');
    return A.func(params, body, isVararg);
  }

  skipGenericParams() {
    this.expect('<');
    let depth = 1;
    while (depth > 0 && this.token.kind !== TokenKind.Eof) {
      if (this.at('<')) depth += 1;
      else if (this.at('>')) depth -= 1;
      this.advance();
    }
  }

  parseExpressionStatement() {
    const first = this.parseSuffixedExpression();
    if (this.at('=') || this.at(',')) {
      const targets = [first];
      while (this.accept(',')) targets.push(this.parseSuffixedExpression());
      this.expect('=');
      const expressions = this.parseExpressionList();
      for (const target of targets) {
        if (!A.ASSIGNABLE.has(target.kind)) this.error('invalid assignment target');
      }
      return A.assignment(targets, expressions);
    }
    const compound = this.token.kind === TokenKind.Symbol
      ? COMPOUND_OPS[this.token.value] : undefined;
    if (compound) {
      this.advance();
      const rhs = this.parseExpression();
      return A.assignment([first], [A.binary(compound, first, rhs)]);
    }
    if (first.kind !== Kind.Call && first.kind !== Kind.MethodCall) {
      this.error('unexpected expression statement');
    }
    return A.callStatement(first);
  }

  parseExpressionList() {
    const list = [this.parseExpression()];
    while (this.accept(',')) list.push(this.parseExpression());
    return list;
  }

  parseExpression(limit = 0) {
    let left;
    const t = this.token;
    const isUnary = (t.kind === TokenKind.Symbol && UNARY_OPS.has(t.value))
      || (t.kind === TokenKind.Keyword && t.value === 'not');
    if (isUnary) {
      const operator = this.advance().value;
      left = A.unary(operator, this.parseExpression(UN_PRIO));
    } else {
      left = this.parseSimpleExpression();
    }
    for (;;) {
      const op = this.token;
      const isBinary = (op.kind === TokenKind.Symbol || op.kind === TokenKind.Keyword)
        && Object.prototype.hasOwnProperty.call(BIN_PRIO, op.value);
      if (!isBinary) break;
      const [leftPriority, rightPriority] = BIN_PRIO[op.value];
      if (leftPriority <= limit) break;
      this.advance();
      left = A.binary(op.value, left, this.parseExpression(rightPriority));
    }
    return left;
  }

  parseSimpleExpression() {
    const t = this.token;
    switch (t.kind) {
      case TokenKind.Number: this.advance(); return A.number(t.value);
      case TokenKind.String: this.advance(); return A.string(t.value);
      case TokenKind.Keyword:
        if (t.value === 'nil') { this.advance(); return A.nil(); }
        if (t.value === 'true') { this.advance(); return A.boolean(true); }
        if (t.value === 'false') { this.advance(); return A.boolean(false); }
        if (t.value === 'function') { this.advance(); return this.parseFunctionBody(); }
        break;
      case TokenKind.Symbol:
        if (t.value === '...') { this.advance(); return A.vararg(); }
        if (t.value === '{') return this.parseTable();
        break;
      default: break;
    }
    return this.parseSuffixedExpression();
  }

  parsePrimaryExpression() {
    if (this.accept('(')) {
      const inner = this.parseExpression();
      this.expect(')');
      return A.paren(inner);
    }
    if (this.token.kind === TokenKind.Name) return A.name(this.advance().value);
    return this.error(`unexpected token '${describe(this.token)}'`);
  }

  parseSuffixedExpression() {
    let node = this.parsePrimaryExpression();
    for (;;) {
      if (this.accept('.')) {
        node = A.index(node, A.string(this.expectName()), true);
        continue;
      }
      if (this.accept('[')) {
        const key = this.parseExpression();
        this.expect(']');
        node = A.index(node, key);
        continue;
      }
      if (this.at(':') && this.peek().kind === TokenKind.Name) {
        this.advance();
        const method = this.expectName();
        node = A.methodCall(node, method, this.parseCallArguments());
        continue;
      }
      if (this.at('(') || this.at('{') || this.token.kind === TokenKind.String) {
        node = A.call(node, this.parseCallArguments());
        continue;
      }
      return node;
    }
  }

  parseCallArguments() {
    if (this.token.kind === TokenKind.String) return [A.string(this.advance().value)];
    if (this.at('{')) return [this.parseTable()];
    this.expect('(');
    if (this.accept(')')) return [];
    const args = this.parseExpressionList();
    this.expect(')');
    return args;
  }

  parseTable() {
    this.expect('{');
    const entries = [];
    while (!this.at('}')) {
      if (this.accept('[')) {
        const key = this.parseExpression();
        this.expect(']');
        this.expect('=');
        entries.push({ type: 'key', key, value: this.parseExpression() });
      } else if (this.token.kind === TokenKind.Name && this.peek().kind === TokenKind.Symbol
        && this.peek().value === '=') {
        const key = A.string(this.advance().value);
        this.advance();
        entries.push({ type: 'key', key, value: this.parseExpression() });
      } else {
        entries.push({ type: 'item', value: this.parseExpression() });
      }
      if (!this.accept(',') && !this.accept(';')) break;
    }
    this.expect('}');
    return A.table(entries);
  }
}

function describe(token) {
  if (token.kind === TokenKind.Eof) return '<eof>';
  if (token.kind === TokenKind.String) return `"${token.value}"`;
  return String(token.value);
}

function parse(source) {
  return new Parser(source).parseChunk();
}

module.exports = { parse, LuaSyntaxError };
