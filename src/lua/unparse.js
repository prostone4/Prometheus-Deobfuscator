'use strict';

const { Kind } = require('./ast');
const F = require('./format');
const layout = require('./layout');

const DEFAULTS = { indent: '  ', maxInlineWidth: 96 };

const OPENERS = new Set(['do', 'then', 'else', 'repeat']);

const FLAT = new Set(['and', 'or']);

function tailToken(text) {
  const trimmed = text.trimEnd();
  if (!trimmed) return '';
  const isWord = (ch) => (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
    || (ch >= '0' && ch <= '9') || ch === '_';
  const end = trimmed.length;
  if (!isWord(trimmed[end - 1])) return trimmed[end - 1];
  let start = end;
  while (start > 0 && isWord(trimmed[start - 1])) start -= 1;
  return trimmed.slice(start, end);
}

class Printer {
  constructor(options = {}) {
    this.options = { ...DEFAULTS, ...options };
    this.lines = [];
    this.depth = 0;
    this.tail = '';
    this.column = 0;
    this.tight = false;
  }

  push(text) {
    this.lines.push(text === '' ? '' : this.options.indent.repeat(this.depth) + text);
    if (text !== '') this.tail = tailToken(text);
  }

  continues() {
    if (!this.lines.length) return false;
    return !(OPENERS.has(this.tail) || this.tail === ';' || this.tail === ':');
  }

  blank() {
    if (this.lines.length && this.lines[this.lines.length - 1] !== '') this.lines.push('');
  }

  indented(fn) {
    this.depth += 1;
    fn();
    this.depth -= 1;
  }

  from(column, fn) {
    const saved = this.column;
    this.column = column;
    const text = fn();
    this.column = saved;
    return text;
  }

  after(head, fn) {
    return head + this.from(this.startOf(head), fn);
  }

  packed(fn) {
    const saved = this.tight;
    this.tight = true;
    const text = fn();
    this.tight = saved;
    return text;
  }

  startOf(head) {
    return this.column + head.length;
  }

  wrap(head, list) {
    const flat = head + list.join(', ');
    if (this.fits(flat)) return flat;
    const indent = this.options.indent.repeat(this.depth + 1);
    const rows = [];
    let row = head.trimEnd();
    let start = this.column;
    for (let at = 0; at < list.length; at += 1) {
      const piece = at === list.length - 1 ? list[at] : `${list[at]},`;
      const joined = row ? `${row} ${piece}` : piece;
      if (start + joined.length <= this.options.maxInlineWidth) {
        row = joined;
      } else {
        rows.push(row);
        row = piece;
        start = indent.length;
      }
    }
    rows.push(row);
    return rows.join(`\n${indent}`);
  }

  fits(flat) {
    return !flat.includes('\n') && this.column + flat.length <= this.options.maxInlineWidth;
  }

  inner() {
    const sub = new Printer(this.options);
    sub.tight = this.tight;
    sub.depth = this.depth + 1;
    sub.column = this.options.indent.length * sub.depth;
    return sub;
  }

  toString() {
    return `${this.lines.join('\n').replace(/\s+$/, '')}\n`;
  }

  block(node) {
    if (!node || !node.statements) return;
    const statements = node.statements;
    const found = layout.groups(statements);
    let above = false;
    for (let at = 0; at < statements.length; at += 1) {
      const start = this.lines.length;
      this.statement(statements[at]);
      const written = this.lines.length - start;
      const wide = written > 1 || (written === 1 && this.lines[start].indexOf('\n') >= 0);
      if (layout.separates(found, at, wide, above)) this.lines.splice(start, 0, '');
      above = wide;
    }
  }

  statement(node) {
    this.column = this.options.indent.length * this.depth;
    switch (node.kind) {
      case Kind.LocalDeclaration: {
        const names = node.names.join(', ');
        if (!node.expressions || node.expressions.length === 0) {
          this.push(this.wrap('local ', node.names));
        } else {
          this.push(this.after(`local ${names} = `,
            () => this.expressionList(node.expressions)));
        }
        return;
      }
      case Kind.LocalFunction:
        this.functionBody(`local function ${node.name}`, node.body);
        return;
      case Kind.FunctionDeclaration: {
        const target = this.targetPath(node.target, node.isMethod);
        this.functionBody(`function ${target}`, node.body, node.isMethod);
        return;
      }
      case Kind.Assignment: {
        const text = this.after(`${this.expressionList(node.targets)} = `,
          () => this.expressionList(node.expressions));
        this.push(text.startsWith('(') && this.continues() ? `;${text}` : text);
        return;
      }
      case Kind.CallStatement: {
        const text = this.expression(node.expression);
        this.push(text.startsWith('(') && this.continues() ? `;${text}` : text);
        return;
      }
      case Kind.Return:
        if (!node.expressions || node.expressions.length === 0) this.push('return');
        else this.push(this.after('return ', () => this.expressionList(node.expressions)));
        return;
      case Kind.Break:
        this.push('break');
        return;
      case Kind.Continue:
        this.push('continue');
        return;
      case Kind.Goto:
        this.push(`goto ${node.label}`);
        return;
      case Kind.Label:
        this.push(`::${node.name}::`);
        return;
      case Kind.Do:
        this.push('do');
        this.indented(() => this.block(node.body));
        this.push('end');
        return;
      case Kind.While:
        this.push(`${this.after('while ', () => this.expression(node.condition))} do`);
        this.indented(() => this.block(node.body));
        this.push('end');
        return;
      case Kind.Repeat:
        this.push('repeat');
        this.indented(() => this.block(node.body));
        this.push(this.after('until ', () => this.expression(node.condition)));
        return;
      case Kind.If:
        this.ifStatement(node);
        return;
      case Kind.NumericFor: {
        const bounds = [node.start, node.limit];
        if (node.step) bounds.push(node.step);
        this.push(`${this.after(`for ${node.variable} = `,
          () => this.expressionList(bounds))} do`);
        this.indented(() => this.block(node.body));
        this.push('end');
        return;
      }
      case Kind.GenericFor:
        this.push(`${this.after(`for ${node.variables.join(', ')} in `,
          () => this.expressionList(node.expressions))} do`);
        this.indented(() => this.block(node.body));
        this.push('end');
        return;
      default:
        this.push(`--[[ unsupported statement ${node.kind} ]]`);
    }
  }

  ifStatement(node) {
    this.push(`${this.after('if ', () => this.expression(node.condition))} then`);
    this.indented(() => this.block(node.body));
    for (const clause of node.elseIfs || []) {
      this.push(`${this.after('elseif ', () => this.expression(clause.condition))} then`);
      this.indented(() => this.block(clause.body));
    }
    if (node.elseBody) {
      this.push('else');
      this.indented(() => this.block(node.elseBody));
    }
    this.push('end');
  }

  targetPath(node, isMethod) {
    if (node.kind !== Kind.Index) return this.expression(node);
    const key = node.index;
    if (isMethod && key.kind === Kind.String && F.isIdentifier(key.value)) {
      return `${this.expression(node.base)}:${key.value}`;
    }
    return this.expression(node);
  }

  functionBody(header, fn, isMethod = false) {
    const params = (fn.params || []).slice();
    if (isMethod && params[0] === 'self') params.shift();
    if (fn.isVararg) params.push('...');
    this.push(`${header}(${params.join(', ')})`);
    this.indented(() => this.block(fn.body));
    this.push('end');
  }

  expressionList(nodes) {
    return nodes.map((node) => this.expression(node)).join(', ');
  }

  static printsParens(node) {
    const inner = node.expression;
    return !!inner && (inner.kind === Kind.Call || inner.kind === Kind.MethodCall
      || inner.kind === Kind.Vararg);
  }

  static precedenceOf(node) {
    if (node.kind === Kind.Paren) {
      if (Printer.printsParens(node)) return F.ATOM_PREC;
      return Printer.precedenceOf(node.expression || node);
    }
    if (node.kind === Kind.Binary) {
      const info = F.BINARY[node.operator];
      return info ? info[0] : 0;
    }
    if (node.kind === Kind.Unary) return F.UNARY_PREC;
    return F.ATOM_PREC;
  }

  expression(node) {
    if (!node) return 'nil';
    switch (node.kind) {
      case Kind.Nil: return 'nil';
      case Kind.True: return 'true';
      case Kind.False: return 'false';
      case Kind.Vararg: return '...';
      case Kind.Number: return F.formatNumber(node.value);
      case Kind.String: return F.formatString(node.value);
      case Kind.Name: return node.name;
      case Kind.Function: return this.functionExpression(node);
      case Kind.Table: return this.tableExpression(node);
      case Kind.Binary: return this.binaryExpression(node);
      case Kind.Unary: return this.unaryExpression(node);
      case Kind.Index: return this.indexExpression(node);
      case Kind.Call: {
        const base = this.prefix(node.base);
        return base + this.from(this.column + base.length, () => this.arguments(node.args));
      }
      case Kind.MethodCall: {
        const head = `${this.prefix(node.base)}:${node.method}`;
        return head + this.from(this.column + head.length, () => this.arguments(node.args));
      }
      case Kind.Paren:
        if (Printer.printsParens(node)) return `(${this.expression(node.expression)})`;
        return this.expression(node.expression);
      default: return `--[[ ${node.kind} ]]nil`;
    }
  }

  operand(node, minPrecedence, side, assoc) {
    const text = this.expression(node);
    const precedence = Printer.precedenceOf(node);
    let inner = node;
    while (inner.kind === Kind.Paren && !Printer.printsParens(inner)) {
      inner = inner.expression;
    }
    let needs = precedence < minPrecedence;
    if (precedence === minPrecedence && inner.kind === Kind.Binary && !FLAT.has(inner.operator)) {
      if (side === 'left' && assoc === 'right') needs = true;
      if (side === 'right' && assoc === 'left') needs = true;
    }

    return needs ? `(${text})` : text;
  }

  binaryExpression(node) {
    const info = F.BINARY[node.operator] || [0, 'left'];
    const [precedence, assoc] = info;
    const parts = [];
    this.chain(node, node.operator, assoc, parts);
    const flat = this.packed(() => this.operands(this, parts, precedence, assoc)
      .join(` ${node.operator} `));
    if (this.tight || flat.includes('\n') || this.fits(flat)) return flat;
    return this.spread(parts, node.operator, precedence, assoc);
  }

  chain(node, operator, assoc, parts) {
    let inner = node;
    while (inner.kind === Kind.Paren && !Printer.printsParens(inner)) inner = inner.expression;
    if (inner.kind !== Kind.Binary || inner.operator !== operator) {
      parts.push(node);
      return;
    }
    const both = FLAT.has(operator);
    if (both || assoc === 'left') this.chain(inner.lhs, operator, assoc, parts);
    else parts.push(inner.lhs);
    if (both || assoc === 'right') this.chain(inner.rhs, operator, assoc, parts);
    else parts.push(inner.rhs);
  }

  operands(printer, parts, precedence, assoc, columnAt) {
    const last = parts.length - 1;
    const leftmost = assoc === 'right' ? (at) => at !== last : (at) => at === 0;
    return parts.map((part, at) => {
      const side = leftmost(at) ? 'left' : 'right';
      const print = () => printer.operand(part, precedence, side, assoc);
      return columnAt ? printer.from(columnAt(at), print) : print();
    });
  }

  spread(parts, operator, precedence, assoc) {
    const sub = this.inner();
    const indent = this.options.indent.repeat(sub.depth);
    const head = `${operator} `;
    const texts = this.operands(sub, parts, precedence, assoc,
      (at) => (at === 0 ? this.column : indent.length + head.length))
      .map((text, at) => (at === 0 ? text : `${head}${text}`));
    const wide = texts.some((text) => text.includes('\n'));
    const rows = [];
    let row = texts[0];
    let start = this.column;
    for (let at = 1; at < texts.length; at += 1) {
      const joined = `${row} ${texts[at]}`;
      if (!wide && start + joined.length <= this.options.maxInlineWidth) {
        row = joined;
      } else {
        rows.push(row);
        row = texts[at];
        start = indent.length;
      }
    }
    rows.push(row);
    return rows.join(`\n${indent}`);
  }

  unaryExpression(node) {
    const text = this.operand(node.argument, F.UNARY_PREC, 'right', 'right');
    if (node.operator === 'not') return `not ${text}`;
    const separator = node.operator === '-' && text.startsWith('-') ? ' ' : '';
    return `${node.operator}${separator}${text}`;
  }

  prefix(node) {
    if (node.kind === Kind.Paren) {
      const inner = node.expression;
      if (inner && (inner.kind === Kind.Name || inner.kind === Kind.Index)) {
        return this.prefix(inner);
      }
      return `(${this.expression(inner)})`;
    }
    const text = this.expression(node);
    if (F.PREFIXES.has(node.kind)) return text;
    return `(${text})`;
  }

  indexExpression(node) {
    const key = node.index;
    if (key && key.kind === Kind.String && F.isIdentifier(key.value)) {
      return `${this.prefix(node.base)}.${key.value}`;
    }
    return `${this.prefix(node.base)}[${this.expression(key)}]`;
  }

  arguments(args) {
    const list = args || [];
    if (!list.length) return '()';
    const flat = `(${this.expressionList(list)})`;
    if (list.length < 2 || flat.includes('\n') || this.fits(flat)) return flat;
    const hugged = this.hug(list);
    if (hugged) return hugged;
    const sub = this.inner();
    const indent = this.options.indent.repeat(sub.depth);
    const items = list.map((node) => ({ text: sub.expression(node), alone: false }));
    const closing = this.options.indent.repeat(this.depth);
    return `(\n${this.filled(items, indent, '').join('\n')}\n${closing})`;
  }

  hug(list) {
    const last = list[list.length - 1];
    if (last.kind !== Kind.Table && last.kind !== Kind.Function) return null;
    const head = `(${this.expressionList(list.slice(0, -1))}, `;
    const start = this.column + head.length;
    if (head.includes('\n') || start > this.options.maxInlineWidth) return null;
    return `${head}${this.from(start, () => this.expression(last))})`;
  }

  functionExpression(fn) {
    const params = (fn.params || []).slice();
    if (fn.isVararg) params.push('...');
    const head = `function(${params.join(', ')})`;
    const sub = this.inner();
    sub.block(fn.body);
    if (sub.lines.length < 2) {
      const only = sub.lines.length ? sub.lines[0].trim() : '';
      const flat = only ? `${head} ${only} end` : `${head} end`;
      if (this.fits(flat)) return flat;
    }
    const closing = this.options.indent.repeat(this.depth);
    const body = sub.lines.length ? `\n${sub.lines.join('\n')}` : '';
    return `${head}${body}\n${closing}end`;
  }

  filled(items, indent, tail = ',') {
    const rows = [];
    let row = '';
    const commit = () => {
      if (row) rows.push(row);
      row = '';
    };
    items.forEach((item, at) => {
      const comma = at === items.length - 1 ? tail : ',';
      const own = `${indent}${item.text}${comma}`;
      const joined = row ? `${row} ${item.text}${comma}` : own;
      if (item.alone) {
        commit();
        rows.push(own);
      } else if (row && joined.length > this.options.maxInlineWidth) {
        commit();
        row = own;
      } else {
        row = joined;
      }
    });
    commit();
    return rows;
  }

  tableExpression(node) {
    const entries = node.entries || [];
    if (entries.length === 0) return '{}';
    const inline = entries.map((entry) => this.tableEntry(entry, false));
    const flat = `{ ${inline.join(', ')} }`;
    if (!layout.record(entries) && this.fits(flat)) return flat;
    const sub = this.inner();
    const items = entries.map((entry) => {
      const text = sub.tableEntry(entry, true);
      return { text, alone: entry.type === 'key' || text.includes('\n') };
    });
    const indent = this.options.indent.repeat(sub.depth);
    const closing = this.options.indent.repeat(this.depth);
    return `{\n${this.filled(items, indent).join('\n')}\n${closing}}`;
  }

  tableEntry(entry) {
    if (entry.type === 'key') {
      const key = entry.key;
      const head = key.kind === Kind.String && F.isIdentifier(key.value)
        ? `${key.value} = `
        : `[${this.expression(key)}] = `;
      return this.after(head, () => this.expression(entry.value));
    }
    return this.expression(entry.value);
  }
}

function unparse(node, options) {
  const printer = new Printer(options);
  if (!node) return '';
  if (node.kind === Kind.Chunk) printer.block(node.body);
  else if (node.kind === Kind.Block) printer.block(node);
  else if (node.kind && require('./ast').isExpression(node)) return printer.expression(node);
  else printer.statement(node);
  return printer.toString();
}

module.exports = { unparse };
