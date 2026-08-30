'use strict';

const { Kind } = require('./ast');

let bindingId = 0;

class Binding {
  constructor(name, kind, options = {}) {
    bindingId += 1;
    this.id = bindingId;
    this.name = name;
    this.kind = kind;
    this.declaration = options.declaration || null;
    this.functionDepth = options.functionDepth || 0;
    this.reads = [];
    this.writes = [];
    this.initializer = options.initializer || null;
    this.captured = false;
  }

  get writeCount() {
    return this.writes.length + (this.initializer ? 1 : 0);
  }

  get isSingleAssignment() {
    return this.writes.length === 0;
  }
}

class Scope {
  constructor(parent, functionDepth) {
    this.parent = parent;
    this.functionDepth = functionDepth;
    this.bindings = new Map();
  }

  declare(name, kind, options) {
    const binding = new Binding(name, kind, { ...options, functionDepth: this.functionDepth });
    this.bindings.set(name, binding);
    return binding;
  }

  lookup(name) {
    let scope = this;
    while (scope) {
      const binding = scope.bindings.get(name);
      if (binding) return binding;
      scope = scope.parent;
    }
    return null;
  }
}

class Resolver {
  constructor() {
    this.globals = new Map();
    this.allBindings = [];
    this.functionDepth = 0;
  }

  global(name) {
    let binding = this.globals.get(name);
    if (!binding) {
      binding = new Binding(name, 'global', {});
      this.globals.set(name, binding);
      this.allBindings.push(binding);
    }
    return binding;
  }

  declare(scope, name, kind, options) {
    const binding = scope.declare(name, kind, options);
    this.allBindings.push(binding);
    return binding;
  }

  reference(scope, node, mode) {
    const binding = scope.lookup(node.name) || this.global(node.name);
    node.binding = binding;
    if (binding.functionDepth !== undefined && binding.kind !== 'global'
      && binding.functionDepth < this.functionDepth) {
      binding.captured = true;
    }
    if (mode === 'write') binding.writes.push(node);
    else binding.reads.push(node);
    return binding;
  }

  block(node, parentScope) {
    const scope = new Scope(parentScope, this.functionDepth);
    node.scope = scope;
    for (const statement of node.statements) this.statement(statement, scope);
    return scope;
  }

  statement(node, scope) {
    switch (node.kind) {
      case Kind.LocalDeclaration: {
        for (const expression of node.expressions) this.expression(expression, scope);
        node.bindings = node.names.map((name) => this.declare(scope, name, 'local', {
          declaration: node,
          initializer: node,
        }));
        return;
      }
      case Kind.LocalFunction: {
        const binding = this.declare(scope, node.name, 'local', {
          declaration: node,
          initializer: node,
        });
        node.binding = binding;
        this.functionExpression(node.body, scope);
        return;
      }
      case Kind.FunctionDeclaration:
        this.expression(node.target, scope, 'write');
        this.functionExpression(node.body, scope);
        return;
      case Kind.Assignment:
        for (const expression of node.expressions) this.expression(expression, scope);
        for (const target of node.targets) this.expression(target, scope, 'write');
        return;
      case Kind.CallStatement:
        this.expression(node.expression, scope);
        return;
      case Kind.Return:
        for (const expression of node.expressions) this.expression(expression, scope);
        return;
      case Kind.Break:
      case Kind.Continue:
      case Kind.Goto:
      case Kind.Label:
        return;
      case Kind.Do:
        this.block(node.body, scope);
        return;
      case Kind.While:
        this.expression(node.condition, scope);
        this.block(node.body, scope);
        return;
      case Kind.Repeat: {
        const inner = new Scope(scope, this.functionDepth);
        node.body.scope = inner;
        for (const statement of node.body.statements) this.statement(statement, inner);
        this.expression(node.condition, inner);
        return;
      }
      case Kind.If: {
        this.expression(node.condition, scope);
        this.block(node.body, scope);
        for (const clause of node.elseIfs || []) {
          this.expression(clause.condition, scope);
          this.block(clause.body, scope);
        }
        if (node.elseBody) this.block(node.elseBody, scope);
        return;
      }
      case Kind.NumericFor: {
        this.expression(node.start, scope);
        this.expression(node.limit, scope);
        if (node.step) this.expression(node.step, scope);
        const inner = new Scope(scope, this.functionDepth);
        node.binding = this.declare(inner, node.variable, 'local', { declaration: node });
        node.body.scope = inner;
        for (const statement of node.body.statements) this.statement(statement, inner);
        return;
      }
      case Kind.GenericFor: {
        for (const expression of node.expressions) this.expression(expression, scope);
        const inner = new Scope(scope, this.functionDepth);
        node.bindings = node.variables.map(
          (name) => this.declare(inner, name, 'local', { declaration: node }),
        );
        node.body.scope = inner;
        for (const statement of node.body.statements) this.statement(statement, inner);
        return;
      }
      default:
        throw new Error(`unsupported statement: ${node.kind}`);
    }
  }

  functionExpression(node, scope) {
    this.functionDepth += 1;
    const inner = new Scope(scope, this.functionDepth);
    node.bindings = (node.params || []).map(
      (name) => this.declare(inner, name, 'param', { declaration: node }),
    );
    node.body.scope = inner;
    for (const statement of node.body.statements) this.statement(statement, inner);
    this.functionDepth -= 1;
  }

  expression(node, scope, mode = 'read') {
    if (!node) return;
    switch (node.kind) {
      case Kind.Name:
        this.reference(scope, node, mode);
        return;
      case Kind.Index:
        this.expression(node.base, scope);
        this.expression(node.index, scope);
        return;
      case Kind.Call:
        this.expression(node.base, scope);
        for (const arg of node.args) this.expression(arg, scope);
        return;
      case Kind.MethodCall:
        this.expression(node.base, scope);
        for (const arg of node.args) this.expression(arg, scope);
        return;
      case Kind.Function:
        this.functionExpression(node, scope);
        return;
      case Kind.Table:
        for (const entry of node.entries) {
          if (entry.key) this.expression(entry.key, scope);
          this.expression(entry.value, scope);
        }
        return;
      case Kind.Binary:
        this.expression(node.lhs, scope);
        this.expression(node.rhs, scope);
        return;
      case Kind.Unary:
        this.expression(node.argument, scope);
        return;
      case Kind.Paren:
        this.expression(node.expression, scope);
        return;
      default:
        return;
    }
  }
}

function resolve(chunk) {
  const resolver = new Resolver();
  const root = new Scope(null, 0);
  resolver.rootScope = root;
  const body = chunk.kind === Kind.Chunk ? chunk.body : chunk;
  resolver.block(body, root);
  return resolver;
}

function isGlobalName(node) {
  if (!node || node.kind !== Kind.Name) return false;
  return !node.binding || node.binding.kind === 'global';
}

function isLocalBinding(binding) {
  return !!binding && binding.kind !== 'global';
}

module.exports = { resolve, Scope, isGlobalName, isLocalBinding };
