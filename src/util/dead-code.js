'use strict';

const { Kind } = require('../lua/ast');
const { children } = require('../lua/walk');
const purity = require('./purity');
const { throughBindings } = purity;
const { isLocalBinding } = require('../lua/scope');

function ownedBlocks(statement) {
  const blocks = [];
  const add = (block, role) => { if (block) blocks.push({ block, role }); };
  switch (statement.kind) {
    case Kind.Do:
      add(statement.body, 'plain');
      break;
    case Kind.While: case Kind.NumericFor: case Kind.GenericFor:
      add(statement.body, 'loop');
      break;
    case Kind.Repeat:
      add(statement.body, 'loop');
      break;
    case Kind.If:
      add(statement.body, 'plain');
      for (const clause of statement.elseIfs || []) add(clause.body, 'plain');
      add(statement.elseBody, 'plain');
      break;
    case Kind.LocalFunction: case Kind.FunctionDeclaration:
      add(statement.body && statement.body.body, 'function');
      break;
    default:
      break;
  }
  return blocks;
}

class Shape {
  constructor(root, facts = null) {
    this.facts = facts;
    this.holder = new Map();
    this.owner = new Map();
    this.role = new Map();
    this.stmtOf = new Map();
    this.declarer = new Map();
    this.mutations = new Map();
    this.reads = new Set();
    this.blocks = [];
    const body = root.kind === Kind.Chunk ? root.body : root;
    this.enter(body, 'chunk');
    this.indexReads();
  }

  indexReads() {
    const seen = new Set();
    for (const node of this.stmtOf.keys()) {
      if (node.kind !== Kind.Name || !node.binding || seen.has(node.binding)) continue;
      seen.add(node.binding);
      for (const read of node.binding.reads || []) this.reads.add(read);
    }
  }

  enter(block, role) {
    if (!block || !block.statements) return;
    this.blocks.push(block);
    this.role.set(block, role);
    for (const statement of block.statements) {
      this.holder.set(statement, block);
      this.declare(statement);
      this.charge(statement);
      this.claim(statement, statement);
    }
  }

  charge(statement) {
    const blame = (binding) => {
      if (!this.mutations.has(binding)) this.mutations.set(binding, []);
      this.mutations.get(binding).push(statement);
    };
    const note = (node) => {
      for (const binding of throughBindings(node, this.facts)) blame(binding);
    };
    for (const target of statement.targets || []) {
      if (target && target.kind !== Kind.Name) note(target);
    }
    for (const node of this.own(statement)) {
      if (node.kind !== Kind.Call && node.kind !== Kind.MethodCall) continue;

      if (node.kind === Kind.MethodCall || (node.base && node.base.kind !== Kind.Name)) {
        note(node.base);
      }
      for (const argument of node.args || []) note(argument);
      if (!this.facts) continue;
      const cells = purity.writesOutside(node, this.facts);
      if (cells) for (const binding of cells) blame(binding);
    }
  }

  declare(statement) {
    const note = (binding) => { if (binding) this.declarer.set(binding, statement); };
    if (statement.kind === Kind.LocalDeclaration) (statement.bindings || []).forEach(note);
    else if (statement.kind === Kind.LocalFunction) note(statement.binding);
    else if (statement.kind === Kind.NumericFor) note(statement.binding);
    else if (statement.kind === Kind.GenericFor) (statement.bindings || []).forEach(note);
  }

  claim(node, statement) {
    this.stmtOf.set(node, statement);
    for (const child of children(node)) {
      const inner = child.node;
      if (!inner || !inner.kind) continue;
      if (inner.kind === Kind.Block) {
        this.owner.set(inner, statement);
        const role = child.parent && child.parent.kind === Kind.Function ? 'function'
          : (ownedBlocks(statement).find((entry) => entry.block === inner) || {}).role || 'plain';
        this.enter(inner, role);
      } else {
        if (inner.kind === Kind.Function) {
          for (const binding of inner.bindings || []) this.declarer.set(binding, statement);
        }
        this.claim(inner, statement);
      }
    }
  }

  * own(statement) {
    const stack = [statement];
    while (stack.length) {
      const node = stack.pop();
      yield node;
      for (const child of children(node)) {
        if (child.node && child.node.kind && child.node.kind !== Kind.Block) {
          stack.push(child.node);
        }
      }
    }
  }
}

function ownExpressions(statement) {
  switch (statement.kind) {
    case Kind.LocalDeclaration: case Kind.Return: case Kind.GenericFor:
      return statement.expressions || [];
    case Kind.Assignment:
      return statement.expressions || [];
    case Kind.CallStatement:
      return [statement.expression];
    case Kind.While: case Kind.Repeat:
      return [statement.condition];
    case Kind.NumericFor:
      return [statement.start, statement.limit, statement.step];
    case Kind.If:
      return [statement.condition, ...(statement.elseIfs || []).map((c) => c.condition)];
    default:
      return [];
  }
}

function endsFunction(shape, statement) {
  let node = statement;
  for (let guard = 0; guard < 1000; guard += 1) {
    const block = shape.holder.get(node);
    if (!block) return false;
    const statements = block.statements || [];
    if (statements[statements.length - 1] !== node) return false;
    const role = shape.role.get(block);
    if (role === 'function') return true;
    if (role !== 'plain') return false;
    const owner = shape.owner.get(block);
    if (!owner || owner === node) return false;
    node = owner;
  }
  return false;
}

function tailReturns(shape, body) {
  const found = [];
  const visit = (block) => {
    const statements = (block && block.statements) || [];
    const last = statements[statements.length - 1];
    if (!last) return;
    if (last.kind === Kind.Return) {
      found.push(last);
      return;
    }
    if (last.kind !== Kind.If && last.kind !== Kind.Do) return;
    for (const entry of ownedBlocks(last)) visit(entry.block);
  };
  visit(body);
  return found;
}

function seeds(shape, facts) {
  const found = [];
  for (const block of shape.blocks) {
    block.statements.forEach((statement) => {
      switch (statement.kind) {
        case Kind.Goto: case Kind.Label: case Kind.FunctionDeclaration:
          found.push(statement);
          return;
        case Kind.Return:
          if (!endsFunction(shape, statement)) {
            found.push(statement);
            return;
          }
          break;
        case Kind.Break: case Kind.Continue:
          return;
        default:
          break;
      }
      if (statement.kind === Kind.Assignment) {
        if ((statement.targets || []).some((target) => !purity.targetWrites(target, facts))) {
          found.push(statement);
          return;
        }
      }
      for (const expression of ownExpressions(statement)) {
        if (expression && !purity.writesOutside(expression, facts)) {
          found.push(statement);
          return;
        }
      }

      for (const target of statement.targets || []) {
        if (target && target.kind === Kind.Index
          && !purity.isRemovable(target, facts)) found.push(statement);
      }
    });
  }
  return found;
}

function readsOf(shape, statement) {
  const bindings = new Set();
  for (const node of shape.own(statement)) {
    if (node.kind !== Kind.Name || !node.binding) continue;
    if (!isLocalBinding(node.binding)) continue;
    if (!shape.reads.has(node)) continue;
    bindings.add(node.binding);
  }
  return bindings;
}

function removeDead(root, facts) {
  const shape = new Shape(root, facts);
  const live = new Set();
  const needed = new Set();
  const queue = [];

  const mark = (statement) => {
    if (!statement || live.has(statement)) return;
    live.add(statement);
    queue.push(statement);
  };
  const want = (binding) => {
    if (!binding || needed.has(binding) || !isLocalBinding(binding)) return;
    needed.add(binding);
    for (const write of binding.writes || []) mark(shape.stmtOf.get(write));
    for (const statement of shape.mutations.get(binding) || []) mark(statement);
    mark(shape.declarer.get(binding));
  };

  const keepJumps = (block) => {
    for (const statement of block.statements) {
      if (statement.kind === Kind.Break || statement.kind === Kind.Continue) mark(statement);
      if (statement.kind === Kind.If || statement.kind === Kind.Do) {
        for (const entry of ownedBlocks(statement)) keepJumps(entry.block);
      }
    }
  };

  for (const statement of seeds(shape, facts)) mark(statement);

  while (queue.length) {
    const statement = queue.pop();
    for (const binding of readsOf(shape, statement)) want(binding);

    let block = shape.holder.get(statement);
    while (block) {
      const owner = shape.owner.get(block);
      if (!owner) break;
      mark(owner);
      block = shape.holder.get(owner);
    }
    for (const entry of ownedBlocks(statement)) {
      if (entry.role === 'loop') keepJumps(entry.block);
    }

    for (const node of shape.own(statement)) {
      if (node.kind !== Kind.Function) continue;
      const body = node.body;
      if (!body || !body.statements.length) continue;
      for (const tail of tailReturns(shape, body)) mark(tail);
    }
  }

  let removed = 0;
  for (const block of shape.blocks) {
    const before = block.statements.length;
    block.statements = block.statements.filter((statement) => live.has(statement));
    removed += before - block.statements.length;
  }
  return removed;
}

module.exports = { removeDead, seeds };
