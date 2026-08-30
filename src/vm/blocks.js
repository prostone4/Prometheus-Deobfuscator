'use strict';

const { Kind } = require('../lua/ast');
const { unparen, bindingOf } = require('./detect');

const FLIP = { '<': '>', '>': '<', '<=': '>=', '>=': '<=' };

function cutOf(condition, pos) {
  const node = unparen(condition);
  if (!node || node.kind !== Kind.Binary || !FLIP[node.operator]) return null;
  let operator = node.operator;
  let side = unparen(node.lhs);
  let bound = unparen(node.rhs);
  if (bindingOf(side) !== pos) {
    if (bindingOf(bound) !== pos) return null;
    operator = FLIP[operator];
    const swap = side;
    side = bound;
    bound = swap;
  }
  if (!bound || bound.kind !== Kind.Number) return null;
  if (operator === '<') return { lo: null, hi: bound.value };
  if (operator === '<=') return { lo: null, hi: bound.value + 1 };
  if (operator === '>') return { lo: bound.value + 1, hi: null };
  return { lo: bound.value, hi: null };
}

function extractLeaves(vm) {
  const leaves = [];
  const pos = vm.container.pos;

  const visit = (block, lo, hi) => {
    const statements = block.statements;
    if (statements.length === 1 && statements[0].kind === Kind.If && statements[0].elseBody) {
      const branch = statements[0];
      const clauses = [{ condition: branch.condition, body: branch.body }]
        .concat(branch.elseIfs || []);
      const cuts = clauses.map((clause) => cutOf(clause.condition, pos));
      if (cuts.every(Boolean)) {
        let low = lo;
        let high = hi;
        for (let i = 0; i < clauses.length; i += 1) {
          if (cuts[i].hi !== null) {
            visit(clauses[i].body, low, Math.min(high, cuts[i].hi));
            low = Math.max(low, cuts[i].hi);
          } else {
            visit(clauses[i].body, Math.max(low, cuts[i].lo), high);
            high = Math.min(high, cuts[i].lo);
          }
        }
        visit(branch.elseBody, low, high);
        return;
      }
    }
    leaves.push({ lo, hi, statements, id: null, index: leaves.length });
  };

  visit(vm.container.dispatch.body, -Infinity, Infinity);
  return leaves;
}

function jumpTargets(expression, out = new Set(), depth = 0) {
  const node = unparen(expression);
  if (!node || depth > 64) return out;
  if (node.kind === Kind.Number) {
    out.add(node.value);
    return out;
  }
  if (node.kind === Kind.Binary && node.operator === 'or') {
    jumpTargets(node.lhs, out, depth + 1);
    jumpTargets(node.rhs, out, depth + 1);
    return out;
  }
  if (node.kind === Kind.Binary && node.operator === 'and') {
    jumpTargets(node.rhs, out, depth + 1);
    return out;
  }
  return out;
}

function assignIds(leaves, ids) {
  const byId = new Map();
  const conflicts = [];
  for (const id of ids) {
    const leaf = leaves.find((candidate) => id >= candidate.lo && id < candidate.hi);
    if (!leaf) {
      conflicts.push({ id, reason: 'outside every interval' });
      continue;
    }
    if (leaf.id !== null) {
      conflicts.push({ id, reason: `interval already taken by ${leaf.id}` });
      continue;
    }
    leaf.id = id;
    byId.set(id, leaf);
  }
  const dead = leaves.filter((leaf) => leaf.id === null);
  return { byId, dead, conflicts };
}

module.exports = { extractLeaves, assignIds };
