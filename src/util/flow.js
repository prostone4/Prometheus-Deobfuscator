'use strict';

const { Kind } = require('../lua/ast');
const { walk } = require('../lua/walk');

const EXIT = new Set(['error']);

const TRUTHY = new Set([Kind.True, Kind.Number, Kind.String, Kind.Table, Kind.Function]);

function isAlwaysTrue(node) {
  if (!node) return false;
  if (node.kind === Kind.Paren) return isAlwaysTrue(node.expression);
  return TRUTHY.has(node.kind);
}

function bare(node) {
  let current = node;
  while (current && current.kind === Kind.Paren) current = current.expression;
  return current;
}

function hasEscape(body) {
  let found = false;
  walk(body, {
    enter(node) {
      if (found) return false;
      if (node.kind === Kind.Function) return false;
      if (node.kind === Kind.While || node.kind === Kind.Repeat
        || node.kind === Kind.NumericFor || node.kind === Kind.GenericFor) {
        let inner = false;
        walk(node.body, {
          enter(child) {
            if (child.kind === Kind.Function) return false;
            if (child.kind === Kind.Return || child.kind === Kind.Goto) inner = true;
            return undefined;
          },
        });
        if (inner) found = true;
        return false;
      }
      if (node.kind === Kind.Break || node.kind === Kind.Return || node.kind === Kind.Goto) {
        found = true;
      }
      return undefined;
    },
  });
  return found;
}

function divergingCall(node, depth) {
  const call = bare(node);
  if (!call || call.kind !== Kind.Call) return false;
  const base = bare(call.base);
  if (!base) return false;
  if (base.kind === Kind.Name && !base.binding && EXIT.has(base.name)) return true;
  if (base.kind === Kind.Function) return divergesBlock(base.body, depth + 1);
  return false;
}

function diverges(statement, depth = 0) {
  if (!statement || depth > 48) return false;
  switch (statement.kind) {
    case Kind.While:
      return isAlwaysTrue(statement.condition) && !hasEscape(statement.body);
    case Kind.Repeat:
      return divergesBlock(statement.body, depth + 1)
        || (statement.condition && statement.condition.kind === Kind.False
          && !hasEscape(statement.body));
    case Kind.Do:
      return divergesBlock(statement.body, depth + 1);
    case Kind.Return:
      return (statement.expressions || []).length === 1
        && divergingCall(statement.expressions[0], depth);
    case Kind.CallStatement:
      return divergingCall(statement.expression, depth);
    case Kind.If: {
      if (!statement.elseBody) return false;
      if (!divergesBlock(statement.body, depth + 1)) return false;
      for (const clause of statement.elseIfs || []) {
        if (!divergesBlock(clause.body, depth + 1)) return false;
      }
      return divergesBlock(statement.elseBody, depth + 1);
    }
    default:
      return false;
  }
}

function divergesBlock(block, depth = 0) {
  if (!block || depth > 48) return false;
  return (block.statements || []).some((s) => diverges(s, depth + 1));
}

function soleValues(chunk) {
  const values = new Map();
  const rejected = new Set();

  const pair = (binding, list, index, assigned) => {
    if (!binding || binding.kind === 'global' || rejected.has(binding)) return;
    if (values.has(binding) || binding.writes.length !== (assigned ? 1 : 0)) {
      rejected.add(binding);
      values.delete(binding);
      return;
    }
    values.set(binding, { list, index });
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.LocalDeclaration) {
        const bindings = node.bindings || [];
        const expressions = node.expressions || [];
        if (bindings.length === expressions.length) {
          bindings.forEach((binding, i) => pair(binding, expressions, i, false));
        }
        return undefined;
      }
      if (node.kind === Kind.LocalFunction && node.binding) {
        pair(node.binding, [node.body], 0, false);
        return undefined;
      }
      if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        if (targets.length === expressions.length) {
          targets.forEach((target, i) => {
            const inner = bare(target);
            if (inner && inner.kind === Kind.Name) pair(inner.binding, expressions, i, true);
          });
        }
      }
      return undefined;
    },
  });
  return values;
}

function copyRoots(values) {
  const roots = new Map();
  for (const binding of values.keys()) {
    let at = binding;
    const seen = new Set([binding]);
    for (;;) {
      const held = bare(soleValueOf(values, at));
      if (!held || held.kind !== Kind.Name || !held.binding) break;
      if (seen.has(held.binding)) break;
      seen.add(held.binding);
      at = held.binding;
    }
    if (at !== binding) roots.set(binding, at);
  }
  return roots;
}

function soleValueOf(values, binding) {
  const at = binding ? values.get(binding) : null;
  return at ? at.list[at.index] : null;
}
module.exports = {
  soleValues,
  soleValueOf,
  copyRoots,
  isAlwaysTrue,
  bare,
  hasEscape,
  diverges,
  divergesBlock,
};
