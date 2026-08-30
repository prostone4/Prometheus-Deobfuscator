'use strict';

const { Kind } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');
const { bare } = require('../util/flow');

function quiet(node) {
  if (!node) return true;
  switch (node.kind) {
    case Kind.Nil:
    case Kind.True:
    case Kind.False:
    case Kind.Number:
    case Kind.String:
    case Kind.Vararg:
    case Kind.Name:
    case Kind.Function:
      return true;
    case Kind.Paren:
      return quiet(node.expression);
    case Kind.Table:
      return (node.entries || []).every((entry) => (entry.type !== 'key' || quiet(entry.key))
        && quiet(entry.value));
    default:
      return false;
  }
}

function holds(root, wanted) {
  return collect(root, (node) => node === wanted).length > 0;
}

function storeSites(root) {
  const stores = new Set();
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Assignment) return undefined;
      for (const target of node.targets || []) {
        const site = bare(target);
        if (site && site.kind === Kind.Index) stores.add(site);
      }
      return undefined;
    },
  });
  return stores;
}

function evaluatedBefore(statement, target) {
  const stores = storeSites(statement);
  const before = [];
  const ancestors = [];
  let reached = false;
  walk(statement, {
    enter(node) {
      if (reached) return false;
      if (node === target) {
        reached = true;
        for (const ancestor of ancestors) {
          const at = before.indexOf(ancestor);
          if (at >= 0) before.splice(at, 1);
        }
        return false;
      }
      if (!stores.has(node)) before.push(node);
      if (node.kind === Kind.Function && !holds(node, target)) return false;
      ancestors.push(node);
      return undefined;
    },
    leave(node) {
      if (!reached && ancestors[ancestors.length - 1] === node) ancestors.pop();
    },
  });
  return reached ? before : null;
}

function reachesQuietly(statement, target) {
  const before = evaluatedBefore(statement, target);
  if (!before) return false;
  return before.every((node) => quiet(node));
}

function readsWithin(root) {
  const found = new Set();
  const stored = new Set();
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        for (const target of node.targets || []) {
          const named = bare(target);
          if (named && named.kind === Kind.Name) stored.add(named);
        }
      }
      if (node.kind === Kind.Name && node.binding && !stored.has(node)) found.add(node.binding);
      return undefined;
    },
  });
  return found;
}

function nameCounts(root) {
  const counts = new Map();
  const seen = new Set();
  const note = (binding, text) => {
    if (!binding || seen.has(binding)) return;
    seen.add(binding);
    counts.set(text, (counts.get(text) || 0) + 1);
  };
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Function) {
        (node.bindings || []).forEach((binding, at) => note(binding, (node.params || [])[at]));
      } else if (node.kind === Kind.LocalDeclaration) {
        (node.bindings || []).forEach((binding, at) => note(binding, (node.names || [])[at]));
      } else if (node.kind === Kind.LocalFunction) {
        note(node.binding, node.name);
      } else if (node.kind === Kind.NumericFor) {
        note(node.binding, node.variable);
      } else if (node.kind === Kind.GenericFor) {
        (node.bindings || []).forEach((binding, at) => note(binding, (node.variables || [])[at]));
      }
      return undefined;
    },
  });
  return counts;
}

function unshadowed(counts, text) {
  return counts.get(text) === 1;
}

function plainWrite(statement) {
  if (!statement || statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  if (targets.length !== 1 || expressions.length !== 1) return null;
  const target = bare(targets[0]);
  if (!target || target.kind !== Kind.Name || !target.binding) return null;
  return { target, value: expressions[0] };
}

function plainDeclaration(statement) {
  if (!statement || statement.kind !== Kind.LocalDeclaration) return null;
  const names = statement.names || [];
  const expressions = statement.expressions || [];
  if (names.length !== 1 || expressions.length !== 1) return null;
  const binding = (statement.bindings || [])[0];
  if (!binding) return null;
  return { binding, name: names[0], value: expressions[0] };
}

function isEmptyDo(statement) {
  if (!statement || statement.kind !== Kind.Do) return false;
  return !((statement.body && statement.body.statements) || []).length;
}

module.exports = {
  quiet,
  reachesQuietly,
  readsWithin,
  nameCounts,
  unshadowed,
  plainWrite,
  plainDeclaration,
  isEmptyDo,
};
