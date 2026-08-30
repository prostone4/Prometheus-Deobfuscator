'use strict';

const A = require('../lua/ast');
const { Kind } = A;
const { walk } = require('../lua/walk');
const { hasEscape } = require('./flow');
const { readsIn, writesIn } = require('./eval');
const purity = require('./purity');
const { isLocalBinding } = require('../lua/scope');

function readsThrough(statement, summary) {
  const direct = readsIn(statement);
  const total = new Set(direct);
  for (const binding of direct) {
    for (const fn of summary.carriersOf(binding)) {
      for (const one of summary.allReadsOf(fn)) total.add(one);
    }
  }
  return total;
}

function hasOpaqueCall(statement, summary) {
  let opaque = false;
  walk(statement, {
    enter(node) {
      if (opaque) return false;
      if (node.kind === Kind.MethodCall) { opaque = true; return false; }
      if (node.kind !== Kind.Call) return undefined;
      let callee = node.base;
      while (callee && callee.kind === Kind.Paren) callee = callee.expression;
      if (!callee || callee.kind !== Kind.Name) { opaque = true; return false; }
      const binding = callee.binding;
      if (!binding) { opaque = true; return false; }
      if (summary.carriersOf(binding).size) return undefined;
      const assigned = (binding.writes || []).length > 0;
      if (isLocalBinding(binding) || assigned) opaque = true;
      return undefined;
    },
  });
  return opaque;
}

function killedBy(statement) {
  const killed = new Set();
  if (statement.kind !== Kind.Assignment) return killed;
  for (const target of statement.targets || []) {
    let node = target;
    while (node && node.kind === Kind.Paren) node = node.expression;
    if (node && node.kind === Kind.Name && node.binding) killed.add(node.binding);
  }
  return killed;
}

function survey(block, summary) {
  const reads = [];
  const kills = [];
  const walls = [];
  for (const statement of block.statements) {
    reads.push(readsThrough(statement, summary));
    kills.push(killedBy(statement));
    walls.push(hasEscape(statement) || hasOpaqueCall(statement, summary));
  }
  return { reads, kills, walls };
}

function isDeadStore(binding, at, info) {
  if (!isLocalBinding(binding)) return false;
  for (let j = at + 1; j < info.reads.length; j += 1) {
    if (info.reads[j].has(binding)) return false;
    if (info.walls[j]) return false;
    if (info.kills[j].has(binding)) return true;
  }
  return false;
}

function targetBinding(target) {
  let node = target;
  while (node && node.kind === Kind.Paren) node = node.expression;
  if (!node || node.kind !== Kind.Name) return null;
  return node.binding || null;
}

function rewrite(statement, dead, facts) {
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  const aligned = targets.length === expressions.length;
  if (dead.every((value) => value)) {
    if (expressions.every((expression) => purity.isSelfContained(expression, facts))) {
      return { statements: [], removed: targets.length };
    }
    if (expressions.length === 1
      && (expressions[0].kind === Kind.Call || expressions[0].kind === Kind.MethodCall)) {
      return { statements: [A.callStatement(expressions[0])], removed: targets.length };
    }
    return null;
  }
  if (!aligned) return null;
  const keep = [];
  let removed = 0;
  for (let i = 0; i < targets.length; i += 1) {
    if (dead[i] && purity.isSelfContained(expressions[i], facts)) removed += 1;
    else keep.push(i);
  }
  if (!removed) return null;
  statement.targets = keep.map((i) => targets[i]);
  statement.expressions = keep.map((i) => expressions[i]);
  return { statements: [statement], removed };
}

function hasLabel(block) {
  return block.statements.some((statement) => statement.kind === Kind.Label);
}

function removeStores(root, summary, facts) {
  let removed = 0;
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Block || hasLabel(node)) return undefined;
      const info = survey(node, summary);
      const out = [];
      for (let i = 0; i < node.statements.length; i += 1) {
        const statement = node.statements[i];
        if (statement.kind !== Kind.Assignment) { out.push(statement); continue; }
        const dead = (statement.targets || []).map((target) => {
          const binding = targetBinding(target);
          return !!binding && isDeadStore(binding, i, info);
        });
        if (!dead.some((value) => value)) { out.push(statement); continue; }
        const result = rewrite(statement, dead, facts);
        if (!result) { out.push(statement); continue; }
        removed += result.removed;
        out.push(...result.statements);
      }
      node.statements = out;
      return undefined;
    },
  });
  return removed;
}

function bareBindings(statement) {
  if (!statement || statement.kind !== Kind.LocalDeclaration) return [];

  if ((statement.expressions || []).length) return [];
  return (statement.bindings || []).filter(Boolean);
}

function stillNil(block, binding, at) {
  const statements = block.statements || [];
  for (let i = 0; i < at; i += 1) {
    if (!bareBindings(statements[i]).includes(binding)) continue;
    for (let j = i + 1; j < at; j += 1) {
      if (writesIn(statements[j], true).has(binding)) return false;
    }
    return true;
  }
  return false;
}

function removeRedundant(root) {
  let removed = 0;
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Block || hasLabel(node)) return undefined;
      const out = [];
      node.statements.forEach((statement, at) => {
        const targets = statement.kind === Kind.Assignment ? statement.targets || [] : [];
        const expressions = statement.expressions || [];
        if (!targets.length || targets.length !== expressions.length) {
          out.push(statement);
          return;
        }
        const seen = new Set();
        const keep = [];
        for (let i = 0; i < targets.length; i += 1) {
          const binding = targetBinding(targets[i]);
          const redundant = binding && isLocalBinding(binding) && !seen.has(binding)
            && expressions[i].kind === Kind.Nil && stillNil(node, binding, at);
          if (binding) seen.add(binding);
          if (redundant) removed += 1;
          else keep.push(i);
        }
        if (keep.length === targets.length) {
          out.push(statement);
          return;
        }
        if (!keep.length) return;
        statement.targets = keep.map((i) => targets[i]);
        statement.expressions = keep.map((i) => expressions[i]);
        out.push(statement);
      });
      node.statements = out;
      return undefined;
    },
  });
  return removed;
}

function neverRead(target) {
  if (!target || target.kind !== Kind.Name || !target.binding) return false;
  if (!isLocalBinding(target.binding)) return false;
  return !((target.binding.reads || []).length);
}

function discharge(chunk) {
  let changed = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      node.statements = node.statements.map((statement) => {
        if (statement.kind !== Kind.Assignment) return statement;
        const targets = statement.targets || [];
        const expressions = statement.expressions || [];
        if (!targets.length || expressions.length !== 1) return statement;
        if (!targets.every(neverRead)) return statement;
        const value = A.unparen(expressions[0]);
        if (value.kind !== Kind.Call && value.kind !== Kind.MethodCall) return statement;
        changed += 1;
        return A.callStatement(value);
      });
      return undefined;
    },
  });
  return changed;
}

module.exports = { removeStores, removeRedundant, discharge };
