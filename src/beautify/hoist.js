'use strict';

const { Kind, unparen } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');
const { isLocalBinding } = require('../lua/scope');
const { Positions } = require('../util/order');
const { visibleAt } = require('./copies');
const { hasLabel } = require('./declare');

function spoken(chunk) {
  const taken = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Name) taken.add(node.name);
      else if (node.kind === Kind.LocalFunction) taken.add(node.name);
      else if (node.kind === Kind.NumericFor) taken.add(node.variable);
      else if (node.kind === Kind.LocalDeclaration) {
        for (const one of node.names || []) taken.add(one);
      } else if (node.kind === Kind.GenericFor) {
        for (const one of node.variables || []) taken.add(one);
      } else if (node.kind === Kind.Function) {
        for (const one of node.params || []) taken.add(one);
      }
      return undefined;
    },
  });
  return taken;
}

function fresh(taken, stem = 'f') {
  for (let n = 1; ; n += 1) {
    const name = `${stem}${n}`;
    if (taken.has(name)) continue;
    taken.add(name);
    return name;
  }
}

function carries(fn, positions, host) {
  const inside = new Set(collect(fn, () => true));
  for (const node of collect(fn, (one) => one.kind === Kind.Name)) {
    const binding = node.binding;
    if (!isLocalBinding(binding)) continue;
    if (!binding.declaration || inside.has(binding.declaration)) continue;
    if (!visibleAt(positions, binding, host)) return false;
  }
  return true;
}

function calledWhereBuilt(chunk, positions) {
  const found = [];
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Call) return undefined;
      const base = unparen(node.base);
      if (!base || base.kind !== Kind.Function) return undefined;
      const spot = positions.path(node);
      if (!spot) return undefined;
      const { block, at } = spot;
      const host = (block.statements || [])[at];

      if (!host || hasLabel(block)) return undefined;
      if (!carries(base, positions, host)) return undefined;
      found.push({ block, host, call: node, fn: base });
      return undefined;
    },
  });
  return found;
}

function nameCalled(chunk) {
  const positions = new Positions(chunk);
  const plans = calledWhereBuilt(chunk, positions);
  if (!plans.length) return 0;
  const taken = spoken(chunk);
  const rows = new Map();
  for (const plan of plans) {
    if (!rows.has(plan.block)) rows.set(plan.block, new Map());
    const above = rows.get(plan.block);
    if (!above.has(plan.host)) above.set(plan.host, []);
    const name = fresh(taken);
    above.get(plan.host).push({ kind: Kind.LocalFunction, name, body: plan.fn });
    plan.call.base = { kind: Kind.Name, name };
  }
  let named = 0;
  for (const [block, above] of rows) {
    const kept = [];
    for (const statement of block.statements || []) {
      const added = above.get(statement);
      if (added) {
        kept.push(...added);
        named += added.length;
      }
      kept.push(statement);
    }
    block.statements = kept;
  }
  return named;
}

module.exports = { spoken, fresh, carries, nameCalled };
