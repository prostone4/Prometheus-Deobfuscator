'use strict';

const { Kind, isMultiValue } = require('../lua/ast');
const { walk, transform } = require('../lua/walk');
const { isLocalBinding } = require('../lua/scope');
const { parentTable } = require('./copies');
const { spoken, fresh } = require('./hoist');

const SLOTS = 8;

function slotOf(node) {
  if (!node || node.kind !== Kind.Number) return 0;
  const value = node.value;
  if (typeof value !== 'number' || !Number.isInteger(value) || value < 1) return 0;
  return value;
}

function packedCall(expression) {
  if (!expression || expression.kind !== Kind.Table) return null;
  const entries = expression.entries || [];
  if (entries.length !== 1 || entries[0].type !== 'item') return null;
  const value = entries[0].value;
  return isMultiValue(value) ? value : null;
}

function slotsRead(parents, binding) {
  const found = new Map();
  for (const read of binding.reads || []) {
    const index = parents.get(read);
    if (!index || index.kind !== Kind.Index || index.base !== read) return null;
    const slot = slotOf(index.index);
    if (!slot || slot > SLOTS) return null;
    const holder = parents.get(index);
    if (holder && holder.kind === Kind.Assignment
      && (holder.targets || []).indexOf(index) >= 0) return null;
    found.set(index, slot);
  }
  return found.size ? found : null;
}

function packed(chunk, parents) {
  const plans = [];
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.LocalDeclaration) return undefined;
      if ((node.names || []).length !== 1 || (node.expressions || []).length !== 1) return undefined;
      const call = packedCall(node.expressions[0]);
      if (!call) return undefined;
      const binding = (node.bindings || [])[0];
      if (!isLocalBinding(binding) || (binding.writes || []).length) return undefined;
      const reads = slotsRead(parents, binding);
      if (!reads) return undefined;
      const wanted = new Set(reads.values());
      const highest = Math.max(...wanted);
      if (wanted.size !== highest) return undefined;
      plans.push({ declaration: node, call, reads, highest });
      return undefined;
    },
  });
  return plans;
}

function nameResults(chunk) {
  const parents = parentTable(chunk);
  const plans = packed(chunk, parents);
  if (!plans.length) return 0;
  const taken = spoken(chunk);
  const swaps = new Map();
  let named = 0;
  for (const plan of plans) {
    const names = [plan.declaration.names[0]];
    for (let slot = 2; slot <= plan.highest; slot += 1) names.push(fresh(taken, 'v'));
    for (const [index, slot] of plan.reads) {
      swaps.set(index, { kind: Kind.Name, name: names[slot - 1] });
    }
    plan.declaration.names = names;
    plan.declaration.bindings = [];
    plan.declaration.expressions = [plan.call];
    named += 1;
  }
  transform(chunk, (node) => swaps.get(node) || node);
  return named;
}

module.exports = { packed, nameResults };
