'use strict';

const { Kind } = require('../lua/ast');
const { walk } = require('../lua/walk');
const { unparen, bindingOf } = require('./detect');
const { extractLeaves, assignIds } = require('./blocks');
const { buildBlock, terminator } = require('./ir');

function closureSites(vm) {
  const sites = new Map();
  walk(vm.container.fn, {
    enter: (node) => {
      if (node.kind !== Kind.Call) return undefined;
      const creator = vm.creatorFor
        ? vm.creatorFor(node.base)
        : vm.creators.get(bindingOf(node.base));
      if (!creator) return undefined;
      const first = unparen(node.args[0]);
      if (!first || first.kind !== Kind.Number) return undefined;
      const existing = sites.get(first.value);
      const site = {
        blockId: first.value,
        creator,
        arity: creator.arity,
        vararg: creator.vararg,
        upvalsExpression: node.args[1] || null,
        call: node,
      };
      if (existing) existing.push(site);
      else sites.set(first.value, [site]);
      return undefined;
    },
  });
  return sites;
}

function successorIds(term) {
  if (term.kind === 'goto') return [term.target];
  if (term.kind === 'branch') {
    return term.whenFalse === null ? [term.whenTrue] : [term.whenTrue, term.whenFalse];
  }
  return [];
}

function buildGraph(vm) {
  const leaves = extractLeaves(vm);
  const built = leaves.map((leaf) => {
    const block = buildBlock(vm, leaf);
    block.terminator = terminator(block);
    return block;
  });

  const sites = closureSites(vm);
  const ids = new Set([vm.entry.blockId]);
  for (const id of sites.keys()) ids.add(id);
  for (const block of built) for (const id of successorIds(block.terminator)) ids.add(id);

  const assigned = assignIds(leaves, [...ids].sort((a, b) => a - b));
  const nodes = new Map();
  for (const block of built) {
    if (block.leaf.id === null) continue;
    block.id = block.leaf.id;
    block.successors = [];
    block.predecessors = [];
    nodes.set(block.id, block);
  }
  const missing = [];
  for (const block of nodes.values()) {
    for (const id of successorIds(block.terminator)) {
      const target = nodes.get(id);
      if (!target) {
        missing.push({ from: block.id, to: id });
        continue;
      }
      block.successors.push(target);
      target.predecessors.push(block);
    }
  }

  return {
    vm,
    blocks: nodes,
    sites,
    dead: assigned.dead,
    conflicts: assigned.conflicts,
    missing,
    unsupported: built.filter((block) => block.unsupported.length),
    unknown: [...nodes.values()].filter((block) => block.terminator.kind === 'unknown'),
  };
}

function reachable(graph, entryId, stops) {
  const seen = new Set();
  const order = [];
  const entry = graph.blocks.get(entryId);
  if (!entry) return { seen, order };
  const queue = [entry];
  seen.add(entry.id);
  while (queue.length) {
    const block = queue.shift();
    order.push(block);
    for (const next of block.successors) {
      if (seen.has(next.id)) continue;
      if (stops.has(next.id) && next.id !== entryId) continue;
      seen.add(next.id);
      queue.push(next);
    }
  }
  return { seen, order };
}

function reversePostorder(entry, members) {
  const visited = new Set();
  const post = [];
  const stack = [{ block: entry, index: 0 }];
  visited.add(entry.id);
  while (stack.length) {
    const frame = stack[stack.length - 1];
    if (frame.index < frame.block.successors.length) {
      const next = frame.block.successors[frame.index];
      frame.index += 1;
      if (!visited.has(next.id) && members.has(next.id)) {
        visited.add(next.id);
        stack.push({ block: next, index: 0 });
      }
      continue;
    }
    post.push(frame.block);
    stack.pop();
  }
  return post.reverse();
}

function sameSet(a, b) {
  if (a.size !== b.size) return false;
  for (const key of a) if (!b.has(key)) return false;
  return true;
}

function solveLiveness(fn, posKey) {
  for (const block of fn.blocks) {
    block.use = new Set([...block.liveIn].filter((key) => key !== posKey));
    block.def = new Set([...block.written].filter((key) => key !== posKey));
    block.liveInRegs = new Set(block.use);
    block.liveOutRegs = new Set();
  }
  const order = [...fn.blocks].reverse();
  for (let round = 0; round < 10000; round += 1) {
    let changed = false;
    for (const block of order) {
      const out = new Set();
      for (const next of block.successors) {
        if (!fn.members.has(next.id)) continue;
        for (const key of next.liveInRegs) out.add(key);
      }
      const inSet = new Set(block.use);
      for (const key of out) if (!block.def.has(key)) inSet.add(key);
      if (!sameSet(out, block.liveOutRegs) || !sameSet(inSet, block.liveInRegs)) changed = true;
      block.liveOutRegs = out;
      block.liveInRegs = inSet;
    }
    if (!changed) break;
  }
}

function buildCfg(vm) {
  const graph = buildGraph(vm);
  const entryIds = new Set([vm.entry.blockId, ...graph.sites.keys()]);

  const descriptors = [];
  descriptors.push({
    id: vm.entry.blockId,
    kind: 'main',
    arity: vm.entry.arity,
    vararg: vm.entry.vararg,
    site: null,
  });
  for (const [id, sites] of graph.sites) {
    if (id === vm.entry.blockId) continue;
    const site = sites[0];
    descriptors.push({
      id, kind: 'closure', arity: site.arity, vararg: site.vararg, site, sites,
    });
  }

  const functions = [];
  const owner = new Map();
  const shared = [];
  for (const descriptor of descriptors) {
    const entry = graph.blocks.get(descriptor.id);
    if (!entry) {
      graph.missing.push({ from: null, to: descriptor.id });
      continue;
    }
    const { seen } = reachable(graph, descriptor.id, entryIds);
    const fn = {
      ...descriptor,
      entry,
      members: seen,
      blocks: reversePostorder(entry, seen),
    };
    for (const id of seen) {
      const previous = owner.get(id);
      if (previous !== undefined && previous !== descriptor.id) {
        shared.push({ block: id, functions: [previous, descriptor.id] });
        continue;
      }
      owner.set(id, descriptor.id);
    }
    solveLiveness(fn, vm.posKey);
    functions.push(fn);
  }

  const orphans = [...graph.blocks.keys()].filter((id) => !owner.has(id));
  return { ...graph, functions, owner, shared, orphans };
}

module.exports = { reversePostorder, buildCfg };
