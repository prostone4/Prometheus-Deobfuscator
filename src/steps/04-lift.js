'use strict';

const A = require('../lua/ast');
const { Kind } = A;
const { parentMap } = require('../vm/detect');
const { detect } = require('../vm/detect');
const { buildCfg } = require('../vm/cfg');
const { liftVm, resultList } = require('../vm/lift');

const fold = require('./02-fold');
const decrypt = require('./03-str');
const guards = require('./05-if');
const idioms = require('../vm/idioms');
const { discharge } = require('../util/dead-stores');
const { walk } = require('../lua/walk');

function varargsArg(vm) {
  const bindings = (vm.wrapper && vm.wrapper.bindings) || [];
  const slot = vm.roles.varargs ? bindings.indexOf(vm.roles.varargs) : -1;
  if (slot < 0) return null;
  return vm.wrapperCall.args[slot] || null;
}

const CARRIED = new Set([Kind.Name, Kind.Number, Kind.String, Kind.Nil, Kind.True, Kind.False]);

function copyPair(statement) {
  if (statement.kind === Kind.Assignment) {
    if (statement.targets.length !== 1 || statement.expressions.length !== 1) return null;
    const target = statement.targets[0];
    const source = A.unparen(statement.expressions[0]);
    if (target.kind !== Kind.Name || source.kind !== Kind.Name) return null;
    return { target: target.binding, source: source.binding, write: target };
  }
  if (statement.kind === Kind.LocalDeclaration) {
    if (statement.names.length !== 1 || statement.expressions.length !== 1) return null;
    const source = A.unparen(statement.expressions[0]);
    if (source.kind !== Kind.Name) return null;
    return { target: (statement.bindings || [])[0], source: source.binding, write: null };
  }
  return null;
}

function callValues(vm) {
  const values = new Map();
  const wrapper = vm.wrapper;
  if (!wrapper || !wrapper.body) return values;
  const args = vm.wrapperCall.args || [];
  const tail = args.length ? A.unparen(args[args.length - 1]) : null;
  const spread = tail ? A.isMultiValue(tail) : false;
  (wrapper.bindings || []).forEach((binding, slot) => {
    if (!binding || slot >= args.length) return;
    if (spread && slot === args.length - 1) return;
    const arg = A.unparen(args[slot]);
    if (CARRIED.has(arg.kind)) values.set(binding, arg);
  });
  for (let round = 0; round < 8; round += 1) {
    let added = 0;
    for (const statement of wrapper.body.statements) {
      const pair = copyPair(statement);
      if (!pair || !pair.target || values.has(pair.target)) continue;
      const value = values.get(pair.source);
      if (!value) continue;
      const writes = pair.target.writes || [];
      const once = pair.write ? writes.length === 1 && writes[0] === pair.write : !writes.length;
      if (!once) continue;
      values.set(pair.target, value);
      added += 1;
    }
    if (!added) break;
  }
  return values;
}

function become(node, value) {
  for (const key of Object.keys(node)) delete node[key];
  Object.assign(node, value.kind === Kind.Name ? A.name(value.name) : { ...value });
}

function wrapperDepth(vm) {
  let depth = null;
  for (const binding of (vm.wrapper && vm.wrapper.bindings) || []) {
    if (!binding) continue;
    const at = binding.functionDepth;
    depth = depth === null ? at : Math.max(depth, at);
  }
  return depth;
}

function reseat(context, vm, lifted) {
  const values = callValues(vm);
  const depth = wrapperDepth(vm);
  const sites = new Map();
  walk(lifted.body, {
    enter(node) {
      if (node.kind !== Kind.Name || !node.binding) return undefined;
      if (node.binding.kind === 'global') return undefined;
      const list = sites.get(node.binding);
      if (list) list.push(node);
      else sites.set(node.binding, [node]);
      return undefined;
    },
  });
  let moved = 0;
  for (const [binding, nodes] of sites) {
    const value = values.get(binding);
    if (value) {
      for (const node of nodes) become(node, value);
      moved += nodes.length;
      continue;
    }
    if (depth === null || binding.functionDepth < depth) continue;
    context.warn(`lift: carried-local ${binding.name}`);
    context.bump('lift.carried-local');
  }
  return moved;
}

function tailReturn(call, parents) {
  let node = call;
  for (let guard = 0; guard < 16; guard += 1) {
    const parent = parents.get(node);
    if (!parent) return null;
    if (parent.kind === Kind.Return) {
      return parent.expressions.length === 1 && parent.expressions[0] === node ? parent : null;
    }
    if (parent.kind === Kind.Paren) {
      node = parent;
      continue;
    }
    if (parent.kind === Kind.Table) {
      const entries = parent.entries || [];
      if (entries.length !== 1 || entries[0].type !== 'item' || entries[0].value !== node) {
        return null;
      }
      node = parent;
      continue;
    }
    if (parent.kind === Kind.Call && parent.base && parent.base.kind === Kind.Name
      && (parent.args || []).length === 1 && parent.args[0] === node) {
      node = parent;
      continue;
    }
    return null;
  }
  return null;
}

function replaceStatement(parents, statement, replacement) {
  const block = parents.get(statement);
  if (!block || !Array.isArray(block.statements)) return false;
  const at = block.statements.indexOf(statement);
  if (at < 0) return false;
  block.statements.splice(at, 1, ...replacement);
  return true;
}

function place(chunk, vm, lifted) {
  const parents = parentMap(chunk);
  const statement = tailReturn(vm.wrapperCall, parents);
  if (statement && replaceStatement(parents, statement, lifted.body.statements)) {
    return 'inline';
  }

  const call = vm.wrapperCall;
  call.base = A.paren(A.func([], lifted.body, true));
  call.args = [A.vararg()];
  return 'closure';
}

function devirtualize(context, vm, counter) {
  const cfg = buildCfg(vm);
  const lifted = liftVm(vm, cfg, { counter, varargs: varargsArg(vm) });
  for (const warning of lifted.warnings) {
    context.warn(`lift: ${warning.kind} ${JSON.stringify(warning)}`);
    context.bump(`lift.${warning.kind}`);
  }
  const reseated = reseat(context, vm, lifted);
  if (reseated) context.bump('devirtualize.reseated', reseated);
  const how = place(context.chunk, vm, lifted);
  context.bump(`devirtualize.${how}`);
  context.bump('devirtualize.blocks', cfg.blocks.size);
  context.bump('devirtualize.functions', cfg.functions.length);
  return lifted.counter;
}

function run(context) {
  let counter = 0;
  let layers = 0;
  for (let pass = 0; pass < 32; pass += 1) {
    context.resolve();
    const found = detect(context.chunk);
    for (const rejected of found.rejected) {
      context.bump(`devirtualize.rejected.${rejected.reason}`);
    }
    if (!found.instances.length) break;

    for (const vm of found.instances) {
      counter = devirtualize(context, vm, counter);
      layers += 1;
      context.reportProgress('progress', {
        step: '04-devirt',
        layers,
        blocks: context.stats['devirtualize.blocks'] || 0,
        functions: context.stats['devirtualize.functions'] || 0,
      });
    }

    context.resolve();
    fold.run(context);

    guards.run(context);
    context.resolve();
    decrypt.run(context);

    context.resolve();
    idioms.run(context);
  }
  if (layers) {
    context.resolve();

    const discharged = discharge(context.chunk);
    if (discharged) {
      context.bump('devirtualize.discharged', discharged);
      context.resolve();
    }
    context.note(`devirtualized ${layers} VM layer(s)`, layers);
    context.bump('devirtualize.layers', layers);
  }
}

module.exports = { name: '04-lift', run, resultList };
