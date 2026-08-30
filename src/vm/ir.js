'use strict';

const { Kind, isMultiValue } = require('../lua/ast');
const { CHILDREN } = require('../lua/walk');
const { unparen, bindingOf } = require('./detect');

const REF = 'VmRef';
const LIVE = 'VmLive';

const ref = (index, slot) => ({ kind: REF, index, slot });
const live = (reg) => ({ kind: LIVE, reg });

function mapNode(node, fn) {
  const spec = CHILDREN[node.kind];
  const copy = { ...node };
  if (!spec) return copy;
  for (const key of Object.keys(spec)) {
    const type = spec[key];
    const value = node[key];
    if (value === undefined || value === null) continue;
    if (type === 'node') copy[key] = fn(value);
    else if (type === 'list') copy[key] = value.map(fn);
    else if (type === 'clauses') {
      copy[key] = value.map((clause) => ({
        ...clause,
        condition: fn(clause.condition),
        body: fn(clause.body),
      }));
    } else if (type === 'entries') {
      copy[key] = value.map((entry) => ({
        ...entry,
        key: entry.key ? fn(entry.key) : entry.key,
        value: fn(entry.value),
      }));
    }
  }
  return copy;
}

function registerSet(vm) {
  if (!vm.regSet) {
    vm.regSet = new Set(vm.container.registers);
    vm.regSet.add(vm.container.pos);
    vm.posKey = `r${vm.container.pos.id}`;
    vm.returnKey = `r${vm.container.returnRegister.id}`;
  }
  return vm.regSet;
}

function registerKey(vm, node) {
  const inner = unparen(node);
  if (!inner) return null;
  if (inner.kind === Kind.Name) {
    const binding = inner.binding;
    return binding && registerSet(vm).has(binding) ? `r${binding.id}` : null;
  }
  if (inner.kind === Kind.Index && vm.container.spill) {
    if (bindingOf(inner.base) !== vm.container.spill) return null;
    const key = unparen(inner.index);
    if (key && key.kind === Kind.Number) return `s${key.value}`;
    return null;
  }
  return null;
}

function isAlias(vm, target) {
  const binding = bindingOf(target);
  if (!binding) return false;
  const { args, upvals, gcDetect } = vm.container;
  return binding === args || binding === upvals || binding === gcDetect;
}

function isAliasMove(vm, statement) {
  return statement.targets.length === 1 && isAlias(vm, statement.targets[0]);
}

function isCalling(node) {
  if (!node || typeof node !== 'object') return false;
  if (node.kind === Kind.Call || node.kind === Kind.MethodCall) return true;
  const spec = CHILDREN[node.kind];
  if (!spec) return false;
  for (const key of Object.keys(spec)) {
    const type = spec[key];
    const value = node[key];
    if (value === undefined || value === null) continue;
    if (type === 'node') {
      if (isCalling(value)) return true;
    } else if (type === 'list') {
      for (const child of value) if (isCalling(child)) return true;
    } else if (type === 'clauses') {
      for (const clause of value) {
        if (isCalling(clause.condition) || isCalling(clause.body)) return true;
      }
    } else if (type === 'entries') {
      for (const entry of value) {
        if ((entry.key && isCalling(entry.key)) || isCalling(entry.value)) return true;
      }
    }
  }
  return false;
}

function isOrdered(node) {
  if (!node || typeof node !== 'object') return false;
  if (node.kind === Kind.Call || node.kind === Kind.MethodCall) return true;
  if (node.kind === Kind.Index) return true;
  const spec = CHILDREN[node.kind];
  if (!spec) return false;
  for (const key of Object.keys(spec)) {
    const type = spec[key];
    const value = node[key];
    if (value === undefined || value === null) continue;
    if (type === 'node') {
      if (isOrdered(value)) return true;
    } else if (type === 'list') {
      for (const child of value) if (isOrdered(child)) return true;
    } else if (type === 'clauses') {
      for (const clause of value) {
        if (isOrdered(clause.condition) || isOrdered(clause.body)) return true;
      }
    } else if (type === 'entries') {
      for (const entry of value) {
        if ((entry.key && isOrdered(entry.key)) || isOrdered(entry.value)) return true;
      }
    }
  }
  return false;
}

function buildBlock(vm, leaf) {
  registerSet(vm);
  const statements = [];
  const version = new Map();
  const liveIn = new Set();
  const written = new Set();
  const unsupported = [];

  const readRegister = (key) => {
    const at = version.get(key);
    if (at) return ref(at.index, at.slot);
    if (!written.has(key)) liveIn.add(key);
    return live(key);
  };

  const substitute = (node) => {
    if (!node || typeof node !== 'object') return node;
    const key = registerKey(vm, node);
    if (key) return readRegister(key);
    if (node.kind === Kind.Paren) {
      const inner = substitute(node.expression);
      if (isMultiValue(unparen(node)) && inner && typeof inner === 'object') {
        inner.truncated = true;
      }
      return inner;
    }
    return mapNode(node, substitute);
  };

  for (const source of leaf.statements) {
    if (source.kind === Kind.CallStatement) {
      statements.push({
        index: statements.length,
        targets: [],
        exprs: [substitute(source.expression)],
        ordered: true,
        source,
      });
      continue;
    }
    if (source.kind !== Kind.Assignment) {
      unsupported.push(source);
      continue;
    }
    if (isAliasMove(vm, source)) continue;

    const exprs = source.expressions.map(substitute);
    const targets = source.targets.map((target) => {
      const key = registerKey(vm, target);
      if (key) return { reg: key, node: null };
      const inner = unparen(target);
      if (inner.kind === Kind.Index) {
        return {
          reg: null,
          node: { ...inner, base: substitute(inner.base), index: substitute(inner.index) },
        };
      }
      return { reg: null, node: { ...inner } };
    });
    const split = targets.length > 1 && exprs.length === targets.length;
    const parts = split
      ? targets.map((target, at) => ({ targets: [target], exprs: [exprs[at]], at }))
      : [{ targets, exprs, at: -1 }];
    for (const part of parts) {
      if (part.at >= 0 && isAlias(vm, source.targets[part.at])
        && !isOrdered(part.exprs[0])) continue;
      const index = statements.length;
      statements.push({
        index,
        targets: part.targets,
        exprs: part.exprs,
        ordered: part.exprs.some(isOrdered) || part.targets.some((entry) => entry.node !== null),
        source,
      });
      for (let slot = 0; slot < part.targets.length; slot += 1) {
        const { reg } = part.targets[slot];
        if (!reg) continue;
        version.set(reg, { index, slot });
        written.add(reg);
      }
    }
  }

  return {
    leaf,
    statements,
    liveIn,
    written,
    unsupported,
    exit: version.get(vm.posKey) || null,
  };
}

function exprAt(statement, slot) {
  if (!statement) return null;
  if (statement.exprs.length === statement.targets.length) {
    return statement.exprs[slot] || null;
  }
  if (statement.targets.length === 1) return statement.exprs[0] || null;
  return null;
}

function definition(block, node) {
  if (!node || node.kind !== REF) return null;
  return exprAt(block.statements[node.index], node.slot);
}

function peel(block, node, depth = 0) {
  let current = node;
  let guard = depth;
  while (current && current.kind === REF && guard < 256) {
    const next = definition(block, current);
    if (!next) return current;
    current = next;
    guard += 1;
  }
  return current;
}

function classifyExit(block, node, depth = 0) {
  if (depth > 64) return { kind: 'unknown' };
  const value = peel(block, node, depth);
  if (!value) return { kind: 'return' };
  if (value.kind === Kind.Number) return { kind: 'goto', target: value.value };
  if (value.kind === Kind.Nil) return { kind: 'return' };
  if (value.kind === Kind.Index) return { kind: 'return' };
  if (value.kind === Kind.Binary && value.operator === 'or') {
    const left = classifyExit(block, value.lhs, depth + 1);
    const right = classifyExit(block, value.rhs, depth + 1);
    if (left.kind !== 'guarded') return { kind: 'unknown' };
    if (right.kind === 'goto') {
      return {
        kind: 'branch',
        condition: left.condition,
        whenTrue: left.target,
        whenFalse: right.target,
      };
    }
    if (right.kind === 'return') {
      return {
        kind: 'branch', condition: left.condition, whenTrue: left.target, whenFalse: null,
      };
    }
    return { kind: 'unknown' };
  }
  if (value.kind === Kind.Binary && value.operator === 'and') {
    const target = classifyExit(block, value.rhs, depth + 1);
    if (target.kind !== 'goto') return { kind: 'unknown' };

    return { kind: 'guarded', condition: value.lhs, target: target.target };
  }
  return { kind: 'unknown' };
}

function terminator(block) {
  if (!block.exit) return { kind: 'unknown', index: null };
  const statement = block.statements[block.exit.index];
  const value = exprAt(statement, block.exit.slot);
  if (!value) return { kind: 'unknown', index: null };
  const classified = classifyExit(block, value);
  if (classified.kind === 'guarded') {
    return {
      kind: 'branch',
      condition: classified.condition,
      whenTrue: classified.target,
      whenFalse: null,
      index: block.exit.index,
    };
  }
  return { ...classified, index: block.exit.index };
}

module.exports = {
  REF,
  LIVE,
  live,
  mapNode,
  isCalling,
  buildBlock,
  definition,
  peel,
  terminator,
};
