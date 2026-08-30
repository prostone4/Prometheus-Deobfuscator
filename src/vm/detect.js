'use strict';

const { Kind, unparen } = require('../lua/ast');
const { walk, children, collect } = require('../lua/walk');

const isName = (node) => !!node && node.kind === Kind.Name;
const bindingOf = (node) => {
  const inner = unparen(node);
  return isName(inner) ? inner.binding || null : null;
};

function parentMap(root) {
  const parents = new Map();
  walk(root, {
    enter(node, info) {
      if (info) parents.set(node, info.parent);
      return undefined;
    },
  });
  return parents;
}

function valueFlow(chunk) {
  const writes = new Map();
  const moves = new Map();
  const record = (binding, value) => {
    if (!binding) return;
    const list = writes.get(binding) || [];
    list.push(value || null);
    writes.set(binding, list);
    const source = value ? bindingOf(value) : null;
    if (!source) return;
    const targets = moves.get(source) || [];
    targets.push(binding);
    moves.set(source, targets);
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        const aligned = targets.length === expressions.length;
        targets.forEach((target, at) => {
          record(bindingOf(target), aligned ? expressions[at] : null);
        });
      } else if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];

        if (!expressions.length) return undefined;
        const aligned = expressions.length === (node.names || []).length;
        (node.bindings || []).forEach((binding, at) => {
          record(binding, aligned ? expressions[at] : null);
        });
      } else if (node.kind === Kind.LocalFunction) record(node.binding, node.body);
      else if (node.kind === Kind.NumericFor) record(node.binding, null);
      else if (node.kind === Kind.GenericFor) {
        for (const binding of node.bindings || []) record(binding, null);
      }
      return undefined;
    },
  });
  return { writes, moves };
}

function carriersOf(target, flow) {
  if (!flow || !target) return null;
  if (!flow.carriers) flow.carriers = new Map();
  const known = flow.carriers.get(target);
  if (known) return known;
  const found = new Set([target]);
  const queue = [target];
  while (queue.length) {
    const at = queue.pop();
    for (const holder of flow.moves.get(at) || []) {
      if (found.has(holder)) continue;
      found.add(holder);
      queue.push(holder);
    }
  }
  flow.carriers.set(target, found);
  return found;
}

function carriesBinding(binding, target, flow) {
  if (!binding) return false;
  if (binding === target) return true;
  const found = carriersOf(target, flow);
  return !!found && found.has(binding);
}

function carries(node, target, flow) {
  return carriesBinding(bindingOf(node), target, flow);
}

function carrierTest(target, flow) {
  if (!target) return () => false;
  return (node) => carriesBinding(bindingOf(node), target, flow);
}

function carrierSet(targets, flow) {
  const list = [...targets].filter(Boolean);
  if (!list.length) return () => false;
  return (node) => {
    const binding = bindingOf(node);
    if (!binding) return false;
    return list.some((target) => carriesBinding(binding, target, flow));
  };
}

function mayHold(node, kind, flow, seen = new Set()) {
  const value = unparen(node);
  if (!value) return false;
  if (value.kind === kind) return true;
  const binding = bindingOf(value);
  if (!binding || !flow || seen.has(binding)) return false;
  seen.add(binding);
  for (const written of flow.writes.get(binding) || []) {
    if (written && mayHold(written, kind, flow, seen)) return true;
  }
  return false;
}

function throughCopy(binding, flow) {
  let current = binding;
  for (let guard = 0; flow && current && guard < 8; guard += 1) {
    if ((current.reads || []).length !== 1) break;
    const targets = flow.moves.get(current) || [];
    if (targets.length !== 1) break;
    const written = flow.writes.get(targets[0]) || [];
    if (written.length !== 1 || !written[0]) break;
    current = targets[0];
  }
  return current;
}

function throughSource(binding, flow) {
  let current = binding;
  for (let guard = 0; flow && current && guard < 8; guard += 1) {
    const written = flow.writes.get(current) || [];
    if (written.length !== 1 || !written[0]) break;
    const source = bindingOf(written[0]);
    if (!source || source === current) break;
    current = source;
  }
  return current;
}

const ROLES = [
  ['env', ['getfenv', '_ENV', 'getfenv2']],
  ['unpack', ['unpack']],
  ['newproxy', ['newproxy']],
  ['setmetatable', ['setmetatable']],
  ['getmetatable', ['getmetatable']],
  ['select', ['select']],
];

function globalsUsed(node) {
  const names = new Set();
  walk(node, {
    enter(inner) {
      if (inner.kind === Kind.Name && inner.binding && inner.binding.kind === 'global') {
        names.add(inner.binding.name);
      }
      return undefined;
    },
  });
  return names;
}

function classifyValue(node) {
  const inner = unparen(node);
  if (!inner) return null;

  if (inner.kind === Kind.Table) return 'varargs';
  const globals = globalsUsed(inner);
  for (const [role, candidates] of ROLES) {
    for (const candidate of candidates) {
      if (globals.has(candidate)) return role;
    }
  }

  if (globals.has('table')) return 'unpack';
  return null;
}

function classifyArgument(node, flow) {
  const direct = classifyValue(node);
  if (direct) return direct;
  const binding = bindingOf(unparen(node));
  if (!binding || !flow) return null;
  const seen = new Set([binding]);
  const pending = [binding];
  while (pending.length) {
    const current = pending.shift();
    const written = flow.writes.get(current) || [];
    for (let i = written.length - 1; i >= 0; i -= 1) {
      const value = written[i];
      if (!value) continue;
      const role = classifyValue(value);
      if (role) return role;
      const source = bindingOf(value);
      if (source && !seen.has(source)) {
        seen.add(source);
        pending.push(source);
      }
    }
  }
  return null;
}

function readsVarargs(fn) {
  if (!fn || !fn.isVararg) return false;
  let found = false;
  walk(fn.body, {
    enter(node) {
      if (found) return false;
      if (node.kind === Kind.Function) return false;
      if (node.kind === Kind.Vararg) found = true;
      return undefined;
    },
  });
  return found;
}

function spreadsVarargs(node) {
  const table = unparen(node);
  if (!table || table.kind !== Kind.Table) return false;
  return (table.entries || []).some((entry) => (
    !entry.key && entry.value && unparen(entry.value).kind === Kind.Vararg));
}

function matchContainer(fn, flow) {
  if (!fn || fn.kind !== Kind.Function || readsVarargs(fn)) return null;
  if (!fn.params || fn.params.length !== 4 || !fn.bindings) return null;
  const statements = fn.body.statements;
  if (statements.length < 2) return null;

  const candidates = new Set([fn.bindings[0]]);
  for (const moved of (flow && flow.moves.get(fn.bindings[0])) || []) candidates.add(moved);
  let loopIndex = -1;
  for (let i = 0; i < statements.length; i += 1) {
    const statement = statements[i];
    if (statement.kind === Kind.While && candidates.has(bindingOf(statement.condition))) {
      loopIndex = i;
      break;
    }
  }
  if (loopIndex < 0) return null;
  const pos = bindingOf(statements[loopIndex].condition);

  const declared = new Set();
  const registers = [];
  let spill = null;
  for (let i = 0; i < loopIndex; i += 1) {
    const statement = statements[i];
    if (statement.kind === Kind.LocalDeclaration && statement.bindings) {
      const expressions = statement.expressions || [];
      for (let k = 0; k < statement.bindings.length; k += 1) {
        const binding = statement.bindings[k];
        declared.add(binding);
        const initializer = unparen(expressions[k]);
        if (initializer && initializer.kind === Kind.Table) spill = binding;
        else registers.push(binding);
      }
      continue;
    }
    if (statement.kind === Kind.Assignment) {
      const targets = statement.targets || [];
      const expressions = statement.expressions || [];
      if (targets.length !== expressions.length) return null;
      for (let k = 0; k < targets.length; k += 1) {
        const binding = bindingOf(targets[k]);
        if (!binding || !declared.has(binding)) return null;
        const value = unparen(expressions[k]);
        if (value && value.kind === Kind.Table) spill = binding;
      }
      continue;
    }
    return null;
  }

  const last = statements[statements.length - 1];
  if (!last || last.kind !== Kind.Return || last.expressions.length !== 1) return null;
  const call = unparen(last.expressions[0]);
  if (!call || call.kind !== Kind.Call || call.args.length !== 1) return null;
  const unpackBinding = bindingOf(call.base);
  const returnBinding = bindingOf(call.args[0]);
  if (!unpackBinding || !returnBinding) return null;

  const args = throughCopy(fn.bindings[1], flow);
  const upvals = throughCopy(fn.bindings[2], flow);
  const gcDetect = throughCopy(fn.bindings[3], flow);
  const reserved = new Set([spill, args, upvals, gcDetect]);

  return {
    fn,
    dispatch: statements[loopIndex],
    registers: registers.filter((binding) => !reserved.has(binding)),
    spill,
    unpackBinding,
    returnRegister: returnBinding,
    pos,
    args,
    upvals,
    gcDetect,
  };
}

function matchClosureCreator(fn, containerBinding, flow) {
  if (!fn || fn.kind !== Kind.Function || readsVarargs(fn)) return null;
  if (!fn.params || fn.params.length !== 2 || !fn.bindings) return null;
  const [idParam, upvalsParam] = fn.bindings;
  let found = null;
  walk(fn.body, {
    enter(node) {
      if (node.kind !== Kind.Function) return undefined;
      const body = node.body.statements;

      const tail = body[body.length - 1];
      if (!tail || tail.kind !== Kind.Return || tail.expressions.length !== 1) return undefined;
      const call = unparen(tail.expressions[0]);
      if (!call || call.kind !== Kind.Call || call.args.length !== 4) return undefined;
      if (!carries(call.base, containerBinding, flow)) return undefined;
      if (!carries(call.args[0], idParam, flow)) return undefined;
      if (!carries(call.args[2], upvalsParam, flow)) return undefined;
      if (!mayHold(call.args[1], Kind.Table, flow)) return undefined;
      found = { inner: node, table: call.args[1], gcExpression: call.args[3] };
      return false;
    },
  });
  if (!found) return null;

  let proxyBinding = null;
  walk(fn.body, {
    enter(node) {
      if (proxyBinding) return false;
      if (node.kind !== Kind.Call || node.args.length !== 1) return undefined;
      if (!carries(node.args[0], upvalsParam, flow)) return undefined;
      proxyBinding = bindingOf(node.base);
      return undefined;
    },
  });

  return {
    fn,
    arity: (found.inner.params || []).length,

    vararg: spreadsVarargs(found.table),
    proxyBinding,
  };
}

function matchAllocUpvalue(fn) {
  if (!fn || fn.kind !== Kind.Function || readsVarargs(fn)) return null;
  if ((fn.params || []).length !== 0) return null;
  const statements = fn.body.statements;
  if (statements.length !== 3) return null;
  const [bump, seed, ret] = statements;
  if (bump.kind !== Kind.Assignment || bump.targets.length !== 1) return null;
  const counter = bindingOf(bump.targets[0]);
  if (!counter) return null;
  const sum = unparen(bump.expressions[0]);
  if (!sum || sum.kind !== Kind.Binary || sum.operator !== '+') return null;
  const operands = [bindingOf(sum.lhs), bindingOf(sum.rhs)];
  if (!operands.includes(counter)) return null;
  if (seed.kind !== Kind.Assignment || seed.targets.length !== 1) return null;
  const slot = unparen(seed.targets[0]);
  if (!slot || slot.kind !== Kind.Index || bindingOf(slot.index) !== counter) return null;
  const refs = bindingOf(slot.base);
  if (!refs) return null;
  if (ret.kind !== Kind.Return || bindingOf(ret.expressions[0]) !== counter) return null;
  return { counter, refs };
}

function findUpvalueTable(root, refs, flow) {
  const clears = [];
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Assignment) return undefined;
      if (!node.expressions.every((expression) => unparen(expression).kind === Kind.Nil)) {
        return undefined;
      }
      for (const target of node.targets || []) {
        const inner = unparen(target);
        if (!inner || inner.kind !== Kind.Index) continue;
        const base = throughSource(bindingOf(inner.base), flow);
        const key = bindingOf(inner.index);
        if (base && key) clears.push({ base, key });
      }
      return undefined;
    },
  });
  const keys = new Set();
  for (const clear of clears) if (clear.base === refs) keys.add(clear.key);
  for (const clear of clears) {
    if (clear.base !== refs && keys.has(clear.key)) return clear.base;
  }
  return null;
}

function findRefHelpers(fns, isRefs, parents) {
  const helpers = new Set();
  for (const fn of fns) {
    let touches = false;
    walk(fn.body, {
      enter(node) {
        if (node.kind !== Kind.Assignment) return undefined;
        for (const target of node.targets || []) {
          const slot = unparen(target);
          if (slot && slot.kind === Kind.Index && isRefs(slot.base)) touches = true;
        }
        return undefined;
      },
    });
    if (!touches) continue;
    const binding = bindingForValue(fn, parents);
    if (binding) helpers.add(binding);
  }
  return helpers;
}

function skipParens(node, parents) {
  let current = node;
  let parent = parents.get(current);
  while (parent && parent.kind === Kind.Paren) {
    current = parent;
    parent = parents.get(current);
  }
  return { node: current, parent };
}

function bindingForValue(node, parents) {
  const { node: outer, parent } = skipParens(node, parents);
  if (!parent) return null;
  if (parent.kind === Kind.Assignment) {
    const at = parent.expressions.indexOf(outer);
    if (at < 0) return null;
    return bindingOf(parent.targets[at]);
  }
  if (parent.kind === Kind.LocalDeclaration) {
    const at = parent.expressions.indexOf(outer);
    if (at < 0 || !parent.bindings) return null;
    return parent.bindings[at] || null;
  }
  if (parent.kind === Kind.LocalFunction) return parent.binding || null;
  return null;
}

function enclosingFunction(node, parents) {
  let current = parents.get(node);
  while (current) {
    if (current.kind === Kind.Function) return current;
    current = parents.get(current);
  }
  return null;
}

function subtreeSet(root) {
  const set = new Set();
  walk(root, {
    enter(node) {
      set.add(node);
      return undefined;
    },
  });
  return set;
}

function functionsOutside(root, excluded) {
  const found = [];
  walk(root, {
    enter(node) {
      if (node === excluded) return false;
      if (node.kind === Kind.Function && node !== root) found.push(node);
      return undefined;
    },
  });
  return found;
}

function statementIn(node, parents) {
  let current = node;
  let parent = parents.get(current);
  while (parent && parent.kind !== Kind.Block) {
    current = parent;
    parent = parents.get(current);
  }
  if (!parent) return null;
  const index = parent.statements.indexOf(current);
  return index < 0 ? null : { block: parent, index };
}

function reaches(definition, use, binding, parents) {
  if (!definition || !use || definition.block !== use.block) return false;
  if (use.index <= definition.index) return false;
  for (const write of (binding && binding.writes) || []) {
    const at = statementIn(write, parents);
    if (!at || at.block !== definition.block) continue;
    if (at.index > definition.index && at.index < use.index) return false;
  }
  return true;
}

function callOf(binding, definition, parents) {
  let best = null;
  for (const read of binding.reads || []) {
    const { node, parent: outer } = skipParens(read, parents);
    if (!outer || outer.kind !== Kind.Call || unparen(outer.base) !== node) continue;
    const use = statementIn(read, parents);
    if (!reaches(definition, use, binding, parents)) continue;
    if (!best || use.index < best.index) best = { call: outer, index: use.index };
  }
  return best ? best.call : null;
}

function copiesOf(binding, flow) {
  const found = [];
  const seen = new Set([binding]);
  const stack = [binding];
  while (stack.length && found.length < 16) {
    const current = stack.pop();
    for (const target of (flow && flow.moves.get(current)) || []) {
      if (seen.has(target)) continue;
      seen.add(target);
      if ((flow.writes.get(target) || []).length !== 1) continue;
      found.push(target);
      stack.push(target);
    }
  }
  return found;
}

function definedAt(binding, flow, parents) {
  const written = (flow && flow.writes.get(binding)) || [];
  if (written.length !== 1 || !written[0]) return null;
  return statementIn(written[0], parents);
}

function findWrapperCall(wrapper, parents, flow) {
  const { parent } = skipParens(wrapper, parents);
  if (parent && parent.kind === Kind.Call && unparen(parent.base) === wrapper) return parent;
  const binding = bindingForValue(wrapper, parents);
  if (!binding) return null;
  const definition = statementIn(wrapper, parents);
  if (!definition) return null;
  const direct = callOf(binding, definition, parents);
  if (direct) return direct;
  for (const alias of copiesOf(binding, flow)) {
    const at = definedAt(alias, flow, parents);
    const call = at ? callOf(alias, at, parents) : null;
    if (call) return call;
  }
  return null;
}

function indexBases(root) {
  const counts = new Map();
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Index) return undefined;
      const binding = bindingOf(node.base);
      if (binding) counts.set(binding, (counts.get(binding) || 0) + 1);
      return undefined;
    },
  });
  return counts;
}

function environmentBinding(container, claimed) {
  const own = new Set([
    container.spill, container.pos, container.args, container.upvals, container.gcDetect,
    ...container.registers, ...(container.fn.bindings || []),
  ]);
  let best = null;
  let bestCount = 0;
  for (const [binding, count] of indexBases(container.fn)) {
    if (own.has(binding) || claimed.has(binding)) continue;
    if (count > bestCount) {
      best = binding;
      bestCount = count;
    }
  }
  return best;
}

function describe(container, parents, flow) {
  const wrapper = enclosingFunction(container.fn, parents);
  if (!wrapper) return { ok: false, reason: 'container is not wrapped' };

  const wrapperCall = findWrapperCall(wrapper, parents, flow);
  if (!wrapperCall) return { ok: false, reason: 'wrapper is not invoked' };

  const containerBinding = bindingForValue(container.fn, parents);
  if (!containerBinding) return { ok: false, reason: 'container is not bound to a name' };

  const roles = {};
  for (let i = 0; i < wrapperCall.args.length; i += 1) {
    const role = classifyArgument(wrapperCall.args[i], flow);
    const binding = (wrapper.bindings || [])[i];
    if (role && binding && !roles[role]) roles[role] = throughCopy(binding, flow);
  }

  if (!roles.unpack && container.unpackBinding) roles.unpack = container.unpackBinding;

  const inner = functionsOutside(wrapper, container.fn);
  const creators = new Map();
  const creatorFns = new Set();
  let upvalues = null;
  let proxyBinding = null;
  for (const fn of inner) {
    const creator = matchClosureCreator(fn, containerBinding, flow);
    if (creator) {
      creatorFns.add(fn);
      const binding = bindingForValue(fn, parents);
      if (binding) {
        creators.set(binding, creator);
        if (creator.proxyBinding) proxyBinding = creator.proxyBinding;
      }
      continue;
    }
    if (!upvalues) {
      const alloc = matchAllocUpvalue(fn);
      if (alloc) {
        upvalues = {
          alloc: bindingForValue(fn, parents),
          counter: alloc.counter,
          refs: alloc.refs,
          table: findUpvalueTable(wrapper, alloc.refs, flow),
        };
      }
    }
  }
  if (creators.size === 0) return { ok: false, reason: 'no closure creator' };

  if (upvalues) {
    upvalues.isAlloc = carrierTest(upvalues.alloc, flow);
    upvalues.isTable = carrierTest(upvalues.table, flow);
    upvalues.isRefs = carrierTest(upvalues.refs, flow);
    upvalues.helpers = findRefHelpers(
      inner.filter((fn) => !creatorFns.has(fn)),
      upvalues.isRefs,
      parents,
    );
    upvalues.isHelper = carrierSet(upvalues.helpers, flow);
  }
  container.isUpvals = carrierTest(container.upvals, flow);

  const creatorFor = (node) => {
    const binding = bindingOf(node);
    if (!binding) return null;
    const direct = creators.get(binding);
    if (direct) return direct;
    for (const [candidate, creator] of creators) {
      if (carriesBinding(binding, candidate, flow)) return creator;
    }
    return null;
  };

  if (!roles.env) {
    const claimed = new Set([
      ...Object.values(roles), ...creators.keys(), proxyBinding,
      upvalues && upvalues.alloc, upvalues && upvalues.counter,
      upvalues && upvalues.refs, upvalues && upvalues.table,
    ]);
    roles.env = environmentBinding(container, claimed);
  }
  if (!roles.env) return { ok: false, reason: 'no environment argument' };

  let entry = null;
  const containerNodes = subtreeSet(container.fn);
  walk(wrapper, {
    enter(node) {
      if (entry || containerNodes.has(node)) return false;
      if (node.kind !== Kind.Call) return undefined;
      const callee = unparen(node.base);
      if (!callee || callee.kind !== Kind.Call) return undefined;
      const creatorBinding = bindingOf(callee.base);
      const creator = creatorFor(callee.base);
      if (!creator) return undefined;
      const id = unparen(callee.args[0]);
      if (!id || id.kind !== Kind.Number) return undefined;
      entry = {
        blockId: id.value,
        creatorBinding,
        vararg: creator.vararg,
        arity: creator.arity,
        upvalsExpression: callee.args[1] || null,
        call: node,
      };
      return false;
    },
  });
  if (!entry) return { ok: false, reason: 'no entry closure' };

  return {
    ok: true,
    vm: {
      wrapper,
      wrapperCall,
      container,
      containerBinding,
      roles,
      creators,
      creatorFor,
      upvalues,
      proxyBinding,
      entry,
    },
  };
}

function detect(chunk) {
  const parents = parentMap(chunk);
  const flow = valueFlow(chunk);
  const found = [];
  const rejected = [];
  for (const fn of collect(chunk, (node) => node.kind === Kind.Function)) {
    const container = matchContainer(fn, flow);
    if (!container) continue;
    const result = describe(container, parents, flow);
    if (result.ok) found.push(result.vm);
    else rejected.push({ fn, reason: result.reason });
  }
  return { instances: found, rejected, parents };
}

module.exports = {
  unparen,
  bindingOf,
  parentMap,
  carries,
  detect,
};
