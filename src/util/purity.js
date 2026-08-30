'use strict';

const { Kind, unparen } = require('../lua/ast');
const { walk, children, collect } = require('../lua/walk');
const { isGlobalName, isLocalBinding } = require('../lua/scope');
const { Positions } = require('./order');

const GLOBALS = new Set([
  'pcall', 'xpcall', 'select', 'type', 'tostring', 'tonumber', 'unpack', 'rawequal',
  'rawget', 'rawset', 'rawlen', 'setmetatable', 'getmetatable', 'newproxy', 'next',
  'ipairs', 'pairs', 'loadstring', 'load', 'gcinfo', 'collectgarbage', 'getfenv',
]);

const TABLES = new Set([
  'math', 'string', 'table', 'debug', 'os', 'coroutine', 'bit', 'bit32', 'utf8', 'jit',
]);

const LIMIT = 96;
let owned = null;

const EFFECTS = new Set([
  'coroutine.yield', 'coroutine.resume', 'coroutine.wrap', 'coroutine.close',
  'os.exit', 'os.remove', 'os.rename', 'os.execute', 'os.setlocale', 'os.tmpname',
  'debug.setupvalue', 'debug.setlocal', 'debug.upvaluejoin', 'debug.setmetatable',
  'debug.setfenv', 'debug.debug',
]);

function hasEffect(base, key) {
  if (!key || key.kind !== Kind.String) return false;
  return EFFECTS.has(`${base.name}.${key.value}`);
}

const IMPURE = new Set(['error', 'assert', 'print', 'pcall_', 'os_exit']);

function localValues(root) {
  const writes = new Map();
  const record = (binding, expr, at, bare) => {
    if (!binding) return;
    let seen = writes.get(binding);
    if (!seen) {
      seen = { count: 0, bare: 0, valued: [] };
      writes.set(binding, seen);
    }
    seen.count += 1;
    if (expr) seen.valued.push({ expr, at });
    else if (bare) seen.bare += 1;
  };

  const filled = new Map();
  const fill = (target, expr) => {
    for (const said of collect(target, (one) => one.kind === Kind.Name)) {
      if (!said.binding) continue;
      let stored = filled.get(said.binding);
      if (!stored) filled.set(said.binding, stored = []);
      stored.push(expr || null);
    }
  };

  const derived = new Map();
  const derive = (binding, expressions) => {
    if (!binding) return;
    derived.set(binding, expressions.filter(Boolean));
  };
  const align = (node, bindings, expressions, bare) => {
    const list = bindings || [];
    for (let i = 0; i < list.length; i += 1) {
      const single = expressions.length === list.length;
      record(list[i], single ? expressions[i] : null, node, bare);
    }
  };
  walk(root, {
    enter(node) {
      if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        align(node, node.bindings, expressions, !expressions.length);
      } else if (node.kind === Kind.LocalFunction) {
        record(node.binding, node.body, node, false);
      } else if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        for (let i = 0; i < targets.length; i += 1) {
          const target = targets[i];
          if (!target) continue;
          const aligned = targets.length === expressions.length;
          if (target.kind !== Kind.Name) {
            fill(target, aligned ? expressions[i] : null);
            continue;
          }
          record(target.binding, aligned ? expressions[i] : null, node, false);
        }
      } else if (node.kind === Kind.NumericFor) {
        record(node.binding, null, node, false);
        derive(node.binding, [node.start, node.limit, node.step]);
      } else if (node.kind === Kind.GenericFor) {
        align(node, node.bindings, [], false);
        for (const binding of node.bindings || []) derive(binding, node.expressions || []);
      }
      else if (node.kind === Kind.Function) align(node, node.bindings, [], false);
      return undefined;
    },
  });
  const values = new Map();

  const callees = new Map();
  let positions = null;
  for (const [binding, info] of writes) {
    if (!info.valued.length) continue;

    if (info.bare + info.valued.length !== info.count) continue;
    callees.set(binding, info.valued.map((write) => write.expr));
    const reads = binding.reads || [];
    if (info.bare && reads.length) {
      if (!positions) positions = new Positions(root);
      const settled = info.valued.some(
        (write) => reads.every((read) => positions.precedes(write.at, read)));
      if (!settled) continue;
    }
    values.set(binding, info.valued.map((write) => write.expr));
  }
  for (const [binding, info] of writes) {
    if (info.count !== 1 || info.valued.length) derived.delete(binding);
  }
  return { values, derived, callees, filled };
}

function confined(node, facts, seen = new Set(), depth = 0) {
  if (!node || typeof node !== 'object' || depth > LIMIT) return false;
  switch (node.kind) {
    case Kind.Nil: case Kind.True: case Kind.False:
    case Kind.Number: case Kind.String:
      return true;
    case Kind.Function: {
      const region = () => new Set(node.bindings || []);
      if (owned) {
        const before = facts.loose.get(node);
        if (before) {
          for (const binding of before.cells) owned.add(binding);
          return before.ok;
        }
        const mine = new Set();
        const outer = owned;
        facts.loose.set(node, { ok: false, cells: mine });
        owned = mine;
        const found = isRemovableBlock(node.body, facts, new Set(), depth + 1, region());
        owned = outer;
        facts.loose.set(node, { ok: found, cells: mine });
        for (const binding of mine) owned.add(binding);
        return found;
      }
      const known = facts.functions.get(node);
      if (known !== undefined) return known;
      facts.functions.set(node, false);
      const answer = isRemovableBlock(node.body, facts, new Set(), depth + 1, region());
      facts.functions.set(node, answer);
      return answer;
    }
    case Kind.Vararg:
      return false;
    case Kind.Name: {
      if (IMPURE.has(node.name)) return false;
      if (isGlobalName(node)) {
        return GLOBALS.has(node.name) || TABLES.has(node.name);
      }
      const binding = node.binding;
      if (!binding || !isLocalBinding(binding)) return false;
      if (seen.has(binding)) return true;
      seen.add(binding);
      const defs = facts.sourcesOf(binding);
      if (!defs) return false;
      if (!defs.every((def) => confined(def, facts, new Set(seen), depth + 1))) return false;

      const stored = facts.fillsOf(binding);
      return !stored
        || stored.every((one) => !!one && confined(one, facts, new Set(seen), depth + 1));
    }
    case Kind.Paren:
      return confined(node.expression, facts, seen, depth + 1);
    case Kind.Unary:
      return confined(node.argument, facts, seen, depth + 1);
    case Kind.Binary:
      return confined(node.lhs, facts, seen, depth + 1)
        && confined(node.rhs, facts, new Set(seen), depth + 1);
    case Kind.Index:
      if (isGlobalName(node.base) && hasEffect(node.base, node.index)) return false;
      return confined(node.base, facts, seen, depth + 1)
        && confined(node.index, facts, new Set(seen), depth + 1);
    case Kind.Table:
      return (node.entries || []).every((entry) => (
        (!entry.key || confined(entry.key, facts, new Set(seen), depth + 1))
        && confined(entry.value, facts, new Set(seen), depth + 1)));
    case Kind.Call: case Kind.MethodCall: {
      const callable = node.kind === Kind.Call
        ? isPure(node.base, facts, new Set(), depth + 1)
        : confined(node.base, facts, new Set(seen), depth + 1);
      return callable
        && (node.args || []).every((arg) => confined(arg, facts, new Set(seen), depth + 1));
    }
    default:
      return false;
  }
}

class Facts {
  constructor(root) {
    const known = localValues(root);
    this.values = known.values;
    this.derived = known.derived;
    this.callees = known.callees;
    this.filled = known.filled;
    this.functions = new Map();
    this.loose = new Map();
  }

  valuesOf(binding) {
    return (binding && this.values.get(binding)) || null;
  }

  calleeValuesOf(binding) {
    return (binding && this.callees.get(binding)) || null;
  }

  fillsOf(binding) {
    return (binding && this.filled.get(binding)) || null;
  }

  sourcesOf(binding) {
    if (!binding) return null;
    return this.values.get(binding) || this.derived.get(binding) || null;
  }

  isConfined(node) {
    return confined(node, this, new Set(), 0);
  }
}

function uncallable(node, facts, seen = new Set(), depth = 0) {
  if (!node || depth > LIMIT) return false;
  switch (node.kind) {
    case Kind.Nil: case Kind.True: case Kind.False:
    case Kind.Number: case Kind.String:
      return true;

    case Kind.Table:
      return true;
    case Kind.Name: {
      if (isGlobalName(node)) return TABLES.has(node.name);
      const binding = node.binding;
      if (!binding || seen.has(binding)) return false;
      seen.add(binding);

      const defs = facts.calleeValuesOf(binding);
      return !!defs && defs.length > 0
        && defs.every((def) => uncallable(def, facts, new Set(seen), depth + 1));
    }
    case Kind.Paren:
      return uncallable(node.expression, facts, seen, depth + 1);
    default:
      return false;
  }
}

function isPure(node, facts, seen = new Set(), depth = 0) {
  if (!node || depth > LIMIT) return false;
  if (node.kind === Kind.Paren) return isPure(node.expression, facts, seen, depth + 1);
  if (node.kind === Kind.Name) {
    if (IMPURE.has(node.name)) return false;

    if (isGlobalName(node)) return GLOBALS.has(node.name);
    const binding = node.binding;
    if (!binding) return GLOBALS.has(node.name);
    if (seen.has(binding)) return false;
    seen.add(binding);
    const defs = (facts.calleeValuesOf(binding) || [])
      .filter((def) => !uncallable(def, facts, new Set(), depth + 1));
    return defs.length > 0
      && defs.every((def) => isPure(def, facts, new Set(seen), depth + 1));
  }
  if (node.kind === Kind.Index) {
    const base = node.base;
    const key = node.index;
    if (isGlobalName(base)) {
      if (!TABLES.has(base.name)) return false;
      if (hasEffect(base, key)) return false;
      return !key || key.kind === Kind.String;
    }

    return confined(base, facts, new Set(), depth + 1)
      && (!key || confined(key, facts, new Set(), depth + 1));
  }
  if (node.kind === Kind.Function) {
    return confined(node, facts, new Set(), depth + 1);
  }

  if (node.kind === Kind.Binary && (node.operator === 'or' || node.operator === 'and')) {
    const sides = [node.lhs, node.rhs]
      .filter((side) => !uncallable(side, facts, new Set(), depth + 1));
    return sides.length > 0
      && sides.every((side) => isPure(side, facts, seen, depth + 1));
  }

  return confined(node, facts, new Set(), depth + 1);
}

function writesOutside(node, facts) {
  const found = new Set();
  const outer = owned;
  owned = found;
  try {
    return isRemovable(node, facts) ? found : null;
  } finally {
    owned = outer;
  }
}

function targetWrites(target, facts) {
  const found = new Set();
  const outer = owned;
  owned = found;
  try {
    return ownWrite(target, facts, false) ? found : null;
  } finally {
    owned = outer;
  }
}

function isRemovable(node, facts, seen = new Set(), depth = 0) {
  if (!node || typeof node !== 'object') return true;
  if (depth > LIMIT) return false;
  switch (node.kind) {
    case Kind.Nil: case Kind.True: case Kind.False:
    case Kind.Number: case Kind.String: case Kind.Vararg: case Kind.Name:
      return true;
    case Kind.Function:
      return true;
    case Kind.Paren:
      return isRemovable(node.expression, facts, seen, depth + 1);
    case Kind.Unary:
      return isRemovable(node.argument, facts, seen, depth + 1);
    case Kind.Binary:
      return isRemovable(node.lhs, facts, seen, depth + 1)
        && isRemovable(node.rhs, facts, seen, depth + 1);
    case Kind.Index:
      return isRemovable(node.base, facts, seen, depth + 1)
        && isRemovable(node.index, facts, seen, depth + 1);
    case Kind.Table:
      return (node.entries || []).every((entry) => (
        (!entry.key || isRemovable(entry.key, facts, seen, depth + 1))
        && isRemovable(entry.value, facts, seen, depth + 1)));
    case Kind.Call:
      return isPure(node.base, facts, new Set(seen), depth + 1)
        && (node.args || []).every((arg) => isRemovable(arg, facts, seen, depth + 1));
    case Kind.MethodCall:
      return confined(node.base, facts, new Set(), depth + 1)
        && (node.args || []).every((arg) => confined(arg, facts, new Set(), depth + 1));
    default:
      return false;
  }
}

function throughBindings(node, facts) {
  const found = [];
  const chain = (binding) => {
    let inner = binding;
    while (inner && isLocalBinding(inner)) {
      if (found.includes(inner)) return;
      found.push(inner);
      const values = facts ? facts.valuesOf(inner) : null;
      let value = values && values.length === 1 ? values[0] : null;
      while (value && value.kind === Kind.Paren) value = value.expression;
      inner = value && value.kind === Kind.Name ? value.binding : null;
    }
  };
  const visit = (inner) => {
    if (!inner || !inner.kind || inner.kind === Kind.Function) return;
    if (inner.kind === Kind.Name) { chain(inner.binding); return; }
    for (const child of children(inner)) visit(child.node);
  };
  visit(node);
  return found;
}

function reachesLive(node, facts) {
  let found = false;
  walk(node, {
    enter(inner) {
      if (found) return false;

      if (inner.kind === Kind.Function) return false;
      if (inner.kind !== Kind.Call && inner.kind !== Kind.MethodCall) return undefined;
      const reached = [];

      if (inner.kind === Kind.MethodCall || (inner.base && inner.base.kind !== Kind.Name)) {
        reached.push(...throughBindings(inner.base, facts));
      }
      for (const argument of inner.args || []) reached.push(...throughBindings(argument, facts));
      if (reached.some((binding) => (binding.reads || []).length)) found = true;
      return undefined;
    },
  });
  return found;
}

function isSelfContained(node, facts) {
  return isRemovable(node, facts) && !reachesLive(node, facts);
}

const LOADERS = new Set(['load', 'loadstring', 'loadfile', 'dofile', 'require']);

function sealed(fn, facts) {
  const inside = new Set();
  const vouched = new Set();
  walk(fn, {
    enter(node) {
      inside.add(node);
      if (node.kind !== Kind.Call || !facts || !isPure(node.base, facts)) return undefined;
      const names = collect(node.base, (one) => one.kind === Kind.Name);
      if (names.some((one) => LOADERS.has(one.name))) return undefined;
      for (const one of names) vouched.add(one);
      return undefined;
    },
  });
  let clear = true;
  walk(fn, {
    enter(node) {
      if (node.kind !== Kind.Name || vouched.has(node)) return undefined;
      const binding = node.binding;
      if (!binding || !isLocalBinding(binding)) clear = false;
      else if (!binding.declaration || !inside.has(binding.declaration)) clear = false;
      return undefined;
    },
  });
  return clear;
}

function madeHere(node, facts, depth = 0) {
  const inner = unparen(node);
  if (!inner || depth > LIMIT) return false;
  switch (inner.kind) {
    case Kind.Nil:
    case Kind.True:
    case Kind.False:
    case Kind.Number:
    case Kind.String:
      return true;
    case Kind.Function:
      return sealed(inner, facts);
    case Kind.Table:
      return (inner.entries || []).every((entry) => madeHere(entry.value, facts, depth + 1)
        && (entry.type !== 'key' || madeHere(entry.key, facts, depth + 1)));
    default:
      return false;
  }
}

function touchesOwn(call, facts) {
  if (!call || call.kind !== Kind.Call) return false;
  return (call.args || []).every((argument) => madeHere(argument, facts));
}

function plainTable(value, facts, depth = 0) {
  const inner = unparen(value);
  if (!inner || depth > LIMIT) return false;
  if (inner.kind === Kind.Table) return true;
  if (madeHere(inner, facts, depth)) return true;
  if (inner.kind !== Kind.Call) return false;
  const callee = unparen(inner.base);
  if (!callee || callee.kind !== Kind.Name || !isGlobalName(callee)
    || callee.name !== 'setmetatable') return false;
  const args = inner.args || [];
  if (args.length !== 2 || !plainTable(args[0], facts, depth + 1)) return false;
  const meta = unparen(args[1]);
  if (!meta || meta.kind !== Kind.Table) return false;
  return (meta.entries || []).every((entry) => entry.type === 'key' && entry.key
    && entry.key.kind === Kind.String && entry.key.value !== '__newindex');
}

function holdsTable(binding, facts, spare, seen, depth) {
  if (!binding || !isLocalBinding(binding) || seen.has(binding) || depth > LIMIT) return false;
  seen.add(binding);
  if (!spare(binding)) return false;
  const values = facts ? facts.valuesOf(binding) : null;
  if (!values || !values.length) return false;
  return values.every((one) => {
    const inner = unparen(one);
    if (inner && inner.kind === Kind.Name && inner.binding) {
      return holdsTable(inner.binding, facts, spare, seen, depth + 1);
    }
    return plainTable(one, facts, depth + 1);
  });
}

function ownWrite(target, facts, region, depth = 0) {
  if (!target || depth > LIMIT) return false;
  const held = (binding) => !!region && !!region.has && region.has(binding);
  const spare = (binding) => {
    if (!binding.captured || held(binding)) return true;
    if (!owned) return false;
    owned.add(binding);
    return true;
  };
  if (target.kind === Kind.Name) {
    const binding = target.binding;
    if (!binding || !isLocalBinding(binding)) return false;
    return spare(binding);
  }
  if (target.kind === Kind.Index) {
    const base = unparen(target.base);
    if (!base || base.kind !== Kind.Name) return false;
    return holdsTable(base.binding, facts, spare, new Set(), depth + 1);
  }
  return false;
}

function declaredBy(statement, into) {
  if (statement.kind === Kind.LocalDeclaration) {
    for (const binding of statement.bindings || []) into.add(binding);
  } else if (statement.kind === Kind.LocalFunction) into.add(statement.binding);
  else if (statement.kind === Kind.NumericFor) into.add(statement.binding);
  else if (statement.kind === Kind.GenericFor) {
    for (const binding of statement.bindings || []) into.add(binding);
  }
}
function isRemovableBlock(block, facts, seen = new Set(), depth = 0, inFunction = false) {
  if (!block || depth > LIMIT) return false;
  const region = inFunction instanceof Set ? new Set(inFunction) : inFunction;
  return (block.statements || []).every((s) => {
    const ok = isRemovableStatement(s, facts, seen, depth + 1, region);
    if (region instanceof Set) declaredBy(s, region);
    return ok;
  });
}

function isRemovableStatement(statement, facts, seen = new Set(), depth = 0, inFunction = false) {
  if (!statement || depth > LIMIT) return false;
  const block = (b) => isRemovableBlock(b, facts, seen, depth + 1, inFunction);
  const value = (e) => isRemovable(e, facts, seen, depth + 1);
  switch (statement.kind) {
    case Kind.LocalDeclaration:
      return (statement.expressions || []).every(value);
    case Kind.Assignment:
      return (statement.targets || []).every((target) => ownWrite(target, facts, inFunction))
        && (statement.expressions || []).every(value);
    case Kind.LocalFunction:
    case Kind.Label:
      return true;
    case Kind.Return:
      return inFunction && (statement.expressions || []).every(value);
    case Kind.Break:
    case Kind.Continue:
      return inFunction;
    case Kind.CallStatement:
      return value(statement.expression);
    case Kind.Do:
      return block(statement.body);
    case Kind.While:
    case Kind.Repeat:
      return value(statement.condition) && block(statement.body);
    case Kind.NumericFor:
      return value(statement.start) && value(statement.limit) && value(statement.step)
        && block(statement.body);
    case Kind.GenericFor:
      return (statement.expressions || []).every(value) && block(statement.body);
    case Kind.If:
      return value(statement.condition) && block(statement.body)
        && (statement.elseIfs || []).every((clause) => (
          value(clause.condition) && block(clause.body)))
        && (!statement.elseBody || block(statement.elseBody));
    default:
      return false;
  }
}

module.exports = {
  TABLES,
  LOADERS,
  Facts,
  isRemovable,
  isSelfContained,
  sealed,
  touchesOwn,
  throughBindings,
  writesOutside,
  targetWrites,
};
