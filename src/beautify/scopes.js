'use strict';

const {
  Kind, block: makeBlock, doStatement, localDecl, assignment, name: makeName,
} = require('../lua/ast');
const { walk } = require('../lua/walk');

const LIMIT = 180;
const WINDOW = 24;
const RUN = 12;

function declaredCount(statement) {
  if (statement.kind === Kind.LocalDeclaration) return statement.names.length;
  if (statement.kind === Kind.LocalFunction) return 1;
  return 0;
}

function declaredBindings(statement) {
  if (statement.kind === Kind.LocalDeclaration) return statement.bindings || [];
  if (statement.kind === Kind.LocalFunction && statement.binding) return [statement.binding];
  return [];
}

function openedBy(statement) {
  switch (statement.kind) {
    case Kind.Do:
    case Kind.While:
      return [{ body: statement.body, extra: 0 }];
    case Kind.Repeat:
      return [{ body: statement.body, extra: 0, sealed: true }];
    case Kind.NumericFor:
      return [{ body: statement.body, extra: 4 }];
    case Kind.GenericFor:
      return [{ body: statement.body, extra: statement.variables.length + 3 }];
    case Kind.If: {
      const bodies = [{ body: statement.body, extra: 0 }];
      for (const clause of statement.elseIfs || []) bodies.push({ body: clause.body, extra: 0 });
      if (statement.elseBody) bodies.push({ body: statement.elseBody, extra: 0 });
      return bodies;
    }
    default:
      return [];
  }
}

function survey(body, base) {
  const blocks = [];
  let peak = base;
  const visit = (current, active, sealed) => {
    let live = active;
    let direct = 0;
    for (const statement of current.statements) {
      live += declaredCount(statement);
      direct += declaredCount(statement);
      if (live > peak) peak = live;
      for (const opened of openedBy(statement)) visit(opened.body, live + opened.extra, opened.sealed);
    }
    blocks.push({ block: current, base: active, direct, sealed });
  };
  visit(body, base, false);
  return { peak, blocks };
}

function jumps(block) {
  const stack = [block];
  while (stack.length) {
    const node = stack.pop();
    if (!node || typeof node !== 'object') continue;
    if (Array.isArray(node)) {
      for (const item of node) stack.push(item);
      continue;
    }
    if (node.kind === Kind.Function) continue;
    if (node.kind === Kind.Label || node.kind === Kind.Goto) return true;
    for (const key of Object.keys(node)) {
      if (key === 'binding' || key === 'bindings') continue;
      stack.push(node[key]);
    }
  }
  return false;
}

function sites(block) {
  const holder = new Map();
  block.statements.forEach((statement, at) => {
    walk(statement, {
      enter(node) {
        if (!holder.has(node)) holder.set(node, at);
        return undefined;
      },
    });
  });
  return holder;
}

function reachOf(block, holder) {
  const last = block.statements.length - 1;
  const reach = new Map();
  block.statements.forEach((statement, at) => {
    const bindings = declaredBindings(statement);
    if (!bindings.length) return;
    let to = at;
    for (const binding of bindings) {
      for (const use of binding.reads.concat(binding.writes)) {
        const site = holder.get(use);
        if (site === undefined) to = last;
        else if (site > to) to = site;
      }
    }
    reach.set(at, to);
  });
  return reach;
}

function ambiguous(block) {
  const owners = new Map();
  const note = (label, id) => {
    let seen = owners.get(label);
    if (!seen) {
      seen = new Set();
      owners.set(label, seen);
    }
    seen.add(id);
  };
  for (const statement of block.statements) {
    for (const binding of declaredBindings(statement)) note(binding.name, binding.id);
  }
  walk(block, {
    enter(node) {
      if (node.kind === Kind.Name && node.binding) note(node.name, node.binding.id);
      if (node.kind === Kind.LocalDeclaration) {
        for (const binding of node.bindings || []) note(binding.name, binding.id);
      }
      if (node.kind === Kind.LocalFunction && node.binding) note(node.binding.name, node.binding.id);
      if (node.kind === Kind.Function) {
        for (const binding of node.bindings || []) note(binding.name, binding.id);
      }
      if (node.kind === Kind.GenericFor) {
        for (const binding of node.bindings || []) note(binding.name, binding.id);
      }
      if (node.kind === Kind.NumericFor && node.binding) note(node.binding.name, node.binding.id);
      return undefined;
    },
  });
  const shared = new Set();
  for (const [label, seen] of owners) if (seen.size > 1) shared.add(label);
  return shared;
}

function boundaries(fixed, reach, lifted, count) {
  const kept = new Set(fixed);
  for (let round = 0; round < count; round += 1) {
    let added = false;
    let next = count;
    for (let at = count - 1; at >= 0; at -= 1) {
      if (kept.has(at)) {
        next = at;
        continue;
      }
      if (lifted.has(at)) continue;
      const to = reach.get(at);
      if (to !== undefined && to >= next) {
        kept.add(at);
        next = at;
        added = true;
      }
    }
    if (!added) break;
  }
  return kept;
}

function runsOf(block, reach, kept, lifted) {
  const count = block.statements.length;
  const runs = [];
  let start = 0;
  let end = -1;
  let held = 0;
  const close = (at) => {
    if (held && at > start) runs.push([start, at]);
    start = at + 1;
    end = at;
    held = 0;
  };
  for (let at = 0; at < count; at += 1) {
    if (kept.has(at)) {
      close(at - 1);
      start = at + 1;
      end = at;
      held = 0;
      continue;
    }
    if (!lifted.has(at)) {
      const to = reach.get(at);
      if (to !== undefined) {
        if (to > end) end = to;
        held += declaredCount(block.statements[at]);
      }
    }
    if (at >= end && at - start + 1 >= RUN) close(at);
  }
  close(count - 1);
  return runs;
}

function narrow(block, done) {
  if (done.has(block)) return 0;
  done.add(block);
  if (block.statements.length < RUN * 2) return 0;
  if (jumps(block)) return 0;
  const holder = sites(block);
  const reach = reachOf(block, holder);
  if (!reach.size) return 0;
  const shared = ambiguous(block);
  const lifted = new Set();
  const fixed = new Set();
  for (const [at, to] of reach) {
    if (to - at <= WINDOW) continue;
    const statement = block.statements[at];
    if (statement.kind !== Kind.LocalDeclaration
      || statement.names.some((label) => shared.has(label))) {
      fixed.add(at);
      continue;
    }
    lifted.add(at);
  }
  const kept = boundaries(fixed, reach, lifted, block.statements.length);
  for (const at of kept) lifted.delete(at);
  const runs = runsOf(block, reach, kept, lifted);
  if (!runs.length) return 0;
  const names = [];
  const rewritten = new Map();
  for (const at of lifted) {
    const statement = block.statements[at];
    for (const label of statement.names) names.push(label);
    rewritten.set(at, statement.expressions.length
      ? assignment(statement.names.map((label) => makeName(label)), statement.expressions)
      : null);
  }
  const out = [];
  if (names.length) out.push(localDecl(names));
  const put = (list, at) => {
    const statement = rewritten.has(at) ? rewritten.get(at) : block.statements[at];
    if (statement) list.push(statement);
  };
  let cursor = 0;
  for (const [from, to] of runs) {
    while (cursor < from) {
      put(out, cursor);
      cursor += 1;
    }
    const inner = [];
    while (cursor <= to) {
      put(inner, cursor);
      cursor += 1;
    }
    if (inner.length) out.push(doStatement(makeBlock(inner)));
  }
  while (cursor < block.statements.length) {
    put(out, cursor);
    cursor += 1;
  }
  block.statements = out;
  return runs.length;
}

function fit(chunk, resolve, limit = LIMIT) {
  let wrapped = 0;
  const bodies = [{ body: chunk.body, base: 0 }];
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Function) {
        bodies.push({ body: node.body, base: (node.params || []).length });
      }
      return undefined;
    },
  });
  const done = new Set();
  for (const holder of bodies) {
    for (let round = 0; round < 16; round += 1) {
      const seen = survey(holder.body, holder.base);
      if (seen.peak <= limit) break;
      const heavy = seen.blocks
        .filter((one) => !one.sealed && one.direct > 0 && !done.has(one.block))
        .sort((one, other) => other.direct - one.direct)[0];
      if (!heavy) break;
      const moved = narrow(heavy.block, done);
      if (!moved) continue;
      wrapped += moved;
      resolve();
    }
  }
  return wrapped;
}

module.exports = { fit, survey, LIMIT };
