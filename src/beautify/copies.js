'use strict';

const { Kind, isMultiValue } = require('../lua/ast');
const { walk, transform, collect, children } = require('../lua/walk');
const { Positions } = require('../util/order');
const { isLocalBinding } = require('../lua/scope');
const { bare } = require('../util/flow');
const services = require('./services');
const M = require('./moves');

function reachOf(binding) {
  if (!binding) return null;
  const declaration = binding.declaration;
  if (!declaration) return null;
  if (declaration.kind === Kind.LocalDeclaration) return 'after';
  if (declaration.kind === Kind.LocalFunction) return 'from';
  return 'inside';
}

function visibleAt(positions, binding, node) {
  const reach = reachOf(binding);
  if (!reach) return false;
  const declared = positions.path(binding.declaration);
  const wanted = positions.path(node);
  if (!declared || !wanted || wanted.depth < declared.depth) return false;
  let here = wanted;
  while (here.depth > declared.depth) here = here.up;
  if (here.up !== declared.up || here.block !== declared.block) return false;
  if (reach === 'after') return here.at > declared.at;
  if (reach === 'from') return here.at >= declared.at;
  return here.at === declared.at && wanted.depth > declared.depth;
}

function writeTable(chunk) {
  const table = new Map();
  const entry = (binding) => {
    let found = table.get(binding);
    if (!found) {
      found = { valued: 0, opaque: 0, empty: 0, value: null, at: null };
      table.set(binding, found);
    }
    return found;
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        const aligned = expressions.length === (node.names || []).length;
        (node.bindings || []).forEach((binding, at) => {
          if (!isLocalBinding(binding)) return;
          const found = entry(binding);
          if (!expressions.length) found.empty += 1;
          else if (aligned) {
            found.valued += 1;
            found.value = expressions[at];
            found.at = node;
          } else found.opaque += 1;
        });
      } else if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        const aligned = targets.length === expressions.length;
        targets.forEach((target, at) => {
          const named = bare(target);
          if (!named || named.kind !== Kind.Name || !isLocalBinding(named.binding)) return;
          const found = entry(named.binding);
          if (aligned) {
            found.valued += 1;
            found.value = expressions[at];
            found.at = node;
          } else found.opaque += 1;
        });
      } else if (node.kind === Kind.LocalFunction) {
        const found = entry(node.binding);
        found.valued += 1;
        found.value = null;
        found.at = node;
      } else if (node.kind === Kind.FunctionDeclaration) {
        const named = bare(node.target);
        if (named && named.kind === Kind.Name && isLocalBinding(named.binding)) {
          const found = entry(named.binding);
          found.valued += 1;
          found.value = null;
          found.at = node;
        }
      } else if (node.kind === Kind.NumericFor || node.kind === Kind.GenericFor
        || node.kind === Kind.Function) {
        for (const binding of node.bindings || []) {
          if (isLocalBinding(binding)) entry(binding).opaque += 1;
        }
      }
      return undefined;
    },
  });
  return table;
}

function readsOf(binding) {
  return (binding && binding.reads) || [];
}

function parentTable(chunk) {
  const parents = new Map();
  walk(chunk, {
    enter(node) {
      for (const child of children(node)) parents.set(child.node, node);
      return undefined;
    },
  });
  return parents;
}

function statementOf(parents, node) {
  let current = node;
  let above = parents.get(current);
  while (above && above.kind !== Kind.Block) {
    current = above;
    above = parents.get(current);
  }
  return above ? current : null;
}

function functionNamed(statement, value) {
  if (!statement) return null;
  if (statement.kind === Kind.LocalFunction) {
    return statement.body === value ? statement.binding : null;
  }
  const expressions = statement.expressions || [];
  if (expressions.length !== 1 || bare(expressions[0]) !== value) return null;
  if (statement.kind === Kind.LocalDeclaration) {
    return (statement.names || []).length === 1 ? (statement.bindings || [])[0] : null;
  }
  if (statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  if (targets.length !== 1) return null;
  const target = bare(targets[0]);
  return target && target.kind === Kind.Name ? target.binding : null;
}

function handedOver(write, named) {
  const harmless = new Set();
  for (const expression of (write && write.expressions) || []) {
    const value = bare(expression);
    if (value && value.kind === Kind.Name && value.binding === named) harmless.add(value);
  }
  return harmless;
}

function sealed(positions, named, made, write) {
  if (!isLocalBinding(named) || named.declaration !== made) return false;
  const madeAt = positions.path(made);
  const writeAt = positions.path(write);
  if (!madeAt || !writeAt || madeAt.depth !== writeAt.depth) return false;
  if (madeAt.up !== writeAt.up) return false;
  const block = madeAt.block;
  if (block !== writeAt.block) return false;
  const from = madeAt.at;
  const to = writeAt.at;
  if (from >= to) return false;
  const statements = block.statements || [];

  if (statements.some((statement) => statement.kind === Kind.Label)) return false;
  const harmless = handedOver(write, named);
  for (let i = from + 1; i <= to; i += 1) {
    const said = collect(statements[i],
      (node) => node.kind === Kind.Name && node.binding === named);
    if (i === to ? said.some((node) => !harmless.has(node)) : said.length) return false;
  }
  return true;
}

function filledBefore(parents, positions, read, write) {
  const writeAt = positions.path(write);
  if (!writeAt) return false;
  const home = writeAt.block;
  let current = parents.get(read);
  while (current) {
    if (current.kind === Kind.Function) {
      const made = statementOf(parents, current);
      const spot = made ? positions.path(made) : null;
      if (spot && spot.depth === writeAt.depth && spot.block === home) {
        const named = functionNamed(made, current);
        return !!named && sealed(positions, named, made, write);
      }
    }
    current = parents.get(current);
  }
  return false;
}

function settledOnce(positions, binding, info, parents) {
  if (!info || info.valued !== 1 || info.opaque) return false;
  const reads = readsOf(binding);
  if (!reads.length) return false;
  if (!info.empty) return true;
  return reads.every((read) => read === info.at || positions.precedes(info.at, read)
    || (parents && filledBefore(parents, positions, read, info.at)));
}

function heldBy(parents, node) {
  let current = parents.get(node);
  while (current) {
    if (current.kind === Kind.Function) return current;
    current = parents.get(current);
  }
  return null;
}

function loopsOver(parents, node) {
  const found = new Set();
  let current = node;
  while (current) {
    if (current.kind === Kind.While || current.kind === Kind.Repeat
      || current.kind === Kind.NumericFor || current.kind === Kind.GenericFor) found.add(current);
    current = parents.get(current);
  }
  return found;
}

function rewritten(parents, positions, from, copy) {
  const around = loopsOver(parents, copy);
  const nodes = (from.writes || []).slice();
  const made = from.declaration;
  if (made && (made.kind === Kind.NumericFor || made.kind === Kind.GenericFor)) nodes.push(made);
  for (const node of nodes) {
    for (const loop of loopsOver(parents, node)) if (around.has(loop)) return true;
    if (node !== copy && !positions.precedes(node, copy)) return true;
  }
  return false;
}

function propagate(chunk) {
  const positions = new Positions(chunk);
  const parents = parentTable(chunk);
  const writes = writeTable(chunk);
  const names = M.nameCounts(chunk);
  const replacements = new Map();

  for (const [binding, info] of writes) {
    if (!settledOnce(positions, binding, info, parents)) continue;
    const source = bare(info.value);
    if (!source || source.kind !== Kind.Name) continue;
    const from = source.binding;
    if (!isLocalBinding(from) || from === binding) continue;
    if (!M.unshadowed(names, from.name)) continue;
    const above = writes.get(from);

    if (above && above.valued > 1) continue;
    if (above && above.opaque > 1) continue;
    if (above && above.valued === 1 && above.at !== info.at
      && !positions.precedes(above.at, info.at)) continue;
    const reads = readsOf(binding);
    if (!reads.every((read) => visibleAt(positions, from, read))) continue;
    if (reads.some((read) => heldBy(parents, read) !== heldBy(parents, info.at))
      && rewritten(parents, positions, from, info.at)) continue;
    replacements.set(binding, from);
  }
  if (!replacements.size) return 0;

  const finalOf = (binding) => {
    let current = binding;
    for (let guard = 0; guard < 1000 && replacements.has(current); guard += 1) {
      current = replacements.get(current);
    }
    return current;
  };

  let moved = 0;
  const stored = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Assignment) return undefined;
      for (const target of node.targets || []) {
        const named = bare(target);
        if (named && named.kind === Kind.Name) stored.add(named);
      }
      return undefined;
    },
  });
  transform(chunk, (node) => {
    if (node.kind !== Kind.Name || !node.binding || stored.has(node)) return node;
    if (!replacements.has(node.binding)) return node;
    const from = finalOf(node.binding);
    if (from === node.binding) return node;
    moved += 1;
    return { kind: Kind.Name, name: from.name, binding: from };
  });
  return moved;
}

function nextOf(statements, at) {
  for (let i = at + 1; i < statements.length; i += 1) {
    if (!M.isEmptyDo(statements[i])) return i;
  }
  return -1;
}

function holderOf(root, wanted) {
  let found = null;
  walk(root, {
    enter(node, info) {
      if (node === wanted && info) found = info.parent;
      return undefined;
    },
  });
  return found;
}

function readsInto(host, read) {
  const holder = holderOf(host, read);
  if (!holder || !holder.kind) return false;
  if (holder.kind === Kind.Unary || holder.kind === Kind.Binary) return true;
  if (holder.kind === Kind.Index) return true;
  if (holder.kind === Kind.Call || holder.kind === Kind.MethodCall) {
    return bare(holder.base) === read || holder.base === read;
  }
  return false;
}

function declaredFunction(statement) {
  if (!statement || statement.kind !== Kind.LocalFunction) return null;
  const binding = statement.binding;
  if (!binding || !statement.body) return null;
  if (collect(statement.body, (node) => node.kind === Kind.Name
    && node.name === statement.name).length) return null;
  return { binding, name: statement.name, value: statement.body };
}

function holdsRead(host, read) {
  let found = false;
  const visit = (node) => {
    if (found || !node || !node.kind || node.kind === Kind.Block) return;
    if (node === read) {
      found = true;
      return;
    }
    for (const child of children(node)) visit(child.node);
  };
  visit(host);
  return found;
}

function inlineBelow(block, at) {
  const statements = block.statements;
  const written = M.plainWrite(statements[at]) || M.plainDeclaration(statements[at])
    || declaredFunction(statements[at]);
  if (!written) return false;
  const binding = written.binding || written.target.binding;
  if (!isLocalBinding(binding)) return false;

  if (services.isLookup(written.value)) return false;
  const reads = readsOf(binding);
  if (reads.length !== 1) return false;
  const below = nextOf(statements, at);
  if (below < 0) return false;
  const read = reads[0];
  const host = statements[below];
  if (host.kind === Kind.While || host.kind === Kind.Repeat) return false;

  if (host.kind === Kind.Assignment
    && (host.targets || []).some((target) => collect(target, (node) => node === read).length)) {
    return false;
  }

  if (!holdsRead(host, read)) return false;
  if (!M.reachesQuietly(host, read)) return false;
  const held = bare(written.value);
  if (held && (held.kind === Kind.Table || held.kind === Kind.Function)
    && readsInto(host, read)) return false;

  const value = isMultiValue(bare(written.value))
    ? { kind: Kind.Paren, expression: written.value }
    : written.value;
  transform(host, (node) => (node === read ? value : node));
  statements[at] = { kind: Kind.Do, body: { kind: Kind.Block, statements: [] } };
  return true;
}

function inlineTemps(chunk) {
  let moved = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let at = 0; at < node.statements.length; at += 1) {
        if (inlineBelow(node, at)) moved += 1;
      }
      return undefined;
    },
  });
  return moved;
}

module.exports = {
  reachOf,
  visibleAt,
  parentTable,
  sealed,
  rewritten,
  propagate,
  declaredFunction,
  holderOf,
  readsInto,
  inlineTemps,
};
