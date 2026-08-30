'use strict';

const A = require('../lua/ast');
const { Kind } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');
const { diverges, divergesBlock } = require('../util/flow');

const TAILS = 8;

const LOOPS = new Set([Kind.While, Kind.Repeat, Kind.NumericFor, Kind.GenericFor]);

const EXITS = new Set([Kind.Return, Kind.Break, Kind.Continue]);

function rootsOf(chunk) {
  const roots = [];
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Chunk) roots.push(node.body);
      else if (node.kind === Kind.Function) roots.push(node.body);
      return undefined;
    },
  });
  return roots;
}

function survey(root) {
  const after = new Map();
  const holder = new Map();
  const labels = new Map();
  const gotos = [];
  const leave = { kind: 'leave' };

  const visitBlock = (block, exit) => {
    const statements = (block && block.statements) || [];
    for (let at = 0; at < statements.length; at += 1) {
      const statement = statements[at];
      let ahead = at + 1;
      while (ahead < statements.length && statements[ahead].kind === Kind.Label) ahead += 1;
      const next = ahead < statements.length
        ? { kind: 'statement', node: statements[ahead] }
        : exit;
      after.set(statement, next);
      holder.set(statement, statements);
      if (statement.kind === Kind.Label) labels.set(statement.name, statement);
      else if (statement.kind === Kind.Goto) gotos.push(statement);
      if (statement.kind === Kind.If) {
        visitBlock(statement.body, next);
        for (const clause of statement.elseIfs || []) visitBlock(clause.body, next);
        if (statement.elseBody) visitBlock(statement.elseBody, next);
      } else if (statement.kind === Kind.Do) {
        visitBlock(statement.body, next);
      } else if (LOOP_KINDS.has(statement.kind)) {
        visitBlock(statement.body, { kind: 'loop', node: statement });
      }
    }
  };

  visitBlock(root, leave);
  return { after, holder, labels, gotos };
}

function same(one, other) {
  if (!one || !other) return false;
  if (one === other) return true;
  if (one.kind !== other.kind) return false;
  return one.node === other.node;
}

function drop(statements, statement) {
  const at = statements.indexOf(statement);
  if (at < 0) return false;
  statements.splice(at, 1);
  return true;
}

function replace(statements, statement, replacement) {
  const at = statements.indexOf(statement);
  if (at < 0) return false;
  statements[at] = replacement;
  return true;
}

function unreachable(statements, statement) {
  const at = statements.indexOf(statement);
  if (at <= 0) return false;
  const before = statements[at - 1];
  if (before.kind === Kind.Label) return false;
  if (before.kind === Kind.Goto) return true;
  return LEAVING_KINDS.has(before.kind) || diverges(before);
}


function copyOf(node) {
  if (Array.isArray(node)) return node.map(copyOf);
  if (!node || typeof node !== 'object') return node;
  const copy = {};
  for (const key of Object.keys(node)) {
    if (key === 'binding' || key === 'bindings') continue;
    copy[key] = copyOf(node[key]);
  }
  return copy;
}

function holds(node, target) {
  let found = false;
  walk(node, {
    enter(one) {
      if (one === target) found = true;
      return undefined;
    },
  });
  return found;
}

function sibling(statement, into) {
  if (statement.kind === Kind.LocalDeclaration) {
    for (const binding of statement.bindings || []) if (binding) into.add(binding);
  } else if (statement.kind === Kind.LocalFunction && statement.binding) {
    into.add(statement.binding);
  }
}

function entering(statement, into) {
  if (statement.kind === Kind.NumericFor && statement.binding) into.add(statement.binding);
  else if (statement.kind === Kind.GenericFor) {
    for (const binding of statement.bindings || []) if (binding) into.add(binding);
  }
}

function bodiesOf(statement) {
  if (statement.kind === Kind.If) {
    const found = [statement.body];
    for (const clause of statement.elseIfs || []) found.push(clause.body);
    if (statement.elseBody) found.push(statement.elseBody);
    return found;
  }
  if (statement.kind === Kind.Do || LOOP_KINDS.has(statement.kind)) return [statement.body];
  return [];
}

function visibleAt(root, jump) {
  const live = new Set();
  const scan = (block) => {
    for (const statement of block.statements || []) {
      if (statement === jump) return true;
      if (holds(statement, jump)) {
        entering(statement, live);
        for (const body of bodiesOf(statement)) {
          if (body && holds(body, jump)) return scan(body);
        }
        return false;
      }
      sibling(statement, live);
    }
    return false;
  };
  return scan(root) ? live : null;
}

function declaredIn(statements) {
  const found = new Set();
  for (const statement of statements) {
    walk(statement, {
      enter(one) {
        sibling(one, found);
        entering(one, found);
        if (one.kind === Kind.Function) {
          for (const binding of one.bindings || []) if (binding) found.add(binding);
        }
        return undefined;
      },
    });
  }
  return found;
}

function leaves(block, depth = 0) {
  const statements = (block && block.statements) || [];
  if (!statements.length || depth > 48) return false;
  const last = statements[statements.length - 1];
  if (last.kind === Kind.Return) return true;
  if (last.kind === Kind.Do) return leaves(last.body, depth + 1);
  if (last.kind === Kind.If) {
    if (!last.elseBody || !leaves(last.body, depth + 1)) return false;
    for (const clause of last.elseIfs || []) {
      if (!leaves(clause.body, depth + 1)) return false;
    }
    return leaves(last.elseBody, depth + 1);
  }
  return divergesBlock(block, depth + 1);
}

function tailOf(statements, label) {
  const at = statements.indexOf(label);
  if (at < 0) return null;
  const tail = statements.slice(at + 1);
  if (!tail.length || tail.length > TAIL_STATEMENTS) return null;
  if (!leaves({ kind: Kind.Block, statements: tail })) return null;
  let nodes = 0;
  for (const statement of tail) {
    for (const one of collect(statement, () => true)) {
      if (one.kind === Kind.Goto || one.kind === Kind.Label) return null;
      if (one.kind === Kind.Break || one.kind === Kind.Continue) return null;
      nodes += 1;
    }
  }
  return nodes > TAIL_NODES ? null : tail;
}

function movable(root, jump, tail) {
  const visible = visibleAt(root, jump);
  if (!visible) return false;
  const inside = declaredIn(tail);
  const used = new Set();
  for (const statement of tail) {
    walk(statement, {
      enter(one) {
        if (one.kind === Kind.Name && one.binding) used.add(one.binding);
        return undefined;
      },
    });
  }
  const local = new Set();
  for (const statement of root.statements || []) {
    walk(statement, {
      enter(one) {
        sibling(one, local);
        entering(one, local);
        return undefined;
      },
    });
  }
  for (const binding of used) {
    if (inside.has(binding) || visible.has(binding)) continue;
    if (local.has(binding)) return false;
  }
  return true;
}

function copyableReturn(statement) {
  if (!statement || statement.kind !== Kind.Return) return null;
  const expressions = statement.expressions || [];
  const plain = expressions.every((value) => {
    const bare = A.unparen(value);
    return bare.kind === Kind.Name || A.LITERALS.has(bare.kind);
  });
  if (!plain) return null;
  return A.returnStatement(expressions.map((value) => copyOf(value)));
}
function lastOf(block) {
  const statements = (block && block.statements) || [];
  return statements.length ? statements[statements.length - 1] : null;
}

function stops(block) {
  const last = lastOf(block);
  if (last && (LEAVING_KINDS.has(last.kind) || last.kind === Kind.Goto)) return true;
  return leaves(block);
}

function jumpsTo(block, name) {
  const last = lastOf(block);
  return last && last.kind === Kind.Goto && last.label === name ? last : null;
}

function namesIn(statements) {
  const found = new Set();
  for (const statement of statements) {
    if (statement.kind === Kind.LocalDeclaration) {
      for (const name of statement.names || []) found.add(name);
    } else if (statement.kind === Kind.LocalFunction && statement.name) {
      found.add(statement.name);
    }
  }
  return found;
}

function readsIn(statements) {
  const found = new Set();
  for (const statement of statements) {
    walk(statement, {
      enter(one) {
        if (one.kind === Kind.Name && one.binding) found.add(one.binding);
        return undefined;
      },
    });
  }
  return found;
}

function ownersOf(root) {
  const owners = new Map();
  const blocks = new Map();
  const note = (block) => {
    for (const one of (block && block.statements) || []) blocks.set(one, block);
  };
  note(root);
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Function) return false;
      for (const body of bodiesOf(node)) {
        if (!body) continue;
        owners.set(body, node);
        note(body);
      }
      return undefined;
    },
  });
  return { owners, blocks };
}

function climb(label, wanted, owners, blocks) {
  const dropping = new Set();
  let block = blocks.get(label);
  let mark = label;
  for (let level = 0; level < 64; level += 1) {
    const owner = owners.get(block);
    if (!owner) return null;
    const above = blocks.get(owner);
    if (!above) return null;
    const list = above.statements || [];
    if (list[list.length - 1] !== owner) return null;
    if (owner.kind === Kind.If) {
      if (!owner.elseBody) return null;
      for (const other of bodiesOf(owner)) {
        if (other === block) continue;
        const jump = jumpsTo(other, label.name);
        if (jump) {
          dropping.add(jump);
          continue;
        }
        if (!stops(other)) return null;
      }
    } else if (owner.kind !== Kind.Do) return null;
    mark = owner;
    block = above;
    if (dropping.size === wanted) return { seat: owner, list, dropping };
  }
  return null;
}

function spill(label, gotos, owners, blocks) {
  const statements = (blocks.get(label) || {}).statements || [];
  const at = statements.indexOf(label);
  if (at < 0) return false;
  const tail = statements.slice(at + 1);
  if (!tail.length) return false;
  const wanted = gotos.filter((jump) => jump.label === label.name);
  if (!wanted.length) return false;
  const reached = climb(label, wanted.length, owners, blocks);
  if (!reached) return false;
  for (const jump of wanted) if (!reached.dropping.has(jump)) return false;
  const held = new Set();
  const inner = new Set();
  for (const one of tail) {
    for (const node of collect(one, (found) => found.kind === Kind.Label)) {
      held.add(node.name);
      inner.add(node);
    }
    for (const node of collect(one, (found) => found.kind === Kind.Goto)) inner.add(node);
  }
  for (const jump of gotos) {
    if (inner.has(jump) || reached.dropping.has(jump)) continue;
    if (held.has(jump.label)) return false;
  }
  const outside = collect(reached.seat, (found) => found.kind === Kind.Label)
    .filter((found) => !inner.has(found) && found !== label);
  for (const node of inner) {
    if (node.kind !== Kind.Goto) continue;
    if (outside.some((found) => found.name === node.label)) return false;
  }
  const inside = declaredIn(tail);
  const blocked = declaredIn([reached.seat]);
  for (const binding of inside) blocked.delete(binding);
  for (const binding of readsIn(tail)) {
    if (!inside.has(binding) && blocked.has(binding)) return false;
  }
  const seat = reached.list.indexOf(reached.seat);
  if (seat < 0) return false;
  const shadowing = namesIn(tail);
  if (shadowing.size) {
    for (let index = seat + 1; index < reached.list.length; index += 1) {
      for (const node of collect(reached.list[index], (found) => found.kind === Kind.Name)) {
        if (shadowing.has(node.name)) return false;
      }
    }
  }
  statements.splice(at, tail.length + 1);
  for (const jump of reached.dropping) {
    const list = (blocks.get(jump) || {}).statements;
    if (list) list.splice(list.indexOf(jump), 1);
  }
  reached.list.splice(seat + 1, 0, ...tail);
  return true;
}

function pull(chunk) {
  let pulled = 0;
  for (const root of rootsOf(chunk)) {
    for (let round = 0; round < 64; round += 1) {
      const { gotos } = survey(root);
      if (!gotos.length) break;
      const { owners, blocks } = ownersOf(root);
      let moved = false;
      for (const label of collect(root, (node) => node.kind === Kind.Label)) {
        if (!blocks.has(label)) continue;
        if (!spill(label, gotos, owners, blocks)) continue;
        moved = true;
        break;
      }
      if (!moved) break;
      pulled += 1;
    }
  }
  return pulled;
}

function clean(chunk) {
  let cleaned = 0;
  for (const root of rootsOf(chunk)) {
    const { after, holder, labels, gotos } = survey(root);
    if (!gotos.length && !labels.size) continue;
    for (const jump of gotos) {
      const statements = holder.get(jump);
      if (!statements) continue;
      if (unreachable(statements, jump)) {
        if (drop(statements, jump)) cleaned += 1;
        continue;
      }
      const label = labels.get(jump.label);
      if (!label) continue;
      const target = after.get(label);
      if (same(target, after.get(jump))) {
        if (drop(statements, jump)) cleaned += 1;
        continue;
      }
      if (target && target.kind === 'leave') {
        if (replace(statements, jump, A.returnStatement([]))) cleaned += 1;
        continue;
      }
      if (target && target.kind === 'statement') {
        const returned = copyableReturn(target.node);
        if (returned && movable(root, jump, [target.node])
          && replace(statements, jump, returned)) {
          cleaned += 1;
          continue;
        }
        const tail = tailOf(holder.get(label) || [], label);
        if (!tail || !movable(root, jump, tail)) continue;
        const at = statements.indexOf(jump);
        if (at < 0) continue;
        statements.splice(at, 1, ...tail.map(copyOf));
        cleaned += 1;
      }
    }

    const named = new Set();
    walk(root, {
      enter(node) {
        if (node.kind === Kind.Function) return false;
        if (node.kind === Kind.Goto) named.add(node.label);
        return undefined;
      },
    });
    for (const [name, label] of labels) {
      if (named.has(name)) continue;
      const statements = holder.get(label);
      if (statements && drop(statements, label)) cleaned += 1;
    }
  }
  return cleaned;
}

module.exports = {
  copyOf,
  leaves,
  visibleAt,
  movable,
  survey,
  same,
  unreachable,
  stops,
  pull,
  clean,
};
