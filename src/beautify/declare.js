'use strict';

const { Kind } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');
const { isIdentifier } = require('../lua/format');
const { isLocalBinding } = require('../lua/scope');
const { bare } = require('../util/flow');
const { Positions } = require('../util/order');
const { visibleAt } = require('./copies');
const M = require('./moves');

function hasLabel(block) {
  return (block.statements || []).some((statement) => statement.kind === Kind.Label);
}

function mentions(root, binding) {
  return collect(root, (node) => node.kind === Kind.Name && node.binding === binding);
}

function mentionSpots(block, own) {
  const spots = new Map();
  (block.statements || []).forEach((statement, at) => {
    walk(statement, {
      enter(node) {
        if (own && node.kind === Kind.Function) return false;
        if (node.kind !== Kind.Name || !node.binding) return undefined;
        const rows = spots.get(node.binding);
        if (!rows) spots.set(node.binding, [{ at, nodes: [node] }]);
        else if (rows[rows.length - 1].at === at) rows[rows.length - 1].nodes.push(node);
        else rows.push({ at, nodes: [node] });
        return undefined;
      },
    });
  });
  return spots;
}

function spotsOf(cache, block) {
  const kept = cache && cache.get(block);
  if (kept) return kept;
  const spots = mentionSpots(block, true);
  if (cache) cache.set(block, spots);
  return spots;
}

function firstMention(spots, binding, after) {
  for (const row of spots.get(binding) || []) {
    if (row.at > after) return row;
  }
  return null;
}

function sinkable(block) {
  const statements = block.statements || [];
  const wanted = new Map();
  if (hasLabel(block)) return wanted;
  let spots = null;
  statements.forEach((statement, at) => {
    if (statement.kind !== Kind.LocalDeclaration) return;
    if ((statement.expressions || []).length) return;
    (statement.bindings || []).forEach((binding, slot) => {
      if (!isLocalBinding(binding)) return;
      if (!spots) spots = mentionSpots(block);
      const first = firstMention(spots, binding, at);
      if (!first) return;
      const host = statements[first.at];
      if (host.kind !== Kind.Assignment) return;
      const targets = (host.targets || []).map((target) => bare(target));
      const stores = first.nodes.filter((node) => targets.indexOf(node) >= 0);
      if (stores.length !== first.nodes.length || stores.length !== 1) return;
      let list = wanted.get(first.at);
      if (!list) {
        list = [];
        wanted.set(first.at, list);
      }
      list.push({ binding, declaration: statement, slot, target: stores[0] });
    });
  });
  return wanted;
}

function rebind(binding, declaration, dropped) {
  binding.declaration = declaration;
  binding.initializer = declaration;
  const at = binding.writes.indexOf(dropped);
  if (at >= 0) binding.writes.splice(at, 1);
}

function sink(chunk) {
  let sunk = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const wanted = sinkable(node);
      for (const [at, list] of wanted) {
        const host = node.statements[at];
        const targets = (host.targets || []).map((target) => bare(target));
        if (targets.length !== list.length) continue;
        const order = targets.map((target) => list.find((one) => one.target === target));
        if (order.some((one) => !one)) continue;
        const declaration = {
          kind: Kind.LocalDeclaration,
          names: order.map((one) => one.binding.name),
          expressions: host.expressions || [],
          bindings: order.map((one) => one.binding),
        };
        node.statements[at] = declaration;
        for (const one of order) {
          const names = one.declaration.names || [];
          const slot = names.indexOf(one.binding.name);
          if (slot >= 0) {
            names.splice(slot, 1);
            (one.declaration.bindings || []).splice(slot, 1);
          }
          rebind(one.binding, declaration, one.target);
          sunk += 1;
        }
      }
      return undefined;
    },
  });
  return sunk;
}

function slidable(block) {
  const statements = block.statements || [];
  const wanted = new Map();
  if (hasLabel(block)) return wanted;
  let spots = null;
  statements.forEach((statement, at) => {
    if (statement.kind !== Kind.LocalDeclaration) return;
    if ((statement.expressions || []).length) return;
    (statement.bindings || []).forEach((binding) => {
      if (!isLocalBinding(binding)) return;
      if (!spots) spots = mentionSpots(block);
      const first = firstMention(spots, binding, at);

      if (!first || first.at === at + 1) return;
      for (let i = at + 1; i < first.at; i += 1) {
        if (!silentAbout(statements[i], binding.name)) return;
      }
      let list = wanted.get(first.at);
      if (!list) {
        list = [];
        wanted.set(first.at, list);
      }
      list.push({ binding, declaration: statement });
    });
  });
  return wanted;
}

function slide(chunk) {
  let slid = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const wanted = slidable(node);
      if (!wanted.size) return undefined;
      const out = [];
      node.statements.forEach((statement, at) => {
        const list = wanted.get(at);
        if (list && list.length) {
          const declaration = {
            kind: Kind.LocalDeclaration,
            names: list.map((one) => one.binding.name),
            expressions: [],
            bindings: list.map((one) => one.binding),
          };
          for (const one of list) {
            const names = one.declaration.names || [];
            const slot = names.indexOf(one.binding.name);
            if (slot >= 0) {
              names.splice(slot, 1);
              (one.declaration.bindings || []).splice(slot, 1);
            }
            one.binding.declaration = declaration;
            one.binding.initializer = declaration;
            slid += 1;
          }
          out.push(declaration);
        }
        out.push(statement);
      });
      node.statements = out;
      return undefined;
    },
  });
  return slid;
}

function innerBlock(root, nodes) {
  const wanted = new Set(nodes);
  const stack = [];
  let common = null;
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Block) stack.push(node);
      if (!wanted.has(node)) return undefined;
      if (!common) common = [...stack];
      else {
        let depth = 0;
        while (depth < common.length && common[depth] === stack[depth]) depth += 1;
        common.length = depth;
      }
      return undefined;
    },
    leave(node) {
      if (node.kind === Kind.Block) stack.pop();
    },
  });
  return common && common.length ? common[common.length - 1] : null;
}

function ownBlocks(root) {
  const found = new Set();
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Function) return false;
      if (node.kind === Kind.Block) found.add(node);
      return undefined;
    },
  });
  return found;
}

function mentionsIn(root) {
  const index = new Map();
  const stack = [];
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Block) {
        stack.push(node);
      } else if (node.kind === Kind.Name && node.binding) {
        const row = index.get(node.binding);
        if (!row) {
          index.set(node.binding, { nodes: [node], path: stack.slice() });
        } else {
          row.nodes.push(node);
          let depth = 0;
          while (depth < row.path.length && row.path[depth] === stack[depth]) depth += 1;
          row.path.length = depth;
        }
      }
      return undefined;
    },
    leave(node) {
      if (node.kind === Kind.Block) stack.pop();
    },
  });
  return index;
}

function pushable(home, index, cache) {
  const statements = home.statements || [];
  const plans = [];
  if (hasLabel(home)) return plans;
  if (!statements.some((statement) => statement.kind === Kind.LocalDeclaration
    && !(statement.expressions || []).length)) return plans;
  let inside = null;
  statements.forEach((statement) => {
    if (statement.kind !== Kind.LocalDeclaration) return;
    if ((statement.expressions || []).length) return;
    (statement.bindings || []).forEach((binding) => {
      if (!isLocalBinding(binding)) return;
      const row = index ? index.get(binding) : null;
      const found = row ? row.nodes : mentions(home, binding);
      if (!found.length) return;
      const target = row ? row.path[row.path.length - 1] : innerBlock(home, found);
      if (!inside) inside = ownBlocks(home);
      if (!target || target === home || !inside.has(target)) return;
      if (hasLabel(target)) return;
      const rows = spotsOf(cache, target).get(binding) || [];
      let own = 0;
      for (const row of rows) own += row.nodes.length;
      if (own !== found.length) return;
      const first = rows[0];
      if (!first) return;
      const host = (target.statements || [])[first.at];
      if (!host || host.kind !== Kind.Assignment) return;
      const targets = (host.targets || []).map((one) => bare(one));
      const stores = first.nodes.filter((node) => targets.indexOf(node) >= 0);
      if (stores.length !== 1 || stores.length !== first.nodes.length) return;
      plans.push({
        binding, declaration: statement, target, at: first.at,
      });
    });
  });
  return plans;
}

function pushIn(chunk) {
  const plans = [];
  const index = mentionsIn(chunk);
  const cache = new Map();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Block) plans.push(...pushable(node, index, cache));
      return undefined;
    },
  });
  if (!plans.length) return 0;
  const rows = new Map();
  for (const plan of plans) {
    let list = rows.get(plan.target);
    if (!list) {
      list = new Map();
      rows.set(plan.target, list);
    }
    let row = list.get(plan.at);
    if (!row) {
      row = [];
      list.set(plan.at, row);
    }
    row.push(plan);
  }
  let pushed = 0;
  for (const [target, list] of rows) {
    for (const at of [...list.keys()].sort((a, b) => b - a)) {
      const row = list.get(at);
      const declaration = {
        kind: Kind.LocalDeclaration,
        names: row.map((one) => one.binding.name),
        expressions: [],
        bindings: row.map((one) => one.binding),
      };
      for (const one of row) {
        const names = one.declaration.names || [];
        const slot = names.indexOf(one.binding.name);
        if (slot >= 0) {
          names.splice(slot, 1);
          (one.declaration.bindings || []).splice(slot, 1);
        }
        one.binding.declaration = declaration;
        one.binding.initializer = declaration;
        pushed += 1;
      }
      target.statements.splice(at, 0, declaration);
    }
  }
  return pushed;
}

function harmless(statement) {
  if (statement.kind === Kind.LocalFunction) return true;
  if (statement.kind === Kind.LocalDeclaration) {
    return (statement.expressions || []).every((one) => M.quiet(one));
  }
  if (statement.kind !== Kind.Assignment) return false;
  return (statement.targets || []).every((one) => {
    const named = bare(one);
    return named && named.kind === Kind.Name && isLocalBinding(named.binding);
  }) && (statement.expressions || []).every((one) => M.quiet(one));
}

function writesAny(statement, wanted) {
  return collect(statement, (node) => node.kind === Kind.Assignment
    && (node.targets || []).some((one) => {
      const named = bare(one);
      return named && named.kind === Kind.Name && wanted.has(named.binding);
    })).length > 0;
}

function fillable(block, positions) {
  const statements = block.statements || [];
  const plans = [];
  if (hasLabel(block)) return plans;
  let spots = null;
  statements.forEach((statement, at) => {
    if (statement.kind !== Kind.LocalDeclaration) return;
    if ((statement.expressions || []).length) return;
    (statement.bindings || []).forEach((binding) => {
      if (!isLocalBinding(binding)) return;
      if (!spots) spots = mentionSpots(block, true);
      const first = firstMention(spots, binding, at);
      if (!first) return;
      const to = first.at;
      const store = statements[to];
      if (store.kind !== Kind.Assignment) return;
      if ((store.targets || []).length !== 1 || (store.expressions || []).length !== 1) return;
      const stored = bare(store.targets[0]);
      if (!stored || stored.kind !== Kind.Name || stored.binding !== binding) return;
      if (first.nodes.length !== 1) return;
      const value = store.expressions[0];
      if (!M.quiet(value)) return;
      const read = collect(value, (node) => node.kind === Kind.Name);
      if (!read.every((node) => isLocalBinding(node.binding)
        && visibleAt(positions, node.binding, statement))) return;
      const wanted = new Set(read.map((node) => node.binding));
      for (let i = at + 1; i < to; i += 1) {
        if (!harmless(statements[i]) || writesAny(statements[i], wanted)) return;
      }
      plans.push({ binding, declaration: statement, store, value, block });
    });
  });
  return plans;
}

function fill(chunk) {
  const positions = new Positions(chunk);
  const plans = [];
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Block) plans.push(...fillable(node, positions));
      return undefined;
    },
  });
  if (!plans.length) return 0;
  const rows = new Map();
  for (const plan of plans) {
    if (!rows.has(plan.block)) rows.set(plan.block, []);
    rows.get(plan.block).push(plan);
  }
  let filled = 0;
  for (const [block, list] of rows) {
    const dropped = new Set(list.map((one) => one.store));
    const above = new Map();
    for (const plan of list) {
      const declaration = {
        kind: Kind.LocalDeclaration,
        names: [plan.binding.name],
        expressions: [plan.value],
        bindings: [plan.binding],
      };
      const names = plan.declaration.names || [];
      const slot = names.indexOf(plan.binding.name);
      if (slot >= 0) {
        names.splice(slot, 1);
        (plan.declaration.bindings || []).splice(slot, 1);
      }
      rebind(plan.binding, declaration, bare(plan.store.targets[0]));
      if (!above.has(plan.declaration)) above.set(plan.declaration, []);
      above.get(plan.declaration).push(declaration);
      filled += 1;
    }
    const kept = [];
    for (const statement of block.statements || []) {
      const added = above.get(statement);
      if (added) kept.push(...added);
      if (!dropped.has(statement)) kept.push(statement);
    }
    block.statements = kept;
  }
  return filled;
}

function dropEmpty(chunk) {
  let dropped = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const kept = node.statements.filter((statement) => {
        const empty = statement.kind === Kind.LocalDeclaration
          && !(statement.names || []).length;
        if (empty) dropped += 1;
        return !empty;
      });
      node.statements = kept;
      return undefined;
    },
  });
  return dropped;
}

function silentAbout(root, text) {
  return !collect(root, (node) => node.kind === Kind.Name && node.name === text).length;
}

function recursiveForm(chunk) {
  let restored = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block || hasLabel(node)) return undefined;
      const statements = node.statements;
      let spots = null;
      statements.forEach((statement, at) => {
        if (statement.kind !== Kind.LocalDeclaration) return;
        if ((statement.expressions || []).length) return;
        for (const binding of [...(statement.bindings || [])]) {
          if (!isLocalBinding(binding) || !isIdentifier(binding.name)) continue;
          if (!spots) spots = mentionSpots(node);
          const first = firstMention(spots, binding, at);
          if (!first) continue;
          const host = statements[first.at];
          if (host.kind !== Kind.Assignment) continue;
          if ((host.targets || []).length !== 1 || (host.expressions || []).length !== 1) continue;
          if (bare(host.targets[0]) !== first.nodes[0]) continue;
          const value = bare(host.expressions[0]);
          if (!value || value.kind !== Kind.Function) continue;

          if (mentions(value.body, binding).length !== first.nodes.length - 1) continue;
          let clear = true;
          for (let i = at + 1; i < first.at; i += 1) {
            if (!silentAbout(statements[i], binding.name)) clear = false;
          }
          if (!clear) continue;
          const declaration = {
            kind: Kind.LocalFunction,
            name: binding.name,
            body: value,
            binding,
          };
          statements[first.at] = declaration;
          const names = statement.names || [];
          const slot = names.indexOf(binding.name);
          if (slot >= 0) {
            names.splice(slot, 1);
            (statement.bindings || []).splice(slot, 1);
          }
          rebind(binding, declaration, first.nodes[0]);
          restored += 1;
        }
      });
      return undefined;
    },
  });
  return restored;
}

function localForm(chunk) {
  let restored = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      node.statements.forEach((statement, at) => {
        const declared = M.plainDeclaration(statement);
        if (!declared) return;
        const value = bare(declared.value);
        if (!value || value.kind !== Kind.Function) return;
        if (!isIdentifier(declared.name)) return;
        if (!silentAbout(value.body, declared.name)) return;
        const declaration = {
          kind: Kind.LocalFunction,
          name: declared.name,
          body: value,
          binding: declared.binding,
        };
        declared.binding.declaration = declaration;
        declared.binding.initializer = declaration;
        node.statements[at] = declaration;
        restored += 1;
      });
      return undefined;
    },
  });
  return restored;
}

function assignedForm(chunk) {
  let restored = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      node.statements.forEach((statement, at) => {
        if (statement.kind !== Kind.Assignment) return;
        const targets = statement.targets || [];
        const expressions = statement.expressions || [];
        if (targets.length !== 1 || expressions.length !== 1) return;
        const target = bare(targets[0]);
        const value = bare(expressions[0]);
        if (!target || target.kind !== Kind.Name) return;
        if (!value || value.kind !== Kind.Function) return;
        if (!isIdentifier(target.name)) return;
        node.statements[at] = {
          kind: Kind.FunctionDeclaration,
          target,
          isMethod: false,
          body: value,
        };
        restored += 1;
      });
      return undefined;
    },
  });
  return restored;
}

function methodNames(chunk) {
  const found = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.MethodCall) found.add(node.method);
      return undefined;
    },
  });
  return found;
}

function fieldName(node) {
  if (!node || node.kind !== Kind.Index) return null;
  const key = bare(node.index);
  if (!key || key.kind !== Kind.String || !isIdentifier(key.value)) return null;
  return key.value;
}

function isFieldPath(node) {
  let current = node;
  while (current && current.kind === Kind.Index) {
    if (!fieldName(current)) return false;
    current = bare(current.base);
  }
  return !!current && current.kind === Kind.Name;
}

function methodForm(chunk) {
  const called = methodNames(chunk);
  let restored = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      node.statements.forEach((statement, at) => {
        if (statement.kind !== Kind.Assignment) return;
        const targets = statement.targets || [];
        const expressions = statement.expressions || [];
        if (targets.length !== 1 || expressions.length !== 1) return;
        const target = bare(targets[0]);
        const value = bare(expressions[0]);
        if (!value || value.kind !== Kind.Function) return;
        const field = fieldName(target);
        if (!field || !isFieldPath(target)) return;
        const params = value.params || [];
        const wantsSelf = called.has(field) && params.length > 0
          && silentAbout(value.body, 'self');
        if (wantsSelf) {
          const binding = (value.bindings || [])[0];
          if (binding) {
            for (const mention of mentions(value.body, binding)) mention.name = 'self';
            binding.name = 'self';
          }
          params[0] = 'self';
        }
        node.statements[at] = {
          kind: Kind.FunctionDeclaration,
          target,
          isMethod: wantsSelf,
          body: value,
        };
        restored += 1;
      });
      return undefined;
    },
  });
  return restored;
}

module.exports = {
  hasLabel,
  mentions,
  sink,
  slide,
  pushIn,
  harmless,
  fill,
  dropEmpty,
  recursiveForm,
  localForm,
  assignedForm,
  methodForm,
};
