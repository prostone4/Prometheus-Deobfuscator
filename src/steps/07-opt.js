'use strict';

const { Kind } = require('../lua/ast');
const A = require('../lua/ast');
const { walk, transform } = require('../lua/walk');
const purity = require('../util/purity');
const { isIdentifier } = require('../lua/format');
const { isGlobalName, isLocalBinding } = require('../lua/scope');
const idioms = require('../vm/idioms');
const { Writes } = require('../util/writes');
const { writesIn, readsIn } = require('../util/eval');
const { removeStores, removeRedundant } = require('../util/dead-stores');
const { removeDead } = require('../util/dead-code');
const { Positions } = require('../util/order');

const fold = require('./02-fold');
const guards = require('./05-if');
const C = require('../util/const');

function decideLogic(chunk, facts, counters) {
  let decided = 0;
  transform(chunk, (node) => {
    if (node.kind !== Kind.Binary) return node;
    if (node.operator !== 'and' && node.operator !== 'or') return node;
    const known = C.truthiness(node.lhs);
    if (known === null) return node;
    const keepsLeft = node.operator === 'and' ? !known : known;
    const dropped = keepsLeft ? node.rhs : node.lhs;
    if (!purity.isSelfContained(dropped, facts)) return node;
    counters.decided += 1;
    decided += 1;
    return keepsLeft ? node.lhs : node.rhs;
  });
  return decided;
}

function nodeSet(root) {
  const seen = new Set();
  walk(root, {
    enter(node) {
      seen.add(node);
      return undefined;
    },
  });
  return seen;
}

function readOnlyIn(binding, root) {
  const reads = binding.reads || [];
  if (!reads.length) return true;
  const inside = nodeSet(root);
  return reads.every((node) => inside.has(node));
}

function isDead(binding, definition) {
  if (!isLocalBinding(binding)) return false;
  const reads = binding.reads || [];
  if (!reads.length) return true;
  return definition ? readOnlyIn(binding, definition) : false;
}

function eliminate(chunk, facts, counters) {
  let removed = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const out = [];
      for (const statement of node.statements) {
        if (statement.kind === Kind.LocalFunction) {
          if (isDead(statement.binding, statement)) {
            removed += 1;
            continue;
          }
        } else if (statement.kind === Kind.LocalDeclaration) {
          const bindings = statement.bindings || [];
          const names = statement.names || [];
          const expressions = statement.expressions || [];
          const aligned = expressions.length === names.length;
          const keep = [];
          for (let i = 0; i < names.length; i += 1) {
            const written = ((bindings[i] && bindings[i].writes) || []).length > 0;
            const dies = !written && isDead(bindings[i], aligned ? expressions[i] : null)
              && (!aligned || purity.isSelfContained(expressions[i], facts));
            if (dies) removed += 1;
            else keep.push(i);
          }
          if (!keep.length && (!expressions.length
            || expressions.every((e) => purity.isSelfContained(e, facts)))) {
            continue;
          }
          if (keep.length !== names.length && aligned) {
            statement.names = keep.map((i) => names[i]);
            statement.bindings = keep.map((i) => bindings[i]);
            statement.expressions = keep.map((i) => expressions[i]);
          } else if (keep.length !== names.length && !expressions.length) {
            statement.names = keep.map((i) => names[i]);
            statement.bindings = keep.map((i) => bindings[i]);
          }
        } else if (statement.kind === Kind.Assignment) {
          const targets = statement.targets || [];
          const expressions = statement.expressions || [];

          if (targets.length === 1 && expressions.length === 1
            && targets[0].kind === Kind.Name && expressions[0].kind === Kind.Name
            && targets[0].binding && targets[0].binding === expressions[0].binding) {
            removed += 1;
            continue;
          }
          const deadTarget = (target) => target.kind === Kind.Name
            && isDead(target.binding, null);
          if (targets.every(deadTarget)
            && expressions.every((e) => purity.isSelfContained(e, facts))) {
            removed += targets.length;
            continue;
          }

          const bare = expressions.length === 1 ? A.unparen(expressions[0]) : null;
          if (targets.every(deadTarget) && bare
            && (bare.kind === Kind.Call || bare.kind === Kind.MethodCall)) {
            removed += targets.length;
            out.push(A.callStatement(bare));
            continue;
          }
          if (targets.length === expressions.length && targets.some(deadTarget)
            && targets.some((t) => !deadTarget(t))) {
            const keep = [];
            for (let i = 0; i < targets.length; i += 1) {
              if (deadTarget(targets[i])
                && purity.isSelfContained(expressions[i], facts)) removed += 1;
              else keep.push(i);
            }
            statement.targets = keep.map((i) => targets[i]);
            statement.expressions = keep.map((i) => expressions[i]);
          }
        } else if (statement.kind === Kind.CallStatement) {
          if (purity.touchesOwn(statement.expression, facts)
            && purity.isSelfContained(statement.expression, facts)) {
            removed += 1;
            continue;
          }
        } else if (statement.kind === Kind.Do
          && !((statement.body && statement.body.statements) || []).length) {
          removed += 1;
          continue;
        }
        out.push(statement);
      }
      node.statements = out;
      return undefined;
    },
  });
  counters.eliminated += removed;
  return removed;
}

function mergeDecls(chunk, counters) {
  let merged = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let i = 0; i + 1 < node.statements.length; i += 1) {
        const decl = node.statements[i];
        if (decl.kind !== Kind.LocalDeclaration || (decl.expressions || []).length) continue;
        const next = node.statements[i + 1];
        if (!next || next.kind !== Kind.Assignment) continue;
        const targets = next.targets || [];
        const expressions = next.expressions || [];
        if (!targets.length || targets.length !== expressions.length) continue;
        const owned = new Set(decl.bindings || []);
        if (!targets.every((t) => t.kind === Kind.Name && owned.has(t.binding))) continue;
        let touches = false;
        for (const expression of expressions) {
          walk(expression, {
            enter(child) {
              if (child.kind === Kind.Name && owned.has(child.binding)) touches = true;
              return undefined;
            },
          });
        }
        if (touches) continue;
        const taken = new Set(targets.map((t) => t.binding));
        const rest = [];
        const restBindings = [];
        (decl.bindings || []).forEach((binding, at) => {
          if (taken.has(binding)) return;
          rest.push(decl.names[at]);
          restBindings.push(binding);
        });
        const joined = A.localDecl(targets.map((t) => t.name), expressions);
        joined.bindings = targets.map((t) => t.binding);

        const replacement = rest.length
          ? [joined, Object.assign(decl, { names: rest, bindings: restBindings })]
          : [joined];
        node.statements.splice(i, 2, ...replacement);
        merged += 1;
        i -= 1;
      }
      return undefined;
    },
  });
  counters.merged += merged;
  return merged;
}

function dropParens(chunk, counters) {
  let dropped = 0;
  transform(chunk, (node) => {
    if (node.kind !== Kind.Paren) return node;
    const inner = node.expression;
    if (!inner) return node;

    if (A.isMultiValue(inner)) return node;
    if (inner.kind === Kind.Name || inner.kind === Kind.Paren || A.isLiteral(inner)
      || inner.kind === Kind.Table || inner.kind === Kind.Index) {
      dropped += 1;
      return inner;
    }
    return node;
  });
  counters.parens += dropped;
  return dropped;
}

function basePositions(chunk) {
  const bases = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Index || node.kind === Kind.Call
        || node.kind === Kind.MethodCall) bases.add(node.base);
      return undefined;
    },
  });
  return bases;
}

function pushLiterals(chunk, counters) {
  const writes = new Map();
  walk(chunk, {
    enter(node) {
      const note = (binding, value, at, bare) => {
        if (!isLocalBinding(binding)) return;
        let seen = writes.get(binding);
        if (!seen) {
          seen = { count: 0, bare: 0, valued: 0, value: null, at: null };
          writes.set(binding, seen);
        }
        seen.count += 1;
        if (value) {
          seen.valued += 1;
          seen.value = value;
          seen.at = at;
        } else if (bare) seen.bare += 1;
      };
      if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        const aligned = expressions.length === (node.names || []).length;
        (node.bindings || []).forEach((binding, at) => {
          note(binding, aligned ? expressions[at] : null, node, !expressions.length);
        });
      } else if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        const aligned = targets.length === expressions.length;
        targets.forEach((target, at) => {
          if (target.kind !== Kind.Name) return;
          note(target.binding, aligned ? expressions[at] : null, node, false);
        });
      } else if (node.kind === Kind.LocalFunction) note(node.binding, null, node, false);
      else if (node.kind === Kind.NumericFor) note(node.binding, null, node, false);
      else if (node.kind === Kind.GenericFor || node.kind === Kind.Function) {
        for (const binding of node.bindings || []) note(binding, null, node, false);
      }
      return undefined;
    },
  });

  const values = new Map();
  let positions = null;
  let bases = null;

  const copies = new Map();
  for (const [binding, info] of writes) {
    if (!info.value || info.valued !== 1 || info.bare !== info.count - 1) continue;
    const value = A.unparen(info.value);
    if (value.kind !== Kind.Name) continue;
    if (!isLocalBinding(value.binding) || value.binding === binding) continue;
    copies.set(value, binding);
  }

  const spelledAt = (binding, seen) => {
    const found = [];
    for (const read of binding.reads || []) {
      const into = copies.get(read);
      if (into && !seen.has(into)) {
        seen.add(into);
        found.push(...spelledAt(into, seen));
      } else found.push(read);
    }
    return found;
  };

  for (const [binding, info] of writes) {
    if (!info.value || info.valued !== 1) continue;
    if (!A.isLiteral(info.value) || info.value.kind === Kind.Vararg) continue;
    const reads = binding.reads || [];
    if (!reads.length) continue;
    if (info.count !== 1) {
      if (info.bare !== info.count - 1) continue;
      if (!positions) positions = new Positions(chunk);
      if (!reads.every((read) => positions.precedes(info.at, read))) continue;
    }
    const spelled = spelledAt(binding, new Set([binding]));
    if (spelled.length > 1) {
      if (!bases) bases = basePositions(chunk);
      if (spelled.some((read) => bases.has(read))) continue;
    }
    values.set(binding, info.value);
  }
  if (!values.size) return 0;

  const targets = new Set();
  for (const binding of values.keys()) {
    for (const write of binding.writes || []) targets.add(write);
  }

  let replaced = 0;
  transform(chunk, (node) => {
    if (node.kind !== Kind.Name || !node.binding || targets.has(node)) return node;
    const value = values.get(node.binding);
    if (!value) return node;
    replaced += 1;
    return { ...value };
  });
  counters.propagated += replaced;
  return replaced;
}

function resolveGlobals(chunk, counters) {
  const locals = new Set();
  walk(chunk, {
    enter(node) {
      if (isLocalBinding(node.binding)) locals.add(node.name);
      return undefined;
    },
  });
  let resolved = 0;
  transform(chunk, (node) => {
    if (node.kind !== Kind.Index) return node;
    const base = node.base;
    if (!isGlobalName(base) || base.name !== '_ENV') return node;
    const key = node.index;
    if (!key || key.kind !== Kind.String || !isIdentifier(key.value)) return node;
    if (locals.has(key.value)) return node;
    resolved += 1;
    return A.name(key.value);
  });
  counters.globals += resolved;
  return resolved;
}

function tidyLoops(chunk, counters) {
  let tidied = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.NumericFor && node.step
        && node.step.kind === Kind.Number && node.step.value === 1) {
        node.step = null;
        tidied += 1;
      }
      return undefined;
    },
  });
  counters.loops += tidied;
  return tidied;
}

function run(context) {
  const counters = {
    eliminated: 0, merged: 0, parens: 0, idioms: 0, propagated: 0, loops: 0, globals: 0,
    stores: 0, decided: 0, unwanted: 0,
  };
  for (let round = 0; round < 24; round += 1) {
    context.resolve();
    let changed = 0;
    changed += idioms.run(context, counters);
    context.resolve();
    changed += pushLiterals(context.chunk, counters);
    context.resolve();
    changed += resolveGlobals(context.chunk, counters);
    context.resolve();
    const facts = new purity.Facts(context.chunk);

    const decided = fold.foldTree(context.chunk, {
      binary: fold.BINARY,
      unary: fold.LOGIC,
    });
    counters.decided += decided;
    changed += decided;
    changed += decideLogic(context.chunk, facts, counters);
    context.resolve();
    const resolved = context.stats['guards.constants'] || 0;
    guards.run(context);
    changed += (context.stats['guards.constants'] || 0) - resolved;
    context.resolve();
    changed += eliminate(context.chunk, facts, counters);
    context.resolve();

    const stores = removeStores(
      context.chunk,
      new Writes(context.chunk, writesIn, readsIn),
      new purity.Facts(context.chunk),
    );
    counters.stores += stores;
    changed += stores;
    context.resolve();

    const restated = removeRedundant(context.chunk);
    counters.stores += restated;
    changed += restated;
    context.resolve();

    const unwanted = removeDead(context.chunk, new purity.Facts(context.chunk));
    counters.unwanted += unwanted;
    changed += unwanted;
    context.resolve();
    changed += mergeDecls(context.chunk, counters);
    changed += dropParens(context.chunk, counters);
    const before = context.stats['fold.count'] || 0;

    fold.run(context);
    changed += (context.stats['fold.count'] || 0) - before;
    if (!changed) break;
  }
  tidyLoops(context.chunk, counters);
  context.resolve();
  const total = Object.values(counters).reduce((a, b) => a + b, 0);
  if (total) {
    context.note(
      `removed ${counters.eliminated + counters.stores} dead write(s),`
      + ` ${counters.unwanted} unwanted statement(s),`
      + ` merged ${counters.merged} declaration(s),`
      + ` rebuilt ${counters.idioms} idiom(s)`,
      total,
    );
  }
  for (const key of Object.keys(counters)) {
    if (counters[key]) context.bump(`simplify.${key}`, counters[key]);
  }
}

module.exports = {
  name: '07-opt',
  run,
  eliminate,
  mergeDecls,
  dropParens,
};
