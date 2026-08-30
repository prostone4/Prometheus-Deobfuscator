'use strict';

const { Kind } = require('../lua/ast');
const { walk } = require('../lua/walk');
const { isIdentifier } = require('../lua/format');
const { isGlobalName } = require('../lua/scope');

const COUNTERS = ['i', 'j', 'k', 'm', 'n'];

function reserved(chunk) {
  const taken = new Set([
    'and', 'break', 'do', 'else', 'elseif', 'end', 'false', 'for', 'function', 'goto', 'if',
    'in', 'local', 'nil', 'not', 'or', 'repeat', 'return', 'then', 'true', 'until', 'while',
    'self', '_ENV',
  ]);
  walk(chunk, {
    enter(node) {
      if (isGlobalName(node)) taken.add(node.name);
      return undefined;
    },
  });
  return taken;
}

function namer(taken) {
  const counts = { p: 0, f: 0, v: 0, i: 0 };
  const next = (category) => {
    for (let guard = 0; guard < 100000; guard += 1) {
      counts[category] += 1;
      const n = counts[category];
      const candidate = category === 'i' && n <= COUNTERS.length
        ? COUNTERS[n - 1]
        : `${category}${n}`;
      if (!taken.has(candidate) && isIdentifier(candidate)) {
        taken.add(candidate);
        return candidate;
      }
    }
    throw new Error('rename: name pool exhausted');
  };
  return next;
}

function holdsFunctions(chunk) {
  const tally = new Map();
  const count = (target, value) => {
    if (!target || target.kind !== Kind.Name || !target.binding) return;
    const seen = tally.get(target.binding) || { functions: 0, other: 0 };
    if (value && value.kind === Kind.Function) seen.functions += 1;
    else seen.other += 1;
    tally.set(target.binding, seen);
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.FunctionDeclaration) count(node.target, node.body);
      else if (node.kind === Kind.Assignment) {
        const values = node.expressions || [];
        const targets = node.targets || [];
        const aligned = values.length === targets.length;
        targets.forEach((target, at) => count(target, aligned ? values[at] : null));
      }
      return undefined;
    },
  });
  const named = new Set();
  for (const [binding, seen] of tally) {
    if (seen.functions && !seen.other) named.add(binding);
  }
  return named;
}

function categories(chunk) {
  const found = new Map();
  const stored = holdsFunctions(chunk);
  const assign = (binding, category) => {
    if (!binding || found.has(binding)) return;
    found.set(binding, category);
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Function) {
        (node.bindings || []).forEach((binding, at) => {
          if ((node.params || [])[at] === 'self') return;
          assign(binding, 'p');
        });
      } else if (node.kind === Kind.LocalFunction) {
        assign(node.binding, 'f');
      } else if (node.kind === Kind.NumericFor) {
        assign(node.binding, 'i');
      } else if (node.kind === Kind.GenericFor) {
        (node.bindings || []).forEach((binding) => assign(binding, 'v'));
      } else if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        const aligned = expressions.length === (node.names || []).length;
        (node.bindings || []).forEach((binding, at) => {
          const value = aligned ? expressions[at] : null;
          const holds = (value && value.kind === Kind.Function) || stored.has(binding);
          assign(binding, holds ? 'f' : 'v');
        });
      }
      return undefined;
    },
  });
  return found;
}

function plan(chunk, next) {
  const names = new Map();
  for (const [binding, category] of categories(chunk)) names.set(binding, next(category));
  return names;
}

function apply(chunk, names) {
  let renamed = 0;
  const rewrite = (list, bindings) => {
    if (!list || !bindings) return;
    for (let i = 0; i < bindings.length && i < list.length; i += 1) {
      const chosen = names.get(bindings[i]);
      if (chosen) list[i] = chosen;
    }
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Function) rewrite(node.params, node.bindings);
      else if (node.kind === Kind.LocalDeclaration) rewrite(node.names, node.bindings);
      else if (node.kind === Kind.GenericFor) rewrite(node.variables, node.bindings);
      else if (node.kind === Kind.LocalFunction) {
        const chosen = names.get(node.binding);
        if (chosen) node.name = chosen;
      } else if (node.kind === Kind.NumericFor) {
        const chosen = names.get(node.binding);
        if (chosen) node.variable = chosen;
      } else if (node.kind === Kind.Name && node.binding) {
        const chosen = names.get(node.binding);
        if (chosen && node.name !== chosen) {
          node.name = chosen;
          renamed += 1;
        }
      }
      return undefined;
    },
  });
  return renamed;
}

function run(context) {
  context.resolve();
  const taken = reserved(context.chunk);
  const names = plan(context.chunk, namer(taken));
  if (!names.size) return;
  const renamed = apply(context.chunk, names);
  context.resolve();
  context.note(`renamed ${names.size} local(s)`, names.size);
  context.bump('rename.bindings', names.size);
  context.bump('rename.mentions', renamed);
}

module.exports = {
  name: '08-vars',
  run,
  reserved,
  namer,
  categories,
  plan,
  apply,
};
