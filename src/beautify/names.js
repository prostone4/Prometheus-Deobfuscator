'use strict';

const { Kind } = require('../lua/ast');
const { walk, collect } = require('../lua/walk');
const { isIdentifier } = require('../lua/format');
const { isLocalBinding } = require('../lua/scope');
const { isDigit, isLower, isUpper } = require('../lua/chars');
const { bare } = require('../util/flow');

function words(text) {
  const found = [];
  let at = 0;
  while (at < text.length) {
    const character = text[at];
    if (!isUpper(character) && !isLower(character) && !isDigit(character)) {
      at += 1;
      continue;
    }
    let end = at;
    if (isUpper(character)) {
      while (end < text.length && isUpper(text[end])) end += 1;
      const run = end - at;
      if (run >= 3 && end < text.length && isLower(text[end])) end -= 1;
      else if (run === 1) {
        while (end < text.length && (isLower(text[end]) || isDigit(text[end]))) end += 1;
      } else if (end < text.length && isLower(text[end])) {
        while (end < text.length && (isLower(text[end]) || isDigit(text[end]))) end += 1;
      }
    } else {
      while (end < text.length && (isLower(text[end]) || isDigit(text[end]))) end += 1;
    }
    found.push(text.slice(at, end));
    at = end;
  }
  return found;
}

function camel(text) {
  const parts = words(String(text || ''));
  if (!parts.length) return null;
  const head = parts[0].toLowerCase();
  const tail = parts.slice(1).map((part) => (part === part.toUpperCase() && part.length > 1
    ? part
    : part[0].toUpperCase() + part.slice(1)));
  const candidate = head + tail.join('');
  return isIdentifier(candidate) ? candidate : null;
}

function typeWord(text) {
  let end = text.length;
  while (end > 1 && isDigit(text[end - 1])) end -= 1;
  return text.slice(0, end);
}

function spelled(node) {
  const value = bare(node);
  if (!value || value.kind !== Kind.String) return null;
  return camel(value.value);
}

function keyOf(node) {
  if (!node || node.kind !== Kind.Index) return null;
  const key = bare(node.index);
  if (!key || key.kind !== Kind.String) return null;
  return key.value;
}

const CTORS = ['Create', 'New', 'Make', 'Build'];

function constructed(method) {
  const text = String(method || '');
  for (const verb of CTORS) {
    if (text.length <= verb.length) continue;
    if (text.slice(0, verb.length) !== verb) continue;
    if (!isUpper(text[verb.length])) continue;
    return text.slice(verb.length);
  }
  return null;
}

function optionName(node) {
  const table = bare(node);
  if (!table || table.kind !== Kind.Table) return null;
  for (const wanted of ['Title', 'Name']) {
    for (const entry of table.entries || []) {
      if (entry.type !== 'key') continue;
      const key = bare(entry.key);
      if (!key || key.kind !== Kind.String || key.value !== wanted) continue;
      const value = bare(entry.value);
      if (value && value.kind === Kind.String) return value.value;
    }
  }
  return null;
}

const QUALIFIERS = 2;

function qualifierOf(args) {
  const first = (args || [])[0];
  if (!first) return null;
  const said = bare(first);
  const text = said && said.kind === Kind.String ? said.value : optionName(first);
  if (!text) return null;
  const parts = words(String(text));
  if (!parts.length || parts.length > QUALIFIERS) return null;
  return parts.join(' ');
}

function entryKey(entry) {
  if (!entry || entry.type !== 'key') return null;
  const key = bare(entry.key);
  return key && key.kind === Kind.String ? key.value : null;
}

const CALLBACKS = new Set(['Callback', 'OnCallback', 'OnChanged', 'OnChange',
  'OnClick', 'OnToggle', 'OnFocusLost']);

const LABELS = ['Title', 'Name', 'Flag'];

function controlWord(table) {
  for (const wanted of LABELS) {
    for (const entry of table.entries || []) {
      if (entryKey(entry) !== wanted) continue;
      const said = bare(entry.value);
      if (!said || said.kind !== Kind.String) continue;
      const parts = words(said.value);
      if (!parts.length || parts.length > QUALIFIERS) continue;
      return parts.join(' ');
    }
  }
  return null;
}

function optionCallbacks(root) {
  const found = [];
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Table) return undefined;
      for (const entry of node.entries || []) {
        if (!CALLBACKS.has(entryKey(entry))) continue;
        const fn = bare(entry.value);
        if (!fn || fn.kind !== Kind.Function) continue;
        found.push({ word: controlWord(node), fn });
      }
      return undefined;
    },
  });
  return found;
}

function writtenBy(fn) {
  const own = new Set();
  walk(fn, {
    enter(node) {
      for (const binding of node.bindings || []) own.add(binding);
      if (node.kind === Kind.LocalFunction || node.kind === Kind.NumericFor) {
        own.add(node.binding);
      }
      return undefined;
    },
  });
  const inside = new Set(collect(fn, (node) => node.kind === Kind.Name));
  const held = new Set();
  for (const said of inside) {
    const binding = said.binding;
    if (!binding || !isLocalBinding(binding) || own.has(binding)) continue;
    const writes = binding.writes || [];
    if (!writes.length || !writes.every((write) => inside.has(write))) continue;
    held.add(binding);
  }
  return held.size === 1 ? [...held][0] : null;
}

const LOADERS = new Set(['loadstring', 'load']);

const PLUMBING = new Set(['raw', 'main', 'master', 'latest', 'download', 'releases',
  'release', 'blob', 'refs', 'heads', 'tags', 'archive', 'files', 'file', 'lua',
  'init', 'source', 'dl', 'api', 'v1', 'v2']);

function fromUrl(text) {
  const shown = String(text).split('?')[0].split('#')[0];
  const scheme = shown.indexOf('://');
  const path = scheme < 0 ? shown : shown.slice(scheme + 3);
  const parts = path.split('/').filter((part) => part.length > 0);

  for (let at = parts.length - 1; at >= 1; at -= 1) {
    const segment = parts[at].split('.')[0];
    if (!segment || PLUMBING.has(segment.toLowerCase())) continue;
    const named = camel(segment);
    if (named) return named;
  }
  return null;
}

function loadedLibrary(node) {
  if (node.kind !== Kind.Call || (node.args || []).length) return null;
  const inner = bare(node.base);
  if (!inner || inner.kind !== Kind.Call) return null;
  const loader = bare(inner.base);
  if (!loader || loader.kind !== Kind.Name || isLocalBinding(loader.binding)) return null;
  if (!LOADERS.has(loader.name)) return null;
  let url = null;
  walk(inner, {
    enter(one) {
      if (url === null && one.kind === Kind.String && one.value.indexOf('://') >= 0) {
        url = one.value;
      }
      return undefined;
    },
  });
  return url === null ? null : fromUrl(url);
}

const CHOICE = { and: ['rhs', 'lhs'], or: ['lhs', 'rhs'] };

function hintOf(node) {
  const value = bare(node);
  if (!value) return null;
  if (value.kind === Kind.Binary) {
    const sides = CHOICE[value.operator];
    if (!sides) return null;
    for (const side of sides) {
      const found = hintOf(value[side]);
      if (found) return found;
    }
    return null;
  }
  if (value.kind === Kind.Call || value.kind === Kind.MethodCall) {
    const args = value.args || [];
    const fetched = loadedLibrary(value);
    if (fetched) return fetched;
    const made = value.kind === Kind.MethodCall ? constructed(value.method) : null;
    const qualifier = qualifierOf(args);
    if (made) {
      const named = camel(qualifier === null ? made : `${qualifier} ${made}`);
      if (named) return named;
    }
    if (args.length === 1) {
      const named = spelled(args[0]);
      if (named) return named;
    }
    if (value.kind === Kind.MethodCall) {
      if (qualifier !== null && optionName(args[0]) !== null) {
        const named = camel(`${qualifier} ${value.method}`);
        if (named) return named;
      }
      return camel(value.method);
    }
    const base = bare(value.base);
    const library = base && base.kind === Kind.Index ? bare(base.base) : null;
    if (library && library.kind === Kind.Name && !isLocalBinding(library.binding)) {
      return camel(typeWord(library.name));
    }
    return null;
  }
  if (value.kind === Kind.Index) {
    const key = keyOf(value);
    return key ? camel(key) : null;
  }
  if (value.kind === Kind.Name && !isLocalBinding(value.binding)) return camel(value.name);
  return null;
}

const LISTENERS = {
  InputBegan: 'input',
  InputChanged: 'input',
  InputEnded: 'input',
  PlayerAdded: 'player',
  PlayerRemoving: 'player',
  CharacterAdded: 'character',
  CharacterRemoving: 'character',
  ChildAdded: 'child',
  ChildRemoved: 'child',
  DescendantAdded: 'descendant',
  DescendantRemoving: 'descendant',
  Touched: 'part',
  TouchEnded: 'part',
  Chatted: 'message',
  Heartbeat: 'delta',
  Stepped: 'delta',
  RenderStepped: 'delta',
  PromptButtonHoldBegan: 'player',
};

function connectedEvent(node) {
  if (!node || node.kind !== Kind.MethodCall || node.method !== 'Connect') return null;
  return keyOf(bare(node.base));
}

const ITERS = {
  ipairs: ['index', 'value'],
  pairs: ['key', 'value'],
  next: ['key', 'value'],
  gmatch: ['match'],
  gfind: ['match'],
  lines: ['line'],
};

function iteratorName(expressions) {
  const first = bare((expressions || [])[0]);
  if (!first) return null;
  if (first.kind === Kind.MethodCall) return first.method;
  if (first.kind === Kind.Call) {
    const base = bare(first.base);
    if (!base) return null;
    if (base.kind === Kind.Name) return isLocalBinding(base.binding) ? null : base.name;
    return keyOf(base);
  }
  if (first.kind === Kind.Name && !isLocalBinding(first.binding)) return first.name;
  return null;
}

const METAS = {
  __index: ['object', 'key'],
  __newindex: ['object', 'key', 'value'],
  __call: ['object'],
  __tostring: ['object'],
  __len: ['object'],
  __unm: ['object'],
  __gc: ['object'],
  __close: ['object'],
  __add: ['lhs', 'rhs'],
  __sub: ['lhs', 'rhs'],
  __mul: ['lhs', 'rhs'],
  __div: ['lhs', 'rhs'],
  __idiv: ['lhs', 'rhs'],
  __mod: ['lhs', 'rhs'],
  __pow: ['lhs', 'rhs'],
  __concat: ['lhs', 'rhs'],
  __eq: ['lhs', 'rhs'],
  __lt: ['lhs', 'rhs'],
  __le: ['lhs', 'rhs'],
};

function keyedFunctions(chunk) {
  const found = [];
  const note = (key, value) => {
    const spelling = bare(key);
    const held = bare(value);
    if (!spelling || spelling.kind !== Kind.String) return;
    if (!held || held.kind !== Kind.Function) return;
    found.push([spelling.value, held]);
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Table) {
        for (const entry of node.entries || []) {
          if (entry.type === 'key') note(entry.key, entry.value);
        }
      } else if (node.kind === Kind.Assignment) {
        const expressions = node.expressions || [];
        if (expressions.length !== (node.targets || []).length) return undefined;
        node.targets.forEach((target, at) => {
          const stored = bare(target);
          if (stored && stored.kind === Kind.Index) note(stored.index, expressions[at]);
        });
      } else if (node.kind === Kind.FunctionDeclaration && !node.isMethod) {
        const target = bare(node.target);
        if (target && target.kind === Kind.Index) note(target.index, node.body);
      }
      return undefined;
    },
  });
  return found;
}

function roleFacts(chunk) {
  const fields = new Map();
  const called = new Set();
  const steps = new Map();
  const note = (list, binding, value) => {
    const kept = list.get(binding);
    if (kept) kept.push(value);
    else list.set(binding, [value]);
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Table) {
        for (const entry of node.entries || []) {
          if (entry.type === 'key') fields.set(bare(entry.value), bare(entry.key));
        }
      } else if (node.kind === Kind.Call) {
        const base = bare(node.base);
        if (base) called.add(base);
      } else if (node.kind === Kind.Assignment) {
        const expressions = node.expressions || [];
        const targets = node.targets || [];
        const aligned = expressions.length === targets.length;
        targets.forEach((target, at) => {
          const value = aligned ? bare(expressions[at]) : null;
          if (target.kind === Kind.Name && target.binding) {
            note(steps, target.binding, value);
          }
          if (!aligned) return;
          const stored = bare(target);
          if (stored && stored.kind === Kind.Index) fields.set(value, bare(stored.index));
        });
      }
      return undefined;
    },
  });
  return { fields, called, steps };
}

function storedField(chunk, binding, facts) {
  const reads = (binding && binding.reads) || [];
  if (!reads.length) return null;
  const { fields } = facts || roleFacts(chunk);
  const keys = new Set();
  let stored = 0;
  for (const read of reads) {
    const spelling = fields.get(read);
    if (spelling === undefined) continue;
    if (spelling && spelling.kind === Kind.String) keys.add(spelling.value);
    stored += 1;
  }
  if (stored !== reads.length || keys.size !== 1) return null;
  return camel([...keys][0]);
}

function onlyCalled(chunk, binding, facts) {
  const reads = (binding && binding.reads) || [];
  if (!reads.length) return false;
  const { called } = facts || roleFacts(chunk);
  let seen = 0;
  for (const read of reads) if (called.has(read)) seen += 1;
  return seen === reads.length;
}

const ACCUMS = { '+': ['count', 'total'], '..': [null, 'text'] };

function seedOperator(node) {
  const seed = bare(node);
  if (!seed) return null;
  if (seed.kind === Kind.Number && seed.value === 0) return '+';
  if (seed.kind === Kind.String && seed.value === '') return '..';
  return null;
}

function accumulated(chunk, binding, operator, facts) {
  const [ones, many] = ACCUMS[operator];
  const written = (facts || roleFacts(chunk)).steps.get(binding) || [];
  let steps = 0;
  let byOne = 0;
  let other = 0;
  for (const value of written) {
    if (!value || value.kind !== Kind.Binary || value.operator !== operator) {
      other += 1;
      continue;
    }
    const lhs = bare(value.lhs);
    const rhs = bare(value.rhs);
    const added = lhs && lhs.kind === Kind.Name && lhs.binding === binding ? rhs
      : (rhs && rhs.kind === Kind.Name && rhs.binding === binding ? lhs : null);
    if (!added) {
      other += 1;
      continue;
    }
    steps += 1;
    if (added.kind === Kind.Number && added.value === 1) byOne += 1;
  }
  if (!steps || other) return null;
  return byOne === steps ? ones : many;
}

function suggest(chunk) {
  const hints = new Map();
  const offer = (binding, hint) => {
    if (!hint || !binding || !isLocalBinding(binding) || hints.has(binding)) return;
    hints.set(binding, hint);
  };
  const named = new Map();
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Assignment) return undefined;
      const targets = node.targets || [];
      const expressions = node.expressions || [];
      if (targets.length !== expressions.length) return undefined;
      targets.forEach((target, at) => {
        const field = bare(target);
        if (keyOf(field) !== 'Name') return;
        const owner = bare(field.base);
        if (!owner || owner.kind !== Kind.Name || !isLocalBinding(owner.binding)) return;
        const hint = spelled(expressions[at]);
        if (hint && !named.has(owner.binding)) named.set(owner.binding, hint);
      });
      return undefined;
    },
  });
  for (const [binding, hint] of named) offer(binding, hint);

  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        if (expressions.length !== (node.names || []).length) return undefined;
        (node.bindings || []).forEach((binding, at) => {
          offer(binding, hintOf(expressions[at]));
        });
      } else if (node.kind === Kind.Assignment) {
        const targets = node.targets || [];
        const expressions = node.expressions || [];
        if (targets.length !== expressions.length) return undefined;
        targets.forEach((target, at) => {
          const stored = bare(target);
          if (!stored || stored.kind !== Kind.Name) return;
          offer(stored.binding, hintOf(expressions[at]));
        });
      } else if (node.kind === Kind.GenericFor) {
        const wanted = ITERS[iteratorName(node.expressions)] || [];
        (node.bindings || []).forEach((binding, at) => offer(binding, wanted[at]));
      } else if (node.kind === Kind.MethodCall) {
        const event = connectedEvent(node);
        const wanted = event && LISTENERS[event];
        if (!wanted) return undefined;
        for (const argument of node.args || []) {
          const listener = bare(argument);
          if (!listener || listener.kind !== Kind.Function) continue;
          if ((listener.params || [])[0] === 'self') continue;
          offer((listener.bindings || [])[0], wanted);
        }
      }
      return undefined;
    },
  });

  for (const { word, fn } of optionCallbacks(chunk)) {
    if ((fn.params || [])[0] !== 'self') offer((fn.bindings || [])[0], 'value');
    const hint = word === null ? null : camel(word);
    if (hint) offer(writtenBy(fn), hint);
  }

  for (const [key, fn] of keyedFunctions(chunk)) {
    const wanted = METAS[key];
    if (!wanted) continue;
    (fn.bindings || []).forEach((binding, at) => offer(binding, wanted[at]));
  }

  const seeds = new Map();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.LocalDeclaration) {
        const expressions = node.expressions || [];
        if (expressions.length !== (node.names || []).length) return undefined;
        (node.bindings || []).forEach((binding, at) => {
          const operator = seedOperator(expressions[at]);
          if (operator && isLocalBinding(binding)) seeds.set(binding, operator);
        });
      }
      return undefined;
    },
  });

  const roles = [];
  walk(chunk, {
    enter(node) {
      const parameter = node.kind === Kind.Function;
      if (!parameter && node.kind !== Kind.LocalDeclaration) return undefined;
      for (const binding of node.bindings || []) {
        if (binding && isLocalBinding(binding) && !hints.has(binding)) {
          roles.push([binding, parameter]);
        }
      }
      return undefined;
    },
  });
  const facts = roles.length ? roleFacts(chunk) : null;
  for (const [binding, parameter] of roles) {
    const field = storedField(chunk, binding, facts);
    if (field) {
      offer(binding, field);
      continue;
    }

    if (parameter && onlyCalled(chunk, binding, facts)) {
      offer(binding, 'fn');
      continue;
    }
    const operator = seeds.get(binding);
    if (operator) offer(binding, accumulated(chunk, binding, operator, facts));
  }
  return hints;
}

function allocator(taken) {
  return (wanted) => {
    if (!taken.has(wanted) && isIdentifier(wanted)) {
      taken.add(wanted);
      return wanted;
    }
    for (let n = 2; n < 100000; n += 1) {
      const candidate = `${wanted}${n}`;
      if (!taken.has(candidate) && isIdentifier(candidate)) {
        taken.add(candidate);
        return candidate;
      }
    }
    throw new Error('names: candidate pool exhausted');
  };
}

module.exports = {
  spelled,
  keyOf,
  entryKey,
  suggest,
  allocator,
};
