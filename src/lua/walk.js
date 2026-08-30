'use strict';

const { Kind } = require('./ast');

const CHILDREN = {
  [Kind.Chunk]: { body: 'node' },
  [Kind.Block]: { statements: 'list' },

  [Kind.LocalDeclaration]: { expressions: 'list' },
  [Kind.LocalFunction]: { body: 'node' },
  [Kind.FunctionDeclaration]: { target: 'node', body: 'node' },
  [Kind.Assignment]: { targets: 'list', expressions: 'list' },
  [Kind.CallStatement]: { expression: 'node' },
  [Kind.Return]: { expressions: 'list' },
  [Kind.Break]: {},
  [Kind.Continue]: {},
  [Kind.Goto]: {},
  [Kind.Label]: {},
  [Kind.Do]: { body: 'node' },
  [Kind.While]: { condition: 'node', body: 'node' },
  [Kind.Repeat]: { body: 'node', condition: 'node' },
  [Kind.If]: { condition: 'node', body: 'node', elseIfs: 'clauses', elseBody: 'node' },
  [Kind.NumericFor]: { start: 'node', limit: 'node', step: 'node', body: 'node' },
  [Kind.GenericFor]: { expressions: 'list', body: 'node' },

  [Kind.Nil]: {},
  [Kind.True]: {},
  [Kind.False]: {},
  [Kind.Number]: {},
  [Kind.String]: {},
  [Kind.Vararg]: {},
  [Kind.Name]: {},
  [Kind.Function]: { body: 'node' },
  [Kind.Table]: { entries: 'entries' },
  [Kind.Binary]: { lhs: 'node', rhs: 'node' },
  [Kind.Unary]: { argument: 'node' },
  [Kind.Index]: { base: 'node', index: 'node' },
  [Kind.Call]: { base: 'node', args: 'list' },
  [Kind.MethodCall]: { base: 'node', args: 'list' },
  [Kind.Paren]: { expression: 'node' },
};

const SPEC = {};
for (const kind of Object.keys(CHILDREN)) SPEC[kind] = Object.entries(CHILDREN[kind]);

const NONE = [];

function children(node) {
  const spec = node ? SPEC[node.kind] : null;
  if (!spec || spec.length === 0) return NONE;
  const out = [];
  for (let s = 0; s < spec.length; s += 1) {
    const key = spec[s][0];
    const value = node[key];
    if (value === undefined || value === null) continue;
    const type = spec[s][1];
    if (type === 'node') {
      out.push({ parent: node, key, index: null, node: value });
    } else if (type === 'list') {
      for (let i = 0; i < value.length; i += 1) {
        out.push({ parent: node, key, index: i, node: value[i] });
      }
    } else if (type === 'clauses') {
      for (let i = 0; i < value.length; i += 1) {
        const clause = value[i];
        out.push({ parent: clause, key: 'condition', index: null, node: clause.condition });
        out.push({ parent: clause, key: 'body', index: null, node: clause.body });
      }
    } else {
      for (let i = 0; i < value.length; i += 1) {
        const entry = value[i];
        if (entry.key) out.push({ parent: entry, key: 'key', index: null, node: entry.key });
        out.push({ parent: entry, key: 'value', index: null, node: entry.value });
      }
    }
  }
  return out;
}

function nodesOf(node) {
  const spec = node ? SPEC[node.kind] : null;
  if (!spec || spec.length === 0) return NONE;
  const out = [];
  for (let s = 0; s < spec.length; s += 1) {
    const value = node[spec[s][0]];
    if (value === undefined || value === null) continue;
    const type = spec[s][1];
    if (type === 'node') {
      out.push(value);
    } else if (type === 'list') {
      for (let i = 0; i < value.length; i += 1) out.push(value[i]);
    } else if (type === 'clauses') {
      for (let i = 0; i < value.length; i += 1) {
        out.push(value[i].condition);
        out.push(value[i].body);
      }
    } else {
      for (let i = 0; i < value.length; i += 1) {
        if (value[i].key) out.push(value[i].key);
        out.push(value[i].value);
      }
    }
  }
  return out;
}

function wants(visit) {
  return (visit.enter && visit.enter.length > 1) || (visit.leave && visit.leave.length > 1);
}

function deep(node, visit) {
  if (!node || !node.kind) return;
  if (visit.enter && visit.enter(node) === false) return;
  const kids = nodesOf(node);
  for (let i = 0; i < kids.length; i += 1) deep(kids[i], visit);
  visit.leave(node);
}

function bare(node, visit) {
  if (visit.leave) {
    deep(node, visit);
    return;
  }
  const enter = visit.enter;
  if (!enter) return;
  const stack = [node];
  let top = 1;
  while (top > 0) {
    top -= 1;
    const one = stack[top];
    if (!one || !one.kind) continue;
    if (enter(one) === false) continue;
    const spec = SPEC[one.kind];
    if (!spec) continue;
    for (let s = spec.length - 1; s >= 0; s -= 1) {
      const value = one[spec[s][0]];
      if (value === undefined || value === null) continue;
      const type = spec[s][1];
      if (type === 'node') {
        stack[top] = value;
        top += 1;
      } else if (type === 'list') {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i];
          top += 1;
        }
      } else if (type === 'clauses') {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i].body;
          top += 1;
          stack[top] = value[i].condition;
          top += 1;
        }
      } else {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i].value;
          top += 1;
          if (value[i].key) {
            stack[top] = value[i].key;
            top += 1;
          }
        }
      }
    }
  }
}

function framed(root, fn) {
  const stack = [root];
  const frames = [null];
  let top = 1;
  while (top > 0) {
    top -= 1;
    const node = stack[top];
    const frame = frames[top];
    if (!node || !node.kind) continue;
    fn(node, frame);
    if (node.kind === Kind.Block) {
      const statements = node.statements;
      const depth = frame ? frame.depth + 1 : 1;
      for (let i = statements.length - 1; i >= 0; i -= 1) {
        stack[top] = statements[i];
        frames[top] = { block: node, at: i, up: frame, depth };
        top += 1;
      }
      continue;
    }
    const spec = SPEC[node.kind];
    if (!spec) continue;
    for (let s = spec.length - 1; s >= 0; s -= 1) {
      const value = node[spec[s][0]];
      if (value === undefined || value === null) continue;
      const type = spec[s][1];
      if (type === 'node') {
        stack[top] = value;
        frames[top] = frame;
        top += 1;
      } else if (type === 'list') {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i];
          frames[top] = frame;
          top += 1;
        }
      } else if (type === 'clauses') {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i].body;
          frames[top] = frame;
          top += 1;
          stack[top] = value[i].condition;
          frames[top] = frame;
          top += 1;
        }
      } else {
        for (let i = value.length - 1; i >= 0; i -= 1) {
          stack[top] = value[i].value;
          frames[top] = frame;
          top += 1;
          if (value[i].key) {
            stack[top] = value[i].key;
            frames[top] = frame;
            top += 1;
          }
        }
      }
    }
  }
}

function walk(node, visit, parentInfo = null) {
  if (parentInfo === null && !wants(visit)) {
    bare(node, visit);
    return;
  }
  if (!node || !node.kind) return;
  if (visit.enter && visit.enter(node, parentInfo) === false) return;
  const kids = children(node);
  for (let i = 0; i < kids.length; i += 1) walk(kids[i].node, visit, kids[i]);
  if (visit.leave) visit.leave(node, parentInfo);
}

function transform(node, fn) {
  if (!node || !node.kind) return node;
  const kids = children(node);
  for (let i = 0; i < kids.length; i += 1) {
    const child = kids[i];
    const replaced = transform(child.node, fn);
    if (replaced === child.node) continue;
    if (child.index === null) child.parent[child.key] = replaced;
    else child.parent[child.key][child.index] = replaced;
  }
  const result = fn(node);
  return result === undefined ? node : result;
}

function collect(root, predicate) {
  const found = [];
  walk(root, {
    enter(node) {
      if (predicate(node)) found.push(node);
    },
  });
  return found;
}

function clone(node) {
  if (Array.isArray(node)) return node.map(clone);
  if (!node || typeof node !== 'object') return node;
  const copy = {};
  for (const key of Object.keys(node)) copy[key] = clone(node[key]);
  return copy;
}

module.exports = {
  CHILDREN,
  children,
  framed,
  walk,
  transform,
  collect,
};
