'use strict';

const A = require('../lua/ast');
const { Kind } = A;
const { walk, transform, collect } = require('../lua/walk');
const { isLocalBinding } = require('../lua/scope');
const { bare } = require('../util/flow');

const METHOD = 'GetService';

function serviceOf(node) {
  if (!node || node.kind !== Kind.MethodCall || node.method !== METHOD) return null;
  const args = node.args || [];
  if (args.length !== 1) return null;
  const argument = bare(args[0]);
  if (!argument || argument.kind !== Kind.String) return null;
  const host = bare(node.base);
  if (!host || host.kind !== Kind.Name || isLocalBinding(host.binding)) return null;
  return argument.value;
}

const isLookup = (node) => serviceOf(bare(node)) !== null;

function declared(statement) {
  if (!statement || statement.kind !== Kind.LocalDeclaration) return null;
  if ((statement.names || []).length !== 1) return null;
  if ((statement.expressions || []).length !== 1) return null;
  const service = serviceOf(bare(statement.expressions[0]));
  if (service === null) return null;
  return { service, name: statement.names[0], initializer: bare(statement.expressions[0]) };
}

function preludeEnd(statements) {
  let at = 0;
  while (at < statements.length && declared(statements[at])) at += 1;
  return at;
}

function allNames(chunk) {
  const taken = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Name) taken.add(node.name);
      for (const key of ['names', 'params', 'variables']) {
        for (const one of node[key] || []) taken.add(one);
      }
      if (node.kind === Kind.LocalFunction || node.kind === Kind.NumericFor) {
        taken.add(node.name || node.variable);
      }
    },
  });
  return taken;
}

function gather(chunk) {
  const statements = chunk.body ? chunk.body.statements : null;
  if (!statements) return 0;

  const lookups = collect(chunk, (node) => serviceOf(node) !== null);
  if (!lookups.length) return 0;

  const groups = new Map();
  for (const node of lookups) {
    const service = serviceOf(node);
    let group = groups.get(service);
    if (!group) groups.set(service, group = []);
    group.push(node);
  }

  const prelude = preludeEnd(statements);
  const settled = new Map();
  for (let at = 0; at < prelude; at += 1) {
    const found = declared(statements[at]);
    if (!settled.has(found.service)) settled.set(found.service, found);
  }
  const done = (service) => {
    const found = settled.get(service);
    const group = groups.get(service);
    return !!found && group.length === 1 && group[0] === found.initializer;
  };
  if ([...groups.keys()].every(done)) return 0;

  const taken = allNames(chunk);
  const fresh = () => {
    let number = 0;
    for (;;) {
      number += 1;
      const candidate = `service${number}`;
      if (!taken.has(candidate)) {
        taken.add(candidate);
        return candidate;
      }
    }
  };

  const written = [];
  const replacement = new Map();
  for (const [service, group] of groups) {
    let holder = settled.get(service);
    if (!holder) {
      const spelling = bare(group[0].base).name;
      holder = { service, name: fresh(), initializer: null };
      written.push(A.localDecl([holder.name], [
        A.methodCall(A.name(spelling), METHOD, [A.string(service)]),
      ]));
      settled.set(service, holder);
    }
    for (const node of group) {
      if (node === holder.initializer) continue;
      replacement.set(node, A.name(holder.name));
    }
  }

  const dropped = new Set();
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return;
      for (const statement of node.statements) {
        if (statement.kind !== Kind.CallStatement) continue;
        const call = bare(statement.expression);
        if (!replacement.has(call)) continue;
        replacement.delete(call);
        dropped.add(statement);
      }
    },
  });

  const moved = replacement.size + written.length + dropped.size;
  if (!moved) return 0;

  transform(chunk, (node) => replacement.get(node) || node);
  if (dropped.size) {
    walk(chunk, {
      enter(node) {
        if (node.kind !== Kind.Block) return;

        for (let at = node.statements.length - 1; at >= 0; at -= 1) {
          if (dropped.has(node.statements[at])) node.statements.splice(at, 1);
        }
      },
    });
  }
  if (written.length) {
    const body = chunk.body.statements;
    body.splice(preludeEnd(body), 0, ...written);
  }
  return moved;
}

module.exports = { gather, isLookup };
