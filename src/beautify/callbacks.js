'use strict';

const { Kind } = require('../lua/ast');
const { walk, transform } = require('../lua/walk');
const { isLocalBinding } = require('../lua/scope');
const { bare } = require('../util/flow');
const copies = require('./copies');
const M = require('./moves');

function closureOf(statement) {
  const declared = copies.declaredFunction(statement);
  if (declared) return declared;
  const plain = M.plainDeclaration(statement);
  if (!plain) return null;
  const value = bare(plain.value);
  if (!value || value.kind !== Kind.Function) return null;
  return { binding: plain.binding, name: plain.name, value };
}

function declaredIn(root) {
  const own = new Set();
  const note = (binding) => { if (binding) own.add(binding); };
  walk(root, {
    enter(node) {
      for (const binding of node.bindings || []) note(binding);
      if (node.kind === Kind.LocalFunction || node.kind === Kind.NumericFor) note(node.binding);
      return undefined;
    },
  });
  return own;
}

function capturesSafe(value, counts) {
  const own = declaredIn(value);
  for (const binding of M.readsWithin(value)) {
    if (own.has(binding)) continue;
    const text = binding.name;
    if (!text) return false;
    if (isLocalBinding(binding) ? !M.unshadowed(counts, text) : counts.has(text)) return false;
  }
  return true;
}

function mentionsOf(block) {
  const index = new Map();
  block.statements.forEach((statement, at) => {
    let depth = 0;
    walk(statement, {
      enter(node) {
        if (node.kind === Kind.Block) depth += 1;
        else if (node.kind === Kind.Name && node.binding) {
          const row = index.get(node.binding);
          if (row) row.count += 1;
          else index.set(node.binding, { count: 1, node, at, direct: depth === 0 });
        }
        return undefined;
      },
      leave(node) {
        if (node.kind === Kind.Block) depth -= 1;
      },
    });
  });
  return index;
}

function inlineAt(block, at, declared, index, counts) {
  const statements = block.statements;
  const row = index.get(declared.binding);
  if (!row || row.count !== 1 || !row.direct || row.at <= at) return false;
  const read = row.node;

  if (statements.some((statement) => statement.kind === Kind.Label)) return false;

  const host = statements[row.at];
  if (host.kind === Kind.While || host.kind === Kind.Repeat) return false;
  if (copies.readsInto(host, read)) return false;
  if (!capturesSafe(declared.value, counts)) return false;

  transform(host, (node) => (node === read ? declared.value : node));
  statements[at] = { kind: Kind.Do, body: { kind: Kind.Block, statements: [] } };
  return true;
}

function inlineClosures(chunk) {
  let moved = 0;
  const counts = M.nameCounts(chunk);
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      let index = null;
      for (let at = 0; at < node.statements.length; at += 1) {
        const declared = closureOf(node.statements[at]);
        if (!declared || !isLocalBinding(declared.binding)) continue;
        if (!index) index = mentionsOf(node);
        if (inlineAt(node, at, declared, index, counts)) moved += 1;
      }
      return undefined;
    },
  });
  return moved;
}

module.exports = {
  inlineClosures,
};
