'use strict';

const { Kind } = require('./ast');

const PARAS = 4;
const RECORDS = 4;

function rootName(node) {
  let current = node;
  for (let guard = 0; guard < 1000 && current; guard += 1) {
    switch (current.kind) {
      case Kind.Name: return current.name;
      case Kind.Paren: current = current.expression; break;
      case Kind.Index: current = current.base; break;
      case Kind.Call:
      case Kind.MethodCall: current = current.base; break;
      default: return null;
    }
  }
  return null;
}

function subjectOf(statement) {
  if (!statement) return null;
  switch (statement.kind) {
    case Kind.LocalDeclaration: return (statement.names || [])[0] || null;
    case Kind.LocalFunction: return statement.name || null;
    case Kind.FunctionDeclaration: return rootName(statement.target);
    case Kind.Assignment: return rootName((statement.targets || [])[0]);
    case Kind.CallStatement: return rootName(statement.expression);
    default: return null;
  }
}

function groups(statements) {
  const index = [];
  const sizes = [];
  let current = -1;
  let subject = null;
  (statements || []).forEach((statement, at) => {
    const found = subjectOf(statement);
    if (at === 0 || found === null || subject === null || found !== subject) {
      current += 1;
      sizes.push(0);
    }
    index.push(current);
    sizes[current] += 1;
    subject = found;
  });
  return { index, sizes, count: index.length };
}

function separates(found, at, wide, above) {
  if (!at) return false;
  if (wide || above) return true;
  if (found.count < PARAS) return false;
  const here = found.index[at];
  const before = found.index[at - 1];
  if (here === before) return false;
  return found.sizes[here] >= 2 || found.sizes[before] >= 2;
}

function record(entries) {
  let keys = 0;
  for (const entry of entries) {
    if (entry.type === 'key') keys += 1;
  }
  return keys >= RECORDS;
}

module.exports = { rootName, groups, record, separates };
