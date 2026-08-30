'use strict';

const { Kind, isMultiValue } = require('../lua/ast');
const { walk } = require('../lua/walk');

function endsBare(block) {
  const statements = (block && block.statements) || [];
  const last = statements[statements.length - 1];
  return !!last && last.kind === Kind.Return && !(last.expressions || []).length;
}

function dropReturns(chunk) {
  let dropped = 0;
  const trim = (block) => {
    if (!endsBare(block)) return;
    block.statements.pop();
    dropped += 1;
  };
  walk(chunk, {
    enter(node) {
      if (node.kind === Kind.Chunk) trim(node.body);
      else if (node.kind === Kind.Function) trim(node.body);
      return undefined;
    },
  });
  return dropped;
}

function loneIf(block) {
  const statements = (block && block.statements) || [];
  if (statements.length !== 1) return null;
  const only = statements[0];
  return only && only.kind === Kind.If ? only : null;
}

function collapseElseIf(chunk) {
  let collapsed = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.If) return undefined;
      for (let guard = 0; guard < 1000; guard += 1) {
        const inner = loneIf(node.elseBody);
        if (!inner) break;
        node.elseIfs = (node.elseIfs || []).concat(
          [{ condition: inner.condition, body: inner.body }],
          inner.elseIfs || [],
        );
        node.elseBody = inner.elseBody || null;
        collapsed += 1;
      }
      return undefined;
    },
  });
  return collapsed;
}

function isTruncated(node) {
  return node && node.kind === Kind.Paren && isMultiValue(node.expression);
}

function unwrapAt(node, key) {
  if (!isTruncated(node[key])) return 0;
  node[key] = node[key].expression;
  return 1;
}

function unwrapList(list, upTo) {
  let dropped = 0;
  for (let at = 0; at < upTo && at < (list || []).length; at += 1) {
    if (!isTruncated(list[at])) continue;
    list[at] = list[at].expression;
    dropped += 1;
  }
  return dropped;
}

function truncatedCount(list, slots) {
  const count = (list || []).length;
  if (!count) return 0;
  if (slots !== null && slots - count + 1 <= 1) return count;
  return count - 1;
}

function dropParens(chunk) {
  let dropped = 0;
  walk(chunk, {
    enter(node) {
      switch (node.kind) {
        case Kind.Index:
          dropped += unwrapAt(node, 'base') + unwrapAt(node, 'index');
          break;
        case Kind.Call:
        case Kind.MethodCall:
          dropped += unwrapAt(node, 'base');
          dropped += unwrapList(node.args, truncatedCount(node.args, null));
          break;
        case Kind.Binary:
          dropped += unwrapAt(node, 'lhs') + unwrapAt(node, 'rhs');
          break;
        case Kind.Unary:
          dropped += unwrapAt(node, 'argument');
          break;
        case Kind.Paren:
          dropped += unwrapAt(node, 'expression');
          break;
        case Kind.Table:
          (node.entries || []).forEach((entry, at) => {
            if (entry.type === 'key') dropped += unwrapAt(entry, 'key');
            const last = at === node.entries.length - 1;
            if (!last || entry.type === 'key') dropped += unwrapAt(entry, 'value');
          });
          break;
        case Kind.If:
          dropped += unwrapAt(node, 'condition');
          for (const clause of node.elseIfs || []) dropped += unwrapAt(clause, 'condition');
          break;
        case Kind.While:
        case Kind.Repeat:
          dropped += unwrapAt(node, 'condition');
          break;
        case Kind.NumericFor:
          dropped += unwrapAt(node, 'start') + unwrapAt(node, 'limit')
            + unwrapAt(node, 'step');
          break;
        case Kind.Return:
          dropped += unwrapList(node.expressions, truncatedCount(node.expressions, null));
          break;
        case Kind.GenericFor:
          dropped += unwrapList(node.expressions, truncatedCount(node.expressions, 3));
          break;
        case Kind.LocalDeclaration:
          dropped += unwrapList(
            node.expressions,
            truncatedCount(node.expressions, (node.names || []).length),
          );
          break;
        case Kind.Assignment:
          dropped += unwrapList(
            node.expressions,
            truncatedCount(node.expressions, (node.targets || []).length),
          );
          break;
        default:
          break;
      }
      return undefined;
    },
  });
  return dropped;
}

function opensNothing(block) {
  return ((block && block.statements) || []).every((statement) => statement.kind !== Kind.Label
    && statement.kind !== Kind.LocalDeclaration && statement.kind !== Kind.LocalFunction);
}

function flatten(chunk) {
  let flattened = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const kept = [];
      for (const statement of node.statements) {
        const inner = statement.kind === Kind.Do ? statement.body : null;
        if (inner && opensNothing(inner)) {
          for (const one of inner.statements || []) kept.push(one);
          flattened += 1;
        } else kept.push(statement);
      }
      node.statements = kept;
      return undefined;
    },
  });
  return flattened;
}

const EXITS = new Set([Kind.Return, Kind.Break, Kind.Continue]);

function alwaysLeaves(block) {
  const statements = (block && block.statements) || [];
  const last = statements[statements.length - 1];
  return !!last && EXITS.has(last.kind);
}

function liftElse(chunk) {
  let lifted = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const statements = node.statements;
      for (let at = 0; at < statements.length; at += 1) {
        const branch = statements[at];
        if (!branch || branch.kind !== Kind.If) continue;
        if (!alwaysLeaves(branch.body)) continue;
        if ((branch.elseIfs || []).length) continue;
        const otherwise = branch.elseBody;
        if (!otherwise || !opensNothing(otherwise) || loneIf(otherwise)) continue;
        branch.elseBody = null;
        statements.splice(at + 1, 0, ...(otherwise.statements || []));
        lifted += 1;
      }
      return undefined;
    },
  });
  return lifted;
}

function dropElse(chunk) {
  let dropped = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.If || !node.elseBody) return undefined;
      if ((node.elseBody.statements || []).length) return undefined;
      node.elseBody = null;
      dropped += 1;
      return undefined;
    },
  });
  return dropped;
}

module.exports = {
  EXITS,
  liftElse,
  dropReturns,
  dropElse,
  collapseElseIf,
  dropParens,
  flatten,
};
