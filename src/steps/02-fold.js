'use strict';

const { Kind } = require('../lua/ast');
const { transform } = require('../lua/walk');
const C = require('../util/const');

const ARITH = new Set(['+', '-', '*', '/', '%', '^', '..']);
const UNARY = new Set(['-']);

const BINARY = new Set([...ARITH, '==', '~=', '<', '<=', '>', '>=', 'and', 'or']);
const LOGIC = new Set([...UNARY, 'not']);

function foldTree(root, options = {}) {
  const binary = options.binary || ARITH;
  const unary = options.unary || UNARY;
  let folded = 0;
  transform(root, (node) => {
    if (node.kind === Kind.Binary) {
      if (!binary.has(node.operator)) return node;
      const replacement = C.foldBinary(node.operator, node.lhs, node.rhs);
      if (replacement) {
        folded += 1;
        return replacement;
      }
      return node;
    }
    if (node.kind === Kind.Unary) {
      if (!unary.has(node.operator)) return node;
      const replacement = C.foldUnary(node.operator, node.argument);
      if (replacement) {
        folded += 1;
        return replacement;
      }
      return node;
    }
    if (node.kind === Kind.Paren) {
      const inner = node.expression;
      if (inner && C.isConstant(inner)) {
        folded += 1;
        return inner;
      }
      return node;
    }
    return node;
  });
  return folded;
}

function run(context) {
  const folded = foldTree(context.chunk);
  if (folded) {
    context.note(`folded ${folded} constant expression(s)`, folded);
    context.bump('fold.count', folded);
  }
}

module.exports = {
  name: '02-fold',
  run,
  foldTree,
  BINARY,
  LOGIC,
};
