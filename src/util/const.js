'use strict';

const { Kind } = require('../lua/ast');
const A = require('../lua/ast');
const ops = require('../interp/ops');
const V = require('../interp/values');

const RT = {
  metamethod: () => undefined,
  call() {
    throw new Error('pure eval: calls not allowed');
  },
  addressOf: () => '0',
};

const NONE = Symbol('none');

function literalValue(node) {
  if (!node) return NONE;
  switch (node.kind) {
    case Kind.Nil: return undefined;
    case Kind.True: return true;
    case Kind.False: return false;
    case Kind.Number: return node.value;
    case Kind.String: return node.value;
    case Kind.Paren: return literalValue(node.expression);
    default: return NONE;
  }
}

const isConstant = (node) => literalValue(node) !== NONE;

function truthiness(node) {
  if (!node) return null;
  if (node.kind === Kind.Paren) return truthiness(node.expression);
  if (node.kind === Kind.Table || node.kind === Kind.Function) return true;
  const value = literalValue(node);
  if (value === NONE) return null;
  return value !== undefined && value !== false;
}

function literalNode(value) {
  if (value === undefined || value === null) return A.nil();
  if (value === true) return A.boolean(true);
  if (value === false) return A.boolean(false);
  if (typeof value === 'number') return A.number(value);
  if (typeof value === 'string') return A.string(value);
  return null;
}

function foldBinary(operator, lhsNode, rhsNode) {
  const a = literalValue(lhsNode);
  const b = literalValue(rhsNode);
  if (a === NONE || b === NONE) return null;
  try {
    switch (operator) {
      case 'and': return literalNode(V.truthy(a) ? b : a);
      case 'or': return literalNode(V.truthy(a) ? a : b);
      case '..': {
        if (typeof a !== 'string' && typeof a !== 'number') return null;
        if (typeof b !== 'string' && typeof b !== 'number') return null;
        return literalNode(ops.concat(RT, a, b));
      }
      case '==': return literalNode(ops.equals(RT, a, b));
      case '~=': return literalNode(!ops.equals(RT, a, b));
      case '<': return literalNode(ops.lessThan(RT, a, b));
      case '>': return literalNode(ops.lessThan(RT, b, a));
      case '<=': return literalNode(ops.lessOrEqual(RT, a, b));
      case '>=': return literalNode(ops.lessOrEqual(RT, b, a));
      default: {
        if (typeof a === 'boolean' || typeof b === 'boolean') return null;
        if (a === undefined || b === undefined) return null;
        return literalNode(ops.arith(RT, operator, a, b));
      }
    }
  } catch (error) {
    return null;
  }
}

function foldUnary(operator, argumentNode) {
  const a = literalValue(argumentNode);
  if (a === NONE) return null;
  try {
    switch (operator) {
      case '-': return typeof a === 'boolean' || a === undefined ? null
        : literalNode(ops.unaryMinus(RT, a));
      case 'not': return literalNode(!V.truthy(a));

      case '#': return null;
      default: return null;
    }
  } catch (error) {
    return null;
  }
}

module.exports = {
  literalNode,
  isConstant,
  truthiness,
  foldBinary,
  foldUnary,
};
