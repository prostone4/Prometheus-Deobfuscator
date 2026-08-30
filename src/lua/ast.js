'use strict';

const Kind = {
  Chunk: 'Chunk',
  Block: 'Block',

  LocalDeclaration: 'LocalDeclaration',
  LocalFunction: 'LocalFunction',
  FunctionDeclaration: 'FunctionDeclaration',
  Assignment: 'Assignment',
  CallStatement: 'CallStatement',
  Return: 'Return',
  Break: 'Break',
  Continue: 'Continue',
  Do: 'Do',
  While: 'While',
  Repeat: 'Repeat',
  If: 'If',
  NumericFor: 'NumericFor',
  GenericFor: 'GenericFor',
  Goto: 'Goto',
  Label: 'Label',

  Nil: 'Nil',
  True: 'True',
  False: 'False',
  Number: 'Number',
  String: 'String',
  Vararg: 'Vararg',
  Function: 'Function',
  Table: 'Table',
  Binary: 'Binary',
  Unary: 'Unary',
  Index: 'Index',
  Call: 'Call',
  MethodCall: 'MethodCall',
  Name: 'Name',
  Paren: 'Paren',
};

const EXPRS = new Set([
  Kind.Nil, Kind.True, Kind.False, Kind.Number, Kind.String, Kind.Vararg,
  Kind.Function, Kind.Table, Kind.Binary, Kind.Unary, Kind.Index, Kind.Call,
  Kind.MethodCall, Kind.Name, Kind.Paren,
]);

const LITERALS = new Set([Kind.Nil, Kind.True, Kind.False, Kind.Number, Kind.String]);

const ASSIGNABLE = new Set([Kind.Name, Kind.Index]);

const MULTIVAL = new Set([Kind.Call, Kind.MethodCall, Kind.Vararg]);

const block = (statements = []) => ({ kind: Kind.Block, statements });
const chunk = (body) => ({ kind: Kind.Chunk, body: body || block() });
const nil = () => ({ kind: Kind.Nil });
const boolean = (value) => ({ kind: value ? Kind.True : Kind.False });
const number = (value) => ({ kind: Kind.Number, value });
const string = (value) => ({ kind: Kind.String, value });
const vararg = () => ({ kind: Kind.Vararg });
const name = (id) => ({ kind: Kind.Name, name: id });
const paren = (expression) => ({ kind: Kind.Paren, expression });
const binary = (operator, lhs, rhs) => ({ kind: Kind.Binary, operator, lhs, rhs });
const unary = (operator, argument) => ({ kind: Kind.Unary, operator, argument });
const index = (base, key, dot = false) => ({ kind: Kind.Index, base, index: key, dot });
const call = (base, args = []) => ({ kind: Kind.Call, base, args });
const methodCall = (base, method, args = []) => ({ kind: Kind.MethodCall, base, method, args });
const table = (entries = []) => ({ kind: Kind.Table, entries });
const func = (params, body, isVararg = false) => ({
  kind: Kind.Function, params, body: body || block(), isVararg,
});

const localDecl = (names, expressions = []) => ({
  kind: Kind.LocalDeclaration, names, expressions,
});
const assignment = (targets, expressions) => ({ kind: Kind.Assignment, targets, expressions });
const callStatement = (expression) => ({ kind: Kind.CallStatement, expression });
const returnStatement = (expressions = []) => ({ kind: Kind.Return, expressions });
const breakStatement = () => ({ kind: Kind.Break });
const doStatement = (body) => ({ kind: Kind.Do, body });
const whileStatement = (condition, body) => ({ kind: Kind.While, condition, body });
const repeatStatement = (body, condition) => ({ kind: Kind.Repeat, body, condition });
const ifStatement = (condition, body, elseIfs = [], elseBody = null) => ({
  kind: Kind.If, condition, body, elseIfs, elseBody,
});
const numericFor = (variable, start, limit, step, body) => ({
  kind: Kind.NumericFor, variable, start, limit, step, body,
});
const genericFor = (variables, expressions, body) => ({
  kind: Kind.GenericFor, variables, expressions, body,
});

const unparen = (node) => {
  let current = node;
  while (current && current.kind === Kind.Paren) current = current.expression;
  return current;
};

const isLiteral = (node) => !!node && LITERALS.has(node.kind);
const isMultiValue = (node) => !!node && MULTIVAL.has(node.kind);
const isExpression = (node) => !!node && EXPRS.has(node.kind);

module.exports = {
  Kind,
  LITERALS,
  ASSIGNABLE,
  isLiteral,
  unparen,
  isMultiValue,
  isExpression,
  block,
  chunk,
  nil,
  boolean,
  number,
  string,
  vararg,
  name,
  paren,
  binary,
  unary,
  index,
  call,
  methodCall,
  table,
  func,
  localDecl,
  assignment,
  callStatement,
  returnStatement,
  breakStatement,
  doStatement,
  whileStatement,
  repeatStatement,
  ifStatement,
  numericFor,
  genericFor,
};
