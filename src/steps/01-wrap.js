'use strict';

const { Kind } = require('../lua/ast');

function matchWrapper(body) {
  if (!body || !body.statements.length) return null;
  const statement = body.statements[body.statements.length - 1];
  if (statement.kind !== Kind.Return || statement.expressions.length !== 1) return null;
  const call = statement.expressions[0];
  if (!call || call.kind !== Kind.Call) return null;

  let callee = call.base;
  while (callee && callee.kind === Kind.Paren) callee = callee.expression;
  if (!callee || callee.kind !== Kind.Function) return null;
  if ((callee.params || []).length !== 0) return null;

  for (const arg of call.args) {
    if (arg.kind !== Kind.Vararg) return null;
  }
  if (call.args.length > 1) return null;
  return callee;
}

function run(context) {
  let unwrapped = 0;
  for (;;) {
    const body = context.chunk.body;
    const fn = matchWrapper(body);
    if (!fn) break;
    body.statements.splice(body.statements.length - 1, 1, ...fn.body.statements);
    unwrapped += 1;
    if (unwrapped > 64) break;
  }
  if (unwrapped) {
    context.note(`removed ${unwrapped} WrapInFunction layer(s)`, unwrapped);
    context.bump('unwrap.layers', unwrapped);
  }
}

module.exports = { name: '01-wrap', run, matchWrapper };
