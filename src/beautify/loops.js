'use strict';

const { Kind, unparen, isMultiValue } = require('../lua/ast');
const { walk } = require('../lua/walk');
const { isLocalBinding } = require('../lua/scope');
const { TABLES } = require('../util/purity');
const { isAlwaysTrue } = require('../util/flow');

const RETURNS = {
  ipairs: [null, null, { kind: Kind.Number, value: 0 }],
  pairs: [null, null, { kind: Kind.Nil }],
  gmatch: [null],
  gfind: [null],
  lines: [null],
};

const CONTROLS = 3;

function isLibrary(node) {
  if (!node || node.kind !== Kind.Name) return false;
  return !node.binding || !isLocalBinding(node.binding);
}

function libraryIterator(call) {
  if (!call || call.kind !== Kind.Call) return null;
  const base = unparen(call.base);
  if (!base) return null;
  if (isLibrary(base)) return base.name;
  if (base.kind !== Kind.Index) return null;
  const owner = unparen(base.base);
  if (!isLibrary(owner) || !TABLES.has(owner.name)) return null;
  const key = base.index;
  if (!key || key.kind !== Kind.String) return null;
  return key.value;
}

function spells(node, wanted) {
  const inner = unparen(node);
  if (!inner || !wanted || inner.kind !== wanted.kind) return false;
  if (inner.kind !== Kind.Number) return true;
  return inner.value === wanted.value;
}

function headerFits(loop, call, taken) {
  const spelled = loop.expressions || [];
  if (spelled.length < taken) return false;
  if (spelled.length > CONTROLS) return false;
  if (spelled.length === CONTROLS && taken === CONTROLS) return true;
  const returns = RETURNS[libraryIterator(call)];
  if (!returns) return false;
  for (let at = taken; at < CONTROLS; at += 1) {
    const wanted = at < returns.length ? returns[at] : { kind: Kind.Nil };
    if (!wanted) return false;
    if (at < spelled.length) {
      if (!spells(spelled[at], wanted)) return false;
    } else if (wanted.kind !== Kind.Nil) return false;
  }
  return true;
}

function headerOnly(declaration, loop) {
  const bindings = declaration.bindings || [];
  const names = declaration.names || [];
  if (!bindings.length || bindings.length !== names.length) return false;
  const spelled = loop.expressions || [];
  if (spelled.length < bindings.length) return false;
  return bindings.every((binding, at) => {
    if (!binding || !isLocalBinding(binding)) return false;
    if ((binding.writes || []).length) return false;
    const reads = binding.reads || [];
    if (reads.length !== 1) return false;
    return unparen(spelled[at]) === reads[0];
  });
}

function hoistedCall(statement) {
  if (!statement || statement.kind !== Kind.LocalDeclaration) return null;
  const expressions = statement.expressions || [];
  if (expressions.length !== 1) return null;
  const call = unparen(expressions[0]);
  return isMultiValue(call) ? call : null;
}

function foldable(chunk) {
  const plans = [];
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const statements = node.statements || [];
      statements.forEach((statement, at) => {
        const loop = statements[at + 1];
        if (!loop || loop.kind !== Kind.GenericFor) return;
        const call = hoistedCall(statement);
        if (!call) return;
        if (!headerOnly(statement, loop)) return;
        if (!headerFits(loop, call, (statement.bindings || []).length)) return;
        plans.push({ block: node, declaration: statement, loop, call });
      });
      return undefined;
    },
  });
  return plans;
}

function foldIterators(chunk) {
  const plans = foldable(chunk);
  if (!plans.length) return 0;
  const dropped = new Set();
  for (const plan of plans) {
    plan.loop.expressions = [plan.call];
    dropped.add(plan.declaration);
  }
  for (const plan of plans) {
    plan.block.statements = plan.block.statements.filter((one) => !dropped.has(one));
  }
  return plans.length;
}

function negated(test) {
  if (test && test.kind === Kind.Unary && test.operator === 'not') return test.argument;
  return { kind: Kind.Unary, operator: 'not', argument: test };
}

function breakArm(branch) {
  if ((branch.elseIfs || []).length) return null;
  const lone = (block) => {
    const statements = (block && block.statements) || [];
    return statements.length === 1 && statements[0].kind === Kind.Break;
  };
  if (!branch.elseBody) return null;
  if (lone(branch.elseBody) && !lone(branch.body)) {
    return { condition: branch.condition, body: branch.body };
  }
  if (lone(branch.body) && !lone(branch.elseBody)) {
    return { condition: negated(branch.condition), body: branch.elseBody };
  }
  return null;
}

function raiseTest(chunk) {
  let raised = 0;
  walk(chunk, {
    enter(node) {
      if (node.kind !== Kind.While) return undefined;
      if (!isAlwaysTrue(node.condition)) return undefined;
      const statements = (node.body && node.body.statements) || [];
      if (statements.length !== 1 || statements[0].kind !== Kind.If) return undefined;
      const arm = breakArm(statements[0]);
      if (!arm) return undefined;
      node.condition = arm.condition;
      node.body = arm.body;
      raised += 1;
      return undefined;
    },
  });
  return raised;
}

module.exports = { foldIterators, negated, raiseTest };
