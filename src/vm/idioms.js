'use strict';

const A = require('../lua/ast');
const { Kind } = A;
const { walk, transform, collect } = require('../lua/walk');
const { isAlwaysTrue, bare } = require('../util/flow');
const { isIdentifier } = require('../lua/format');

function sameSimple(a, b) {
  const x = bare(a);
  const y = bare(b);
  if (!x || !y || x.kind !== y.kind) return false;
  if (x.kind === Kind.Name) return x.binding ? x.binding === y.binding : x.name === y.name;
  if (x.kind === Kind.Number || x.kind === Kind.String) return x.value === y.value;
  if (x.kind === Kind.Nil || x.kind === Kind.True || x.kind === Kind.False) return true;
  return false;
}

function nameOf(node) {
  const inner = bare(node);
  return inner && inner.kind === Kind.Name ? inner : null;
}

function matchIncrement(statement) {
  if (!statement || statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  if (targets.length !== 1 || expressions.length !== 1) return null;
  const counter = nameOf(targets[0]);
  const sum = bare(expressions[0]);
  if (!counter || !sum || sum.kind !== Kind.Binary || sum.operator !== '+') return null;
  if (!sameSimple(sum.lhs, counter)) return null;
  return { counter, step: sum.rhs };
}

function matchHalf(node, counter) {
  const conjunction = bare(node);
  if (!conjunction || conjunction.kind !== Kind.Binary || conjunction.operator !== 'and') {
    return null;
  }
  const sides = [bare(conjunction.lhs), bare(conjunction.rhs)];
  const compare = sides.find((side) => side && side.kind === Kind.Binary
    && (side.operator === '>=' || side.operator === '<='));
  const flag = sides.find((side) => side !== compare);
  if (!compare || !flag) return null;
  let negated = false;
  let sign = flag;
  if (sign.kind === Kind.Unary && sign.operator === 'not') {
    negated = true;
    sign = bare(sign.argument);
  }
  if (!sign) return null;
  let operator = compare.operator;
  let variable = compare.lhs;
  let limit = compare.rhs;
  if (counter && !sameSimple(variable, counter)) {
    if (!sameSimple(limit, counter)) return null;
    variable = compare.rhs;
    limit = compare.lhs;
    operator = operator === '>=' ? '<=' : '>=';
  }
  const descending = operator === '>=';

  if (sign.kind === Kind.True || sign.kind === Kind.False) {
    const value = sign.kind === Kind.True ? !negated : negated;
    return {
      descending,
      isNeg: A.boolean(descending ? value : !value),
      counter: variable,
      limit,
    };
  }
  if (sign.kind !== Kind.Name) return null;

  if (descending === negated) return null;
  return {
    descending, isNeg: sign, counter: variable, limit,
  };
}

function matchRange(condition, counter) {
  const test = bare(condition);
  if (!test || test.kind !== Kind.Binary || test.operator !== 'or') return null;
  const left = matchHalf(test.lhs, counter);
  const right = matchHalf(test.rhs, counter);
  if (!left || !right) return null;
  if (left.descending === right.descending) return null;
  if (!sameSimple(left.isNeg, right.isNeg)) return null;
  if (!sameSimple(left.counter, right.counter)) return null;
  if (!sameSimple(left.limit, right.limit)) return null;
  return { counter: left.counter, limit: left.limit, isNeg: left.isNeg };
}

function matchExit(statement, counter) {
  if (!statement || statement.kind !== Kind.If) return null;
  if ((statement.elseIfs || []).length || statement.elseBody) return null;
  const body = (statement.body && statement.body.statements) || [];
  if (body.length !== 1 || body[0].kind !== Kind.Break) return null;
  const test = bare(statement.condition);
  if (!test || test.kind !== Kind.Unary || test.operator !== 'not') return null;
  return matchRange(test.argument, counter);
}

function writtenBindings(root) {
  const written = new Set();
  const add = (node) => {
    const inner = bare(node);
    if (inner && inner.kind === Kind.Name && inner.binding) written.add(inner.binding);
  };
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) (node.targets || []).forEach(add);
      else if (node.kind === Kind.LocalDeclaration) {
        for (const binding of node.bindings || []) written.add(binding);
      } else if (node.kind === Kind.NumericFor) written.add(node.binding);
      else if (node.kind === Kind.GenericFor) {
        for (const binding of node.bindings || []) written.add(binding);
      }
      return undefined;
    },
  });
  return written;
}

function readsBinding(root, binding) {
  let found = false;
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Name && node.binding === binding) found = true;
      return undefined;
    },
  });
  return found;
}

function findStart(statements, at, counter, step) {
  const opening = (value, index) => {
    const difference = bare(value);
    if (!difference) return null;
    if (difference.kind === Kind.Binary && difference.operator === '-'
      && sameSimple(difference.rhs, step)) {
      return { start: difference.lhs, index };
    }

    const increment = bare(step);
    if (difference.kind === Kind.Number && increment && increment.kind === Kind.Number) {
      return { start: A.number(difference.value + increment.value), index };
    }
    return null;
  };
  for (let i = at - 1; i >= 0; i -= 1) {
    const statement = statements[i];
    if (statement.kind === Kind.LocalDeclaration) {
      const bindings = statement.bindings || [];
      const expressions = statement.expressions || [];
      const slot = bindings.indexOf(counter.binding);
      if (slot < 0) continue;
      if (expressions.length !== bindings.length) return null;
      return opening(expressions[slot], i);
    }
    if (statement.kind !== Kind.Assignment) {
      if (writtenBindings(statement).has(counter.binding)) return null;
      continue;
    }
    const targets = statement.targets || [];
    const expressions = statement.expressions || [];
    const writesCounter = targets.some((target) => sameSimple(target, counter));
    if (!writesCounter) continue;
    if (targets.length !== 1 || expressions.length !== 1) return null;
    return opening(expressions[0], i);
  }
  return null;
}

function rebuildNumericFor(block, at) {
  const loop = block.statements[at];
  if (!loop || loop.kind !== Kind.While || !isAlwaysTrue(loop.condition)) return false;
  const body = (loop.body && loop.body.statements) || [];
  if (body.length < 2) return false;
  const increment = matchIncrement(body[0]);
  if (!increment) return false;
  const range = matchExit(body[1], increment.counter);
  if (!range) return false;
  if (!sameSimple(range.counter, increment.counter)) return false;
  if (!increment.counter.binding) return false;

  const rest = A.block(body.slice(2));
  const written = writtenBindings(rest);

  for (const node of [increment.counter, increment.step, range.limit, range.isNeg]) {
    const named = nameOf(node);
    if (named && named.binding && written.has(named.binding)) return false;
  }
  if (range.isNeg.binding && readsBinding(rest, range.isNeg.binding)) return false;

  const flag = bare(range.isNeg);
  const stride = bare(increment.step);
  if (flag && (flag.kind === Kind.True || flag.kind === Kind.False)
    && stride && stride.kind === Kind.Number && (stride.value < 0) !== (flag.kind === Kind.True)) {
    return false;
  }

  const opening = findStart(block.statements, at, increment.counter, increment.step);
  if (!opening) return false;

  let variable = increment.counter;
  const held = rest.statements;
  for (let k = 0; k < held.length; k += 1) {
    const copy = singleAssign(held[k]);
    if (!copy || !sameSimple(copy.value, increment.counter)) continue;
    if (copy.target.binding === increment.counter.binding) break;
    const ahead = A.block(held.slice(0, k));
    const behind = A.block(held.slice(k + 1));
    if (readsBinding(ahead, increment.counter.binding)) break;
    if (readsBinding(behind, increment.counter.binding)) break;
    if (readsBinding(ahead, copy.target.binding)) break;
    if (writtenBindings(ahead).has(copy.target.binding)) break;
    variable = copy.target;
    rest.statements = held.slice(0, k).concat(held.slice(k + 1));
    break;
  }

  for (const binding of new Set([increment.counter.binding, variable.binding])) {
    for (let i = at + 1; i < block.statements.length; i += 1) {
      const statement = block.statements[i];
      if (readsBinding(statement, binding)) return false;
      if (writtenBindings(statement).has(binding)) break;
    }
  }

  block.statements[at] = A.numericFor(
    variable.name,
    opening.start,
    range.limit,
    increment.step,
    rest,
  );
  return true;
}

function lastWriteBefore(statements, at, binding) {
  for (let i = at - 1; i >= 0; i -= 1) {
    if (writtenBindings(statements[i]).has(binding)) return i;
  }
  return -1;
}

function seedingWrite(statement, target) {
  if (!statement) return null;
  if ((statement.expressions || []).length !== 1) return null;
  if (statement.kind === Kind.LocalDeclaration) {
    if ((statement.names || []).length !== 1) return null;
    if ((statement.bindings || [])[0] !== target.binding) return null;
    return { holder: statement, value: statement.expressions[0], declared: true };
  }
  if (statement.kind !== Kind.Assignment) return null;
  if ((statement.targets || []).length !== 1) return null;
  if (!sameSimple(statement.targets[0], target)) return null;
  return { holder: statement, value: statement.expressions[0], declared: false };
}

function fuseConditional(block, at) {
  const statements = block.statements;
  const branch = statements[at];
  if (!branch || branch.kind !== Kind.If) return false;
  if ((branch.elseIfs || []).length || branch.elseBody) return false;
  const body = (branch.body && branch.body.statements) || [];
  if (body.length !== 1) return false;
  const move = body[0];
  if (!move || move.kind !== Kind.Assignment) return false;
  if ((move.targets || []).length !== 1 || (move.expressions || []).length !== 1) return false;
  const target = nameOf(move.targets[0]);
  if (!target || !target.binding) return false;
  const value = bare(move.expressions[0]);
  if (!value || value.kind === Kind.Vararg) return false;
  if (readsBinding(value, target.binding)) return false;

  let condition = bare(branch.condition);
  let operator = 'and';
  if (condition && condition.kind === Kind.Unary && condition.operator === 'not') {
    condition = bare(condition.argument);
    operator = 'or';
  }
  const guard = nameOf(condition);
  if (!guard || !guard.binding) return false;
  if (guard.binding === target.binding) return false;

  const previous = lastWriteBefore(statements, at, target.binding);
  if (previous < 0) return false;
  const seed = seedingWrite(statements[previous], target);
  if (!seed || !sameSimple(seed.value, guard)) return false;
  for (let i = previous + 1; i < at; i += 1) {
    if (writtenBindings(statements[i]).has(guard.binding)) return false;
  }

  const fused = A.binary(operator, A.name(guard.name), value);
  if (seed.declared) {
    if (previous !== at - 1) return false;
    seed.holder.expressions = [fused];
    statements[at] = A.doStatement(A.block([]));
    return true;
  }
  statements[at] = A.assignment([A.name(target.name)], [fused]);
  return true;
}

function restoreMethodCall(node) {
  if (node.kind !== Kind.Call) return null;
  const args = node.args || [];
  if (!args.length) return null;
  const callee = bare(node.base);
  if (!callee || callee.kind !== Kind.Index) return null;
  const key = bare(callee.index);
  if (!key || key.kind !== Kind.String || !isIdentifier(key.value)) return null;
  if (!sameSimple(callee.base, args[0])) return null;
  return A.methodCall(callee.base, key.value, args.slice(1));
}

function singleAssign(statement) {
  if (!statement || statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  if (targets.length !== 1 || expressions.length !== 1) return null;
  const target = nameOf(targets[0]);
  if (!target || !target.binding) return null;
  return { target, value: expressions[0] };
}

function indexAt(node) {
  const key = bare(node);
  if (!key || key.kind !== Kind.Number) return null;
  if (!Number.isInteger(key.value) || key.value < 1) return null;
  return key.value;
}

function settled(node) {
  const named = nameOf(node);
  if (named) return named.binding ? named : null;
  const inner = bare(node);
  return A.isLiteral(inner) ? inner : null;
}

function usage(root) {
  const reads = new Map();
  const writes = new Map();
  const stored = new Set();
  const note = (map, binding, node) => {
    if (!binding) return;
    const list = map.get(binding);
    if (list) list.push(node);
    else map.set(binding, [node]);
  };
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        for (const target of node.targets || []) {
          const named = bare(target);
          if (named && named.kind === Kind.Name) {
            stored.add(named);
            note(writes, named.binding, node);
          }
        }
      } else if (node.kind === Kind.LocalDeclaration) {
        if ((node.expressions || []).length) {
          for (const binding of node.bindings || []) note(writes, binding, node);
        }
      } else if (node.kind === Kind.NumericFor) note(writes, node.binding, node);
      else if (node.kind === Kind.GenericFor) {
        for (const binding of node.bindings || []) note(writes, binding, node);
      } else if (node.kind === Kind.Name) note(reads, node.binding, node);
      return undefined;
    },
  });
  for (const [binding, list] of reads) {
    reads.set(binding, list.filter((node) => !stored.has(node)));
  }
  return { reads, writes };
}

function countReads(root, binding) {
  let found = 0;
  const stored = new Set();
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        for (const target of node.targets || []) {
          const named = bare(target);
          if (named && named.kind === Kind.Name) stored.add(named);
        }
      }
      if (node.kind === Kind.Name && node.binding === binding && !stored.has(node)) {
        found += 1;
      }
      return undefined;
    },
  });
  return found;
}

function countWrites(root, binding) {
  let found = 0;
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Assignment) {
        for (const target of node.targets || []) {
          const named = bare(target);
          if (named && named.kind === Kind.Name && named.binding === binding) found += 1;
        }
      } else if (node.kind === Kind.LocalDeclaration && (node.expressions || []).length) {
        for (const held of node.bindings || []) if (held === binding) found += 1;
      } else if (node.kind === Kind.NumericFor) {
        if (node.binding === binding) found += 1;
      } else if (node.kind === Kind.GenericFor) {
        for (const held of node.bindings || []) if (held === binding) found += 1;
      }
      return undefined;
    },
  });
  return found;
}

function spreadCall(block, at, use) {
  const statements = block.statements;
  const pack = singleAssign(statements[at]);
  if (!pack) return false;
  const held = bare(pack.value);
  if (!held || held.kind !== Kind.Table) return false;
  const entries = held.entries || [];
  if (entries.length !== 1 || entries[0].type === 'key') return false;

  const call = entries[0].value;
  if (!call || (call.kind !== Kind.Call && call.kind !== Kind.MethodCall)) return false;
  const holder = pack.target.binding;
  if ((use.writes.get(holder) || []).length !== 1) return false;

  const taken = [];
  for (let i = at + 1; i < statements.length; i += 1) {
    const slot = singleAssign(statements[i]);
    if (!slot) continue;
    const read = bare(slot.value);
    if (!read || read.kind !== Kind.Index) continue;
    const base = nameOf(read.base);
    if (!base || base.binding !== holder) continue;
    const key = indexAt(read.index);
    if (key === null) return false;
    taken.push({ at: i, key, target: slot.target, binding: slot.target.binding });
  }
  if (!taken.length) return false;

  if (countReads(block, holder) !== taken.length) return false;
  if ((use.reads.get(holder) || []).length !== taken.length) return false;

  const keys = new Set(taken.map((slot) => slot.key));
  if (keys.size !== taken.length) return false;
  for (let key = 1; key <= taken.length; key += 1) if (!keys.has(key)) return false;
  const filled = new Set(taken.map((slot) => slot.binding));
  if (filled.size !== taken.length || filled.has(holder)) return false;

  const moving = new Set(taken.map((slot) => slot.at));
  for (let i = at + 1; i < taken[taken.length - 1].at; i += 1) {
    if (moving.has(i)) continue;
    const written = writtenBindings(statements[i]);
    if (written.has(holder)) return false;
    for (const binding of filled) {
      if (written.has(binding) || readsBinding(statements[i], binding)) return false;
    }
  }

  const order = taken.slice().sort((a, b) => a.key - b.key);

  statements[at] = A.assignment(order.map((slot) => slot.target), [call]);

  for (const slot of taken) statements[slot.at] = A.doStatement(A.block([]));
  return true;
}

function matchIterate(statement) {
  if (!statement || statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  if (!targets.length || targets.length > 2 || expressions.length !== 1) return null;
  const call = expressions[0];
  if (!call || call.kind !== Kind.Call) return null;
  const args = call.args || [];
  if (args.length !== 2) return null;
  const ctrl = nameOf(targets[0]);
  if (!ctrl || !ctrl.binding) return null;
  if (!sameSimple(args[1], ctrl)) return null;
  const second = targets.length === 2 ? nameOf(targets[1]) : null;
  if (targets.length === 2 && (!second || !second.binding)) return null;

  const iterator = settled(call.base);
  const state = settled(args[0]);
  if (!iterator || !state) return null;
  return { ctrl, second, iterator, state };
}

function matchNilExit(statement, ctrl) {
  if (!statement || statement.kind !== Kind.If) return false;
  if ((statement.elseIfs || []).length || statement.elseBody) return false;
  const body = (statement.body && statement.body.statements) || [];
  if (body.length !== 1 || body[0].kind !== Kind.Break) return false;
  const test = bare(statement.condition);
  if (!test) return false;
  if (test.kind === Kind.Unary && test.operator === 'not') {
    return sameSimple(test.argument, ctrl);
  }
  if (test.kind === Kind.Binary && test.operator === '==') {
    const empty = bare(test.rhs);
    return !!empty && empty.kind === Kind.Nil && sameSimple(test.lhs, ctrl);
  }
  return false;
}

function collapseTriple(statements, at, wanted, within, use) {
  if (wanted.length !== 3 || wanted.some((binding) => !binding)) return null;
  if (new Set(wanted).size !== 3) return null;
  const source = lastWriteBefore(statements, at, wanted[2]);
  if (source < 0) return null;
  const statement = statements[source];
  if (!statement || statement.kind !== Kind.Assignment) return null;
  const targets = statement.targets || [];
  const expressions = statement.expressions || [];
  if (targets.length !== 3 || expressions.length !== 1) return null;
  const call = expressions[0];
  if (!call || (call.kind !== Kind.Call && call.kind !== Kind.MethodCall)) return null;
  const named = targets.map(nameOf);
  if (named.some((node) => !node || !node.binding)) return null;
  for (let i = 0; i < 3; i += 1) if (named[i].binding !== wanted[i]) return null;

  for (const binding of wanted) {
    const reads = (use.reads.get(binding) || []).length;
    if (!reads || reads !== countReads(within, binding)) return null;
    const writes = (use.writes.get(binding) || []).length;
    if (writes - countWrites(within, binding) !== 1) return null;
  }
  statements[source] = A.doStatement(A.block([]));
  return call;
}

function rebuildGenericFor(block, at, use) {
  const statements = block.statements;
  const loop = statements[at];
  if (!loop || loop.kind !== Kind.While || !isAlwaysTrue(loop.condition)) return false;
  const body = (loop.body && loop.body.statements) || [];
  if (body.length < 2) return false;
  const step = matchIterate(body[0]);
  if (!step) return false;
  if (!matchNilExit(body[1], step.ctrl)) return false;

  let cut = 2;
  let first = step.ctrl;
  const copy = singleAssign(body[2]);
  if (copy && sameSimple(copy.value, step.ctrl) && copy.target.binding !== step.ctrl.binding) {
    first = copy.target;
    cut = 3;
  }
  const rest = A.block(body.slice(cut));
  const written = writtenBindings(rest);
  for (const node of [step.iterator, step.state]) {
    if (node.binding && written.has(node.binding)) return false;
  }

  if (written.has(step.ctrl.binding)) return false;
  if (first !== step.ctrl && readsBinding(rest, step.ctrl.binding)) return false;
  if (step.second && step.second.binding === step.ctrl.binding) return false;

  const scoped = [step.ctrl.binding, first.binding];
  if (step.second) scoped.push(step.second.binding);
  for (const binding of scoped) {
    for (let i = at + 1; i < statements.length; i += 1) {
      if (readsBinding(statements[i], binding)) return false;
      if (writtenBindings(statements[i]).has(binding)) break;
    }
  }

  const variables = [first.name];
  if (step.second) variables.push(step.second.name);

  const wanted = [step.iterator.binding, step.state.binding, step.ctrl.binding];
  const packed = collapseTriple(statements, at, wanted, loop, use);
  const expressions = packed
    ? [packed]
    : [step.iterator, step.state, A.name(step.ctrl.name)];
  statements[at] = A.genericFor(variables, expressions, rest);
  return true;
}

function spreadAll(block, at, use) {
  const statements = block.statements;
  const pack = singleAssign(statements[at]);
  if (!pack) return false;
  const held = bare(pack.value);
  if (!held || held.kind !== Kind.Table) return false;
  const entries = held.entries || [];
  if (entries.length !== 1 || entries[0].type === 'key') return false;
  const call = entries[0].value;
  if (!call || (call.kind !== Kind.Call && call.kind !== Kind.MethodCall)) return false;
  const binding = pack.target.binding;
  if ((use.writes.get(binding) || []).length !== 1) return false;
  if ((use.reads.get(binding) || []).length !== 1) return false;

  let spreadAt = -1;
  let spread = null;
  for (let i = at + 1; i < statements.length; i += 1) {
    const found = findSpread(statements[i], binding);
    if (!found) continue;
    spreadAt = i;
    spread = found;
    break;
  }
  if (!spread) return false;
  if (countReads(statements[spreadAt], binding) !== 1) return false;

  const reads = readBindings(call);
  for (let i = at + 1; i < spreadAt; i += 1) {
    if (!movable(statements[i])) return false;
    for (const written of writtenBindings(statements[i])) {
      if (reads.has(written)) return false;
    }
  }

  let done = false;
  statements[spreadAt] = transform(statements[spreadAt], (node) => {
    if (done || node !== spread) return node;
    done = true;
    return call;
  });
  if (!done) return false;
  statements[at] = A.doStatement(A.block([]));
  return true;
}

function globalRead(node, name) {
  const inner = bare(node);
  if (!inner) return false;
  if (inner.kind === Kind.Name) {
    if (inner.name !== name) return false;
    return !inner.binding || inner.binding.kind === 'global';
  }
  if (inner.kind !== Kind.Index) return false;
  const key = bare(inner.index);
  if (!key || key.kind !== Kind.String || key.value !== name) return false;
  const base = bare(inner.base);
  if (!base || base.kind !== Kind.Name) return false;
  if (base.binding && base.binding.kind !== 'global') return false;
  return base.name === '_ENV' || base.name === '_G';
}

function spreadsTable(node) {
  if (globalRead(node, 'unpack')) return true;
  const inner = bare(node);
  if (!inner || inner.kind !== Kind.Index) return false;
  const key = bare(inner.index);
  if (!key || key.kind !== Kind.String || key.value !== 'unpack') return false;
  return globalRead(inner.base, 'table');
}

function readBindings(root) {
  const found = new Set();
  walk(root, {
    enter(node) {
      if (node.kind === Kind.Name && node.binding) found.add(node.binding);
      return undefined;
    },
  });
  return found;
}

function movable(statement) {
  if (!statement) return false;
  if (statement.kind === Kind.Do) {
    return !((statement.body && statement.body.statements) || []).length;
  }
  if (statement.kind !== Kind.Assignment) return false;
  for (const target of statement.targets || []) {
    const named = bare(target);
    if (!named || named.kind !== Kind.Name || !named.binding) return false;
  }
  for (const expression of statement.expressions || []) {
    const inner = bare(expression);
    if (!inner) return false;
    if (inner.kind === Kind.Function || A.isLiteral(inner)) continue;
    if (inner.kind === Kind.Name && inner.binding) continue;
    return false;
  }
  return true;
}

function findSpread(statement, binding) {
  let found = null;
  let several = false;
  walk(statement, {
    enter(node) {
      if (node.kind !== Kind.Call) return undefined;
      if (!spreadsTable(node.base)) return undefined;
      const args = node.args || [];
      if (args.length !== 1) return undefined;
      const named = nameOf(args[0]);
      if (!named || named.binding !== binding) return undefined;
      if (found) several = true;
      found = node;
      return undefined;
    },
  });
  return several ? null : found;
}

function collapseHeader(block, at, use) {
  const loop = block.statements[at];
  if (!loop || loop.kind !== Kind.GenericFor) return false;
  const expressions = loop.expressions || [];
  if (expressions.length !== 3) return false;
  const named = expressions.map(nameOf);
  if (named.some((node) => !node || !node.binding)) return false;
  const wanted = named.map((node) => node.binding);
  const packed = collapseTriple(block.statements, at, wanted, loop, use);
  if (!packed) return false;
  loop.expressions = [packed];
  return true;
}

function headerSlots(loop) {
  if (!loop) return null;
  if (loop.kind === Kind.NumericFor) {
    return ["start", "limit", "step"].map((key) => ({
      read: () => loop[key],
      write: (value) => { loop[key] = value; },
      last: false,
    }));
  }
  if (loop.kind === Kind.GenericFor) {
    const count = (loop.expressions || []).length;
    return (loop.expressions || []).map((ignored, index) => ({
      read: () => loop.expressions[index],
      write: (value) => { loop.expressions[index] = value; },
      last: index === count - 1,
    }));
  }
  return null;
}

function statementAbove(statements, at) {
  for (let i = at - 1; i >= 0; i -= 1) {
    const statement = statements[i];
    if (statement.kind !== Kind.Do) return i;
    if (((statement.body && statement.body.statements) || []).length) return i;
  }
  return -1;
}

function inlineHeader(block, at, use) {
  const statements = block.statements;
  const loop = statements[at];
  const slots = headerSlots(loop);
  if (!slots) return false;
  let rebuilt = false;
  for (let round = 0; round < slots.length; round += 1) {
    const above = statementAbove(statements, at);
    if (above < 0) break;
    const assign = singleAssign(statements[above]);
    if (!assign) break;
    const holder = assign.target.binding;
    if ((use.reads.get(holder) || []).length !== 1) break;
    if (countReads(loop, holder) !== 1) break;
    if ((use.writes.get(holder) || []).length !== 1) break;
    if (countWrites(loop, holder) !== 0) break;
    const slot = slots.find((one) => {
      const named = nameOf(one.read());
      return !!named && named.binding === holder;
    });
    if (!slot) break;
    if (slot.last && A.isMultiValue(bare(assign.value))) break;
    slot.write(assign.value);
    statements[above] = A.doStatement(A.block([]));
    rebuilt = true;
  }
  return rebuilt;
}

function copyValue(node) {
  if (Array.isArray(node)) return node.map(copyValue);
  if (!node || typeof node !== 'object') return node;
  const copy = {};
  for (const key of Object.keys(node)) {
    if (key === 'binding' || key === 'bindings' || key === 'declaration') copy[key] = node[key];
    else copy[key] = copyValue(node[key]);
  }
  return copy;
}

function packedItems(node) {
  if (!node) return null;
  const inner = bare(node);
  if (!inner || inner.kind !== Kind.Table) return null;
  const entries = inner.entries || [];
  if (!entries.length) return null;
  const items = [];
  for (const entry of entries) {
    if (entry.type !== 'item') return null;
    items.push(entry.value);
  }
  return items;
}

function spreadArgument(node) {
  if (!node || node.kind !== Kind.Call) return null;
  if (!spreadsTable(node.base)) return null;
  const args = node.args || [];
  return args.length === 1 ? args[0] : null;
}

function selectParts(node) {
  if (!node || node.kind !== Kind.Call) return null;
  if (!globalRead(node.base, 'select')) return null;
  const args = node.args || [];
  if (args.length !== 2) return null;
  const index = bare(args[0]);
  if (!index || index.kind !== Kind.Number) return null;
  if (!Number.isInteger(index.value) || index.value < 1) return null;
  return { skip: index.value - 1, values: args[1] };
}

function droppable(node) {
  const inner = bare(node);
  if (!inner) return false;
  return inner.kind === Kind.Name || A.isLiteral(inner);
}

function varargPack(items) {
  if (!items || !items.length) return false;
  if (!A.isMultiValue(items[items.length - 1])) return false;
  for (let i = 0; i < items.length - 1; i += 1) {
    if (!droppable(items[i])) return false;
  }
  return true;
}

function passVarargs(node) {
  const spread = spreadArgument(node);
  if (spread) {
    const items = packedItems(spread);

    if (!items || items.length !== 1 || !varargPack(items)) return null;
    return items[0];
  }
  const parts = selectParts(node);
  if (!parts) return null;

  if (!parts.skip) return A.isMultiValue(parts.values) ? parts.values : null;
  const items = packedItems(spreadArgument(parts.values));
  if (!items || !varargPack(items)) return null;

  if (items.length !== parts.skip + 1) return null;
  return items[items.length - 1];
}

function carriesVarargs(items) {
  if (!items || items.length !== 1) return false;
  const inner = bare(items[0]);
  return !!inner && inner.kind === Kind.Vararg;
}

function ownersOf(root, wanted) {
  const owners = new Map();
  const stack = [root];
  walk(root, {
    enter(node) {
      if (wanted.has(node)) owners.set(node, stack[stack.length - 1]);
      if (node.kind === Kind.Function) stack.push(node);
      return undefined;
    },
    leave(node) {
      if (node.kind === Kind.Function) stack.pop();
    },
  });
  return owners;
}

function inlineVarargPack(root, statements, at, use) {
  const assign = singleAssign(statements[at]);
  if (!assign) return false;
  const holder = assign.target.binding;
  if (!holder) return false;
  const packed = bare(assign.value);
  const items = packedItems(packed);
  if (!carriesVarargs(items)) return false;
  const writes = use.writes.get(holder) || [];
  if (writes.length !== 1 || writes[0] !== statements[at]) return false;
  const reads = use.reads.get(holder) || [];
  if (!reads.length) return false;
  const spreads = collect(root, (node) => {
    const inner = bare(spreadArgument(node));
    return !!inner && inner.kind === Kind.Name && inner.binding === holder;
  });

  if (spreads.length !== reads.length) return false;

  const owners = ownersOf(root, new Set([statements[at]].concat(spreads)));
  const home = owners.get(statements[at]);
  if (!home) return false;
  for (const spread of spreads) {
    if (owners.get(spread) !== home) return false;
  }
  transform(root, (node) => {
    if (spreads.indexOf(node) < 0) return node;
    return A.call(node.base, [copyValue(packed)]);
  });

  statements[at] = A.doStatement(A.block([]));
  return true;
}

function run(context, counters) {
  let rebuilt = 0;
  walk(context.chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;

      for (let i = 0; i < node.statements.length; i += 1) {
        if (fuseConditional(node, i)) rebuilt += 1;
      }
      for (let i = 0; i < node.statements.length; i += 1) {
        if (rebuildNumericFor(node, i)) rebuilt += 1;
      }
      return undefined;
    },
  });

  const packs = usage(context.chunk);
  walk(context.chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let i = 0; i < node.statements.length; i += 1) {
        if (spreadAll(node, i, packs)) rebuilt += 1;
      }
      for (let i = 0; i < node.statements.length; i += 1) {
        if (spreadCall(node, i, packs)) rebuilt += 1;
      }
      return undefined;
    },
  });
  const spread = usage(context.chunk);
  walk(context.chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let i = 0; i < node.statements.length; i += 1) {
        if (rebuildGenericFor(node, i, spread)) rebuilt += 1;
      }
      for (let i = 0; i < node.statements.length; i += 1) {
        if (inlineHeader(node, i, spread)) rebuilt += 1;
      }
      for (let i = 0; i < node.statements.length; i += 1) {
        if (collapseHeader(node, i, spread)) rebuilt += 1;
      }
      return undefined;
    },
  });

  const carried = usage(context.chunk);
  const packed = [];
  walk(context.chunk, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let i = 0; i < node.statements.length; i += 1) packed.push([node.statements, i]);
      return undefined;
    },
  });
  for (const [statements, at] of packed) {
    if (inlineVarargPack(context.chunk, statements, at, carried)) rebuilt += 1;
  }

  transform(context.chunk, (node) => {
    const passed = passVarargs(node);
    if (passed) {
      rebuilt += 1;
      return passed;
    }
    const method = restoreMethodCall(node);
    if (!method) return node;
    rebuilt += 1;
    return method;
  });
  if (counters) counters.idioms += rebuilt;
  return rebuilt;
}

module.exports = { run, usage, movable };
