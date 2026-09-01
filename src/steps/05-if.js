'use strict';

const { Kind } = require('../lua/ast');
const { isGlobalName } = require('../lua/scope');
const { transform, walk } = require('../lua/walk');
const { diverges, divergesBlock, bare } = require('../util/flow');
const C = require('../util/const');

function isPure(node) {
  if (!node) return true;
  const inner = bare(node);
  if (!inner) return true;
  switch (inner.kind) {
    case Kind.Name:
    case Kind.Nil: case Kind.True: case Kind.False:
    case Kind.Number: case Kind.String: case Kind.Vararg:
      return true;
    case Kind.Unary:
      return isPure(inner.argument);
    case Kind.Binary:
      return isPure(inner.lhs) && isPure(inner.rhs);
    default:
      return false;
  }
}

function inlined(block) {
  return { kind: Kind.Do, body: block, inlineHint: true };
}

function resolveGuard(statement, counters) {
  const clauses = [
    { condition: statement.condition, body: statement.body },
    ...(statement.elseIfs || []).map((clause) => ({ ...clause })),
  ];
  const otherwise = statement.elseBody;
  if (!otherwise) return null;
  if (!clauses.every((clause) => isPure(clause.condition))) return null;

  const exits = clauses.map((clause) => divergesBlock(clause.body));
  const elseExits = divergesBlock(otherwise);
  const live = exits.filter((value) => !value).length + (elseExits ? 0 : 1);
  if (live !== 1) return null;

  counters.guards += 1;
  if (!elseExits) return inlined(otherwise);
  const at = exits.indexOf(false);
  return inlined(clauses[at].body);
}

function isWatermark(statement) {
  if (statement.kind !== Kind.CallStatement) return false;
  const call = bare(statement.expression);
  if (!call || call.kind !== Kind.MethodCall || call.method !== 'gsub') return false;
  const subject = bare(call.base);
  if (!subject || subject.kind !== Kind.String) return false;
  const args = call.args || [];
  if (args.length !== 2) return false;
  const pattern = bare(args[0]);
  if (!pattern || pattern.kind !== Kind.String) return false;
  const fn = bare(args[1]);
  if (!fn || fn.kind !== Kind.Function) return false;
  const body = (fn.body && fn.body.statements) || [];
  if (body.length !== 1 || body[0].kind !== Kind.Assignment) return false;
  const targets = body[0].targets || [];
  return targets.length === 1 && isGlobalName(targets[0]);
}

function isWatermarkCheck(statement) {
  if (statement.kind !== Kind.If) return false;
  if ((statement.elseIfs || []).length) return false;
  const body = (statement.body && statement.body.statements) || [];
  if (body.length !== 1 || body[0].kind !== Kind.Return) return false;
  if ((body[0].expressions || []).length) return false;
  const test = bare(statement.condition);
  if (!test || test.kind !== Kind.Binary || test.operator !== '~=') return false;
  const sides = [bare(test.lhs), bare(test.rhs)];
  const global = sides.find((side) => isGlobalName(side));
  const literal = sides.find((side) => side && side.kind === Kind.String);
  return !!global && !!literal;
}

function resolveConstant(statement, counters) {
  const clauses = [
    { condition: statement.condition, body: statement.body },
    ...(statement.elseIfs || []).map((clause) => ({ ...clause })),
  ];
  const kept = [];
  let taken = null;
  for (const clause of clauses) {
    const value = C.truthiness(clause.condition);
    if (value === false) continue;
    if (value === true) {
      taken = clause;
      break;
    }
    kept.push(clause);
  }
  const otherwise = taken ? taken.body : statement.elseBody;
  const dropped = clauses.length - kept.length - (taken ? 1 : 0);
  if (!dropped && !taken) return null;
  counters.constants += 1;
  if (!kept.length) {
    return inlined(otherwise || { kind: Kind.Block, statements: [] });
  }
  return {
    kind: Kind.If,
    condition: kept[0].condition,
    body: kept[0].body,
    elseIfs: kept.slice(1),
    elseBody: otherwise,
  };
}

function flattenMarkers(root) {
  let merged = 0;
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      const out = [];
      for (const statement of node.statements) {
        if (statement.kind === Kind.Do && statement.inlineHint) {
          merged += 1;
          out.push(...((statement.body && statement.body.statements) || []));
        } else out.push(statement);
      }
      node.statements = out;
      return undefined;
    },
  });
  return merged;
}

function isAntiTamperGuard(statement, blockStatements, index) {
  if (statement.kind !== Kind.If) return false;
  if (statement.elseIfs && statement.elseIfs.length > 0) return false;
  if (statement.elseBody && statement.elseBody.statements && statement.elseBody.statements.length > 0) {
    if (!divergesBlock(statement.elseBody)) return false;
  }

  const cond = bare(statement.condition);
  if (!cond || cond.kind !== Kind.Name) return false;

  const flagName = cond.name;
  const binding = cond.binding;

  const preceding = blockStatements.slice(0, index);
  let hasTamperCheck = false;
  let flagInitialized = false;

  for (const prev of preceding) {
    walk(prev, {
      enter(node) {
        if (node.kind === Kind.String && typeof node.value === 'string' && /tamper/i.test(node.value)) {
          hasTamperCheck = true;
        }
        if (node.kind === Kind.Call && node.base && node.base.kind === Kind.Name && node.base.name === 'error') {
          if (node.args && node.args.length && node.args[0].kind === Kind.String && /tamper/i.test(node.args[0].value)) {
            hasTamperCheck = true;
          }
        }
        if (node.kind === Kind.Assignment) {
          for (let i = 0; i < (node.targets || []).length; i += 1) {
            const target = bare(node.targets[i]);
            if (target && target.kind === Kind.Name && (target.name === flagName || (binding && target.binding === binding))) {
              const expr = (node.expressions || [])[i];
              if (expr && (expr.kind === Kind.True || C.truthiness(expr) === true)) {
                flagInitialized = true;
              }
            }
          }
        }
        return undefined;
      },
    });
  }

  return hasTamperCheck && flagInitialized;
}

function pruneBlock(block, counters) {
  const out = [];
  for (let i = 0; i < block.statements.length; i += 1) {
    const statement = block.statements[i];
    if (isAntiTamperGuard(statement, block.statements, i)) {
      counters.guards += 1;
      const inner = (statement.body && statement.body.statements) || [];
      out.push(...inner);
      continue;
    }
    if (statement.kind === Kind.Repeat && !(statement.body.statements || []).length) {
      if (isPure(statement.condition)) {
        counters.loops += 1;
        continue;
      }
    }
    if (statement.kind === Kind.While && C.truthiness(statement.condition) === false) {
      counters.loops += 1;
      continue;
    }
    if (isWatermark(statement)) {
      counters.watermarks += 1;
      continue;
    }
    if (isWatermarkCheck(statement)) {
      counters.watermarks += 1;

      if (statement.elseBody) out.push(inlined(statement.elseBody));
      continue;
    }
    out.push(statement);
  }
  block.statements = out;
}

function pruneUnreachable(root, counters) {
  walk(root, {
    enter(node) {
      if (node.kind !== Kind.Block) return undefined;
      for (let i = 0; i < node.statements.length; i += 1) {
        const statement = node.statements[i];
        const stops = statement.kind === Kind.Return || statement.kind === Kind.Break
          || diverges(statement);
        if (stops && i + 1 < node.statements.length) {
          counters.unreachable += node.statements.length - i - 1;
          node.statements.length = i + 1;
          break;
        }
      }
      return undefined;
    },
  });
}

function run(context) {
  const counters = {
    guards: 0, constants: 0, loops: 0, watermarks: 0, unreachable: 0,
  };
  for (let pass = 0; pass < 16; pass += 1) {
    const before = { ...counters };
    context.resolve();
    transform(context.chunk, (node) => {
      if (node.kind !== Kind.If) return node;
      const constant = resolveConstant(node, counters);
      if (constant) return constant;
      const guard = resolveGuard(node, counters);
      if (guard) return guard;
      return node;
    });
    flattenMarkers(context.chunk);
    walk(context.chunk, {
      enter(node) {
        if (node.kind === Kind.Block) pruneBlock(node, counters);
        return undefined;
      },
    });
    pruneUnreachable(context.chunk, counters);
    const changed = Object.keys(counters).some((key) => counters[key] !== before[key]);
    if (!changed) break;
  }
  const total = counters.guards + counters.constants + counters.loops + counters.watermarks;
  if (total) {
    context.note(
      `resolved ${counters.guards} integrity guard(s), ${counters.constants} constant branch(es),`
      + ` dropped ${counters.loops} dead loop(s) and ${counters.watermarks} watermark(s)`,
      total,
    );
  }
  for (const key of Object.keys(counters)) {
    if (counters[key]) context.bump(`guards.${key}`, counters[key]);
  }
}

module.exports = { name: '05-if', run };
