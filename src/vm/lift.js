'use strict';

const A = require('../lua/ast');
const { Kind } = A;
const { isIdentifier } = require('../lua/format');
const { walk, transform } = require('../lua/walk');
const {
  buildWebs, entryKey, defKey, liveness,
} = require('./webs');
const { bindingOf, unparen } = require('./detect');
const {
  REF, LIVE, mapNode, definition, peel, isCalling,
} = require('./ir');
const { structureFunction } = require('./structure');

const isBinding = (node, binding) => !!binding && bindingOf(node) === binding;

const upvalsTest = (vm) => vm.container.isUpvals
  || ((node) => isBinding(node, vm.container.upvals));
const allocTest = (vm) => (vm.upvalues && vm.upvalues.isAlloc)
  || ((node) => !!vm.upvalues && isBinding(node, vm.upvalues.alloc));
const tableTest = (vm) => (vm.upvalues && vm.upvalues.isTable)
  || ((node) => !!vm.upvalues && isBinding(node, vm.upvalues.table));
const refsTest = (vm) => (vm.upvalues && vm.upvalues.isRefs)
  || ((node) => !!vm.upvalues && isBinding(node, vm.upvalues.refs));

function numericIndexOn(node, binding) {
  if (!node || node.kind !== Kind.Index) return null;
  if (!isBinding(node.base, binding)) return null;
  const key = unparen(node.index);
  return key && key.kind === Kind.Number ? key.value : null;
}

function unrepack(body) {
  return transform(body, (node) => {
    if (node.kind !== Kind.Call || (node.args || []).length !== 1) return node;
    if (!node.base || node.base.kind !== Kind.Name || node.base.name !== 'unpack') return node;
    const list = resultList(node.args[0]);
    return list && list.length === 1 ? list[0] : node;
  });
}

function dropTailContinue(statements) {
  while (statements.length && statements[statements.length - 1].kind === Kind.Continue) {
    statements.pop();
  }
  const last = statements[statements.length - 1];
  if (!last || last.kind !== Kind.If) return statements;
  dropTailContinue(last.body.statements);
  for (const clause of last.elseIfs || []) dropTailContinue(clause.body.statements);
  if (last.elseBody) {
    dropTailContinue(last.elseBody.statements);
    if (!last.elseBody.statements.length) last.elseBody = null;
  }
  return statements;
}

function isCellToken(token) {
  return typeof token === 'string'
    && (token.startsWith('alloc:') || token.startsWith('param:'));
}

function numericIndexWhere(node, accepts, resolve) {
  if (!node || node.kind !== Kind.Index) return null;
  if (!accepts(resolve(node.base))) return null;
  const key = unparen(resolve(node.index));
  return key && key.kind === Kind.Number ? key.value : null;
}

function stringIndexOn(node, binding) {
  if (!node || node.kind !== Kind.Index) return null;
  if (!isBinding(node.base, binding)) return null;
  const key = unparen(node.index);
  return key && key.kind === Kind.String ? key.value : null;
}

function eachExpression(fn, visitor) {
  let current = null;
  const walkNode = (node) => {
    if (!node || typeof node !== 'object') return;
    if (visitor(node, current) === false) return;
    if (node.kind === REF || node.kind === LIVE) return;
    mapNode(node, (child) => {
      walkNode(child);
      return child;
    });
  };
  for (const block of fn.blocks) {
    current = block;
    for (const statement of block.statements) {
      for (const expression of statement.exprs) walkNode(expression);
      for (const target of statement.targets) if (target.node) walkNode(target.node);
    }
  }
}

function analyzeArgs(vm, fn) {
  let arity = 0;
  let usesTable = false;
  const args = vm.container.args;
  eachExpression(fn, (node, block) => {
    if (node.kind === Kind.Index && isBinding(node.base, args)) {
      const key = unparen(peel(block, node.index));
      if (key && key.kind === Kind.Number && Number.isInteger(key.value) && key.value > 0) {
        arity = Math.max(arity, key.value);
        return false;
      }
    }
    if (node.kind === Kind.Name && bindingOf(node) === args) usesTable = true;
    return undefined;
  });
  return { arity, usesTable };
}

function collectRefs(node, out) {
  if (!node || typeof node !== 'object') return;
  if (node.kind === REF) {
    out.push(node);
    return;
  }
  if (node.kind === LIVE) return;
  mapNode(node, (child) => {
    collectRefs(child, out);
    return child;
  });
}

function collectLive(node, out) {
  if (!node || typeof node !== 'object') return;
  if (node.kind === LIVE) {
    out.add(node.reg);
    return;
  }
  if (node.kind === REF) return;
  mapNode(node, (child) => {
    collectLive(child, out);
    return child;
  });
}

const TOP = Symbol('top');

function copyExpression(node) {
  if (!node || typeof node !== 'object') return node;
  const copy = mapNode(node, copyExpression);
  delete copy.binding;
  delete copy.bindings;
  return copy;
}

function isRepack(node) {
  return !!node && node.kind === Kind.Call && node.base && node.base.kind === Kind.Name
    && node.base.name === 'unpack' && (node.args || []).length === 1;
}

function resultList(expr) {
  if (!expr) return null;
  if (expr.kind === Kind.Paren) {
    const bare = unparen(expr);
    return A.isMultiValue(bare) ? null : resultList(bare);
  }
  const inner = expr;
  if (inner.kind === Kind.Table) {
    const entries = inner.entries || [];
    if (!entries.every((entry) => entry.type === 'item')) return null;
    const values = entries.map((entry) => entry.value);

    if (values.length === 1 && isRepack(values[0])) {
      const nested = resultList(values[0]);
      if (nested) return nested;
    }
    return values;
  }
  if (isRepack(inner)) return resultList(inner.args[0]);
  return null;
}

const negated = (expr, flag) => {
  if (!flag) return expr;
  if (expr && expr.kind === Kind.Unary && expr.operator === 'not') return expr.argument;
  return A.unary('not', expr);
};

function analyzeUpvalues(vm, fn) {
  const isUpvals = upvalsTest(vm);
  const isAlloc = allocTest(vm);

  const tokenFromExpression = (block, node, state, tokens) => {
    if (!node) return TOP;
    if (node.kind === REF) return tokens.get(`${node.index}.${node.slot}`) || TOP;
    if (node.kind === LIVE) return state.get(node.reg) || TOP;
    const behind = (operand) => peel(block, operand);
    const slot = numericIndexWhere(node, isUpvals, behind);
    if (slot !== null) return `param:${slot}`;
    if (node.kind === Kind.Call && isAlloc(behind(node.base))) {
      return `alloc:${block.id}:${node.allocSite}`;
    }
    return TOP;
  };

  for (const block of fn.blocks) {
    block.statements.forEach((statement, index) => {
      for (const expression of statement.exprs) {
        if (expression && expression.kind === Kind.Call
          && isAlloc(peel(block, expression.base))) {
          expression.allocSite = index;
        }
      }
    });
  }
  const entryState = new Map();
  const exitState = new Map();
  for (const block of fn.blocks) {
    entryState.set(block, new Map());
    exitState.set(block, new Map());
  }

  const { liveIn: liveBefore, liveOut: liveAfter } = liveness(fn);
  const NONE = new Set();
  const restrict = (state, live) => {
    const out = new Map();
    for (const reg of live) {
      const token = state.get(reg);
      if (token !== undefined) out.set(reg, token);
    }
    return out;
  };

  const transfer = (block) => {
    const state = new Map(entryState.get(block));
    const tokens = new Map();
    block.statements.forEach((statement, index) => {
      const single = statement.targets.length === 1 && statement.exprs.length === 1;
      statement.targets.forEach((target, slot) => {
        const token = single
          ? tokenFromExpression(block, statement.exprs[0], state, tokens)
          : TOP;
        tokens.set(`${index}.${slot}`, token);
        if (target.reg) state.set(target.reg, token);
      });
    });
    block.upvalueTokens = tokens;
    return restrict(state, liveAfter.get(block) || NONE);
  };

  const join = (block, fn2) => {
    const live = liveBefore.get(block) || NONE;
    const merged = new Map();
    for (const pred of block.predecessors) {
      if (!fn2.members.has(pred.id)) continue;
      const state = exitState.get(pred);
      if (!state || !state.size) continue;
      for (const reg of live) {
        const token = state.get(reg);
        if (token === undefined) continue;
        if (!merged.has(reg)) merged.set(reg, token);
        else if (merged.get(reg) !== token) merged.set(reg, TOP);
      }
    }
    return merged;
  };

  for (let round = 0; round < 1000; round += 1) {
    let changed = false;
    for (const block of fn.blocks) {
      const merged = block === fn.entry ? new Map() : join(block, fn);
      const previous = entryState.get(block);
      let differs = previous.size !== merged.size;
      if (!differs) for (const [k, v] of merged) if (previous.get(k) !== v) { differs = true; break; }
      if (differs) {
        entryState.set(block, merged);
        changed = true;
      }
      const out = transfer(block);
      const before = exitState.get(block);
      let outDiffers = before.size !== out.size;
      if (!outDiffers) for (const [k, v] of out) if (before.get(k) !== v) { outDiffers = true; break; }
      if (outDiffers) {
        exitState.set(block, out);
        changed = true;
      }
    }
    if (!changed) break;
  }

  for (const block of fn.blocks) block.upvalueEntry = entryState.get(block);
  return { entryState, exitState, tokenFromExpression };
}
class Lifter {
  constructor(vm, cfg, options = {}) {
    this.vm = vm;
    this.cfg = cfg;
    this.options = options;
    this.warnings = [];
    this.counter = options.counter || 0;
    this.byId = new Map(cfg.functions.map((fn) => [fn.id, fn]));
    this.vmBindings = new Set(vm.wrapper && vm.wrapper.bindings ? vm.wrapper.bindings : []);
    this.roleBindings = new Set(Object.keys(vm.roles).map((key) => vm.roles[key]));
    this.roleOf = new Map(Object.keys(vm.roles).map((key) => [vm.roles[key], key]));
    this.isUpvalueTable = tableTest(vm);
    this.isRefsTable = refsTest(vm);
    this.isRefHelper = (vm.upvalues && vm.upvalues.isHelper) || (() => false);
    this.active = new Set();
  }

  fresh(prefix) {
    this.counter += 1;
    return `${prefix}${this.counter}`;
  }

  warn(kind, detail) {
    this.warnings.push({ kind, ...detail });
  }

  creatorFor(node) {
    if (!node) return null;
    if (this.vm.creatorFor) return this.vm.creatorFor(node);
    const binding = bindingOf(node);
    return (binding && this.vm.creators.get(binding)) || null;
  }

  isHelperCall(block, node) {
    if (!node || node.kind !== Kind.Call) return false;
    const callee = peel(block, node.base);
    const binding = bindingOf(callee);
    if (!binding) return false;
    if (!this.vmBindings.has(binding) && !this.isRefHelper(callee)) return false;
    if (this.roleBindings.has(binding)) return false;
    if (this.creatorFor(callee)) return false;
    if (binding === this.vm.containerBinding) return false;
    return true;
  }

  tokenAt(block, index, slot) {
    return block.upvalueTokens ? block.upvalueTokens.get(`${index}.${slot}`) : TOP;
  }

  isNoise(block, statement, index) {
    for (const target of statement.targets) {
      if (target.node && this.isRefsTable(peel(block, target.node.base))) return true;
    }
    if (statement.exprs.length === 1 && this.isHelperCall(block, statement.exprs[0])) {
      return statement.targets.every((target) => target.reg !== null);
    }

    if (statement.targets.length && !statement.ordered
      && statement.targets.every((target, slot) => target.reg
        && isCellToken(this.tokenAt(block, index, slot)))) {
      return true;
    }
    return false;
  }

  varFor(ctx, key) {
    let existing = ctx.regVars.get(key);
    if (!existing) {
      existing = this.fresh('v');
      ctx.regVars.set(key, existing);
    }
    ctx.used.add(existing);
    return existing;
  }

  cellFor(ctx, token) {
    if (token === TOP || token === undefined || token === null) return null;
    const existing = ctx.cells.get(token);
    if (existing) {
      ctx.used.add(existing);
      return existing;
    }
    if (typeof token !== 'string' || !token.startsWith('alloc:')) return null;
    const name = this.fresh('u');
    ctx.cells.set(token, name);
    ctx.cellToken.set(name, token);
    ctx.used.add(name);
    return name;
  }

  argsTable(ctx) {
    const entries = ctx.params.map((name) => ({ type: 'item', value: A.name(name) }));
    entries.push({ type: 'item', value: A.vararg() });
    return A.table(entries);
  }

  roleValue(role) {
    if (role === 'varargs') {
      const given = this.options.varargs;
      return given ? copyExpression(given) : A.table([{ type: 'item', value: A.vararg() }]);
    }
    if (role === 'env') return A.name('_ENV');
    return A.name(role);
  }

  renderVm(node, ctx, render) {
    const vm = this.vm;
    const container = vm.container;
    if (node.kind === Kind.Index) {
      const base = peel(ctx.block, node.base);
      if (this.isUpvalueTable(base)) {
        const name = this.cellFor(ctx, ctx.tokenOf(node.index));
        if (name) return A.name(name);
      }
      const onEnv = isBinding(base, vm.roles.env);
      const onArgs = isBinding(base, container.args);
      if (onEnv || onArgs) {
        const key = unparen(render(node.index));
        if (onEnv) {
          if (key && key.kind === Kind.String && isIdentifier(key.value)) return A.name(key.value);
          return A.index(A.name('_ENV'), key);
        }
        if (key && key.kind === Kind.Number && Number.isInteger(key.value)
          && key.value >= 1 && key.value <= ctx.params.length) {
          return A.name(ctx.params[key.value - 1]);
        }
        return A.index(this.argsTable(ctx), key);
      }
    }
    if (node.kind === Kind.Call) {
      const creator = this.creatorFor(peel(ctx.block, node.base));
      if (creator) {
        const lifted = this.liftSite(node, ctx);
        if (lifted) return lifted;
      }
    }
    if (node.kind === Kind.Name) {
      const binding = bindingOf(node);
      if (binding && binding === container.args) {
        return this.argsTable(ctx);
      }
      const role = binding ? this.roleOf.get(binding) : null;
      if (role) return this.roleValue(role);
    }
    return mapNode(node, render);
  }

  liftSite(node, ctx) {
    const args = node.args || [];
    const id = unparen(peel(ctx.block, args[0]));
    if (!id || id.kind !== Kind.Number) return null;
    const fn = this.byId.get(id.value);
    if (!fn) {
      this.warn('missing-closure', { id: id.value, block: ctx.block.id });
      return null;
    }
    return this.liftFunction(fn, this.closureUpvalues(args[1], ctx), ctx.depth + 1);
  }

  closureUpvalues(expression, ctx) {
    let node = expression;
    for (let guard = 0; guard < 64 && node && node.kind === REF; guard += 1) {
      node = definition(ctx.block, node);
    }
    const inner = node ? unparen(node) : null;
    if (!inner || inner.kind !== Kind.Table) {
      if (expression) this.warn('opaque-upvalues', { block: ctx.block.id });
      return [];
    }
    return (inner.entries || []).map((entry, i) => {
      if (entry.type !== 'item') return null;
      const token = ctx.tokenOf(entry.value);
      const name = this.cellFor(ctx, token);
      if (!name) {
        this.warn('opaque-upvalue', { block: ctx.block.id, slot: i + 1, token: String(token) });
      }
      return name;
    });
  }

  prepareBlock(block, ctx) {
    const cached = ctx.emitters.get(block);
    if (cached) return cached;
    const emitter = {
      block, statements: [], condition: null, returns: null,
    };
    ctx.emitters.set(block, emitter);
    this.fillEmitter(emitter, block, ctx);
    return emitter;
  }

  fillEmitter(emitter, block, ctx) {
    const vm = this.vm;
    const stmts = block.statements;
    const term = block.terminator;
    const keyOf = (i, slot) => `${i}.${slot}`;

    const nameOfEntry = (reg) => ctx.webs.find(entryKey(block, reg));
    const nameOfDef = (i, slot) => ctx.webs.find(defKey(block, i, slot));
    ctx.block = block;

    const writes = new Map();
    stmts.forEach((statement, i) => statement.targets.forEach((target) => {
      if (!target.reg) return;
      if (!writes.has(target.reg)) writes.set(target.reg, []);
      writes.get(target.reg).push(i);
    }));
    const lastWrite = (reg) => {
      const list = writes.get(reg);
      return list ? list[list.length - 1] : -1;
    };

    const refsCache = new Map();
    const refsOf = (i) => {
      let list = refsCache.get(i);
      if (list) return list;
      list = [];
      for (const expr of stmts[i].exprs) collectRefs(expr, list);
      for (const target of stmts[i].targets) if (target.node) collectRefs(target.node, list);
      refsCache.set(i, list);
      return list;
    };
    const liveOf = (i) => {
      const set = new Set();
      for (const expr of stmts[i].exprs) collectLive(expr, set);
      for (const target of stmts[i].targets) if (target.node) collectLive(target.node, set);
      return set;
    };
    const condRefs = [];
    if (term.kind === 'branch') collectRefs(term.condition, condRefs);

    const condTargets = new Set(condRefs.map((node) => node.index));
    const control = new Set();
    const stack = term.index === null || term.index === undefined ? [] : [term.index];
    while (stack.length) {
      const i = stack.pop();
      if (control.has(i)) continue;
      control.add(i);
      for (const node of refsOf(i)) {
        if (condTargets.has(node.index)) continue;
        const target = stmts[node.index].targets[node.slot];
        if (target && target.reg === vm.posKey) stack.push(node.index);
      }
    }
    stmts.forEach((statement, i) => {
      if (this.isNoise(block, statement, i)) control.add(i);
    });

    let retAt = null;
    const canLeave = term.kind === 'return' || term.kind === 'unknown'
      || (term.kind === 'branch' && term.whenFalse === null);
    if (canLeave) {
      const list = (writes.get(vm.returnKey) || []).filter((i) => !control.has(i));
      const candidate = list.length ? list[list.length - 1] : null;
      if (candidate !== null) {
        let read = condRefs.some((node) => node.index === candidate);
        for (let i = candidate + 1; !read && i < stmts.length; i += 1) {
          read = refsOf(i).some((node) => node.index === candidate);
        }
        if (!read) {
          retAt = candidate;
          control.add(candidate);
        }
      }
    }
    const tailRefs = retAt === null ? [] : refsOf(retAt);

    const body = [];
    for (let i = 0; i < stmts.length; i += 1) if (!control.has(i)) body.push(i);

    const plan = (pinned) => {
      const drop = new Set();
      const counts = new Map();
      const host = new Map();
      for (let round = 0; round <= stmts.length + 1; round += 1) {
        counts.clear();
        host.clear();
        const bump = (list, at) => {
          for (const node of list) {
            const key = keyOf(node.index, node.slot);
            counts.set(key, (counts.get(key) || 0) + 1);
            host.set(key, at);
          }
        };
        for (const i of body) if (!drop.has(i)) bump(refsOf(i), i);
        bump(tailRefs, stmts.length);
        bump(condRefs, stmts.length);
        let changed = false;
        for (const i of body) {
          if (drop.has(i) || this.isNeeded(block, stmts[i], i, counts, pinned, lastWrite)) continue;
          drop.add(i);
          changed = true;
        }
        if (!changed) break;
      }
      const materialized = new Set();
      for (const i of body) {
        if (drop.has(i)) continue;
        const multi = stmts[i].targets.length > 1;
        stmts[i].targets.forEach((target, slot) => {
          if (!target.reg) return;
          const key = keyOf(i, slot);
          const live = block.liveOutRegs.has(target.reg) && lastWrite(target.reg) === i;
          if (multi || live || pinned.has(key) || (counts.get(key) || 0) !== 1) {
            materialized.add(key);
          }
        });
      }
      return { drop, counts, host, materialized };
    };

    const hazards = (decision) => {
      const { drop, host, materialized } = decision;
      const positionOf = (start) => {
        let key = start;
        for (let guard = 0; guard < 512; guard += 1) {
          const at = host.get(key);
          if (at === undefined || at >= stmts.length || drop.has(at)) return stmts.length;
          const target = stmts[at].targets[0];
          if (stmts[at].targets.length !== 1 || !target || !target.reg) return at;
          const next = keyOf(at, 0);
          if (materialized.has(next)) return at;
          key = next;
        }
        return stmts.length;
      };
      const pinned = new Set();
      for (const i of body) {
        if (drop.has(i) || stmts[i].targets.length !== 1) continue;
        const key = keyOf(i, 0);
        if (materialized.has(key) || !stmts[i].targets[0].reg) continue;
        const at = positionOf(key);
        for (const reg of liveOf(i)) {
          for (const write of writes.get(reg) || []) {
            if (write > i && write < at && !drop.has(write) && !control.has(write)) pinned.add(key);
          }
        }
      }
      return pinned;
    };

    const build = (decision) => {
      const {
        drop, counts, materialized,
      } = decision;

      const mark = this.warnings.length;
      const out = [];
      const violations = [];
      let violation = null;

      const kinds = new Map();
      const kindOf = (i) => {
        if (kinds.has(i)) return kinds.get(i);
        const statement = stmts[i];
        let answer = 'read';
        if (statement.targets.some((target) => target.node !== null)) answer = 'store';
        else if (statement.exprs.some(isCalling)) answer = 'call';
        kinds.set(i, answer);
        return answer;
      };
      let seen = -1;
      let acted = -1;
      let stored = -1;
      const note = (i) => {
        const kind = kindOf(i);
        let crossed = stored;
        if (kind === 'store') crossed = seen;
        else if (kind === 'call') crossed = acted;
        if (i < crossed) {
          if (violation === null) violation = { small: i, large: crossed };
          violations.push({ small: i, large: crossed });
        }
        if (i > seen) seen = i;
        if (kind !== 'read' && i > acted) acted = i;
        if (kind === 'store' && i > stored) stored = i;
      };
      const render = (node) => {
        if (!node || typeof node !== 'object') return node;
        if (node.kind === LIVE) return A.name(this.varFor(ctx, nameOfEntry(node.reg)));
        if (node.kind === REF) {
          const key = keyOf(node.index, node.slot);
          if (materialized.has(key)) {
            return A.name(this.varFor(ctx, nameOfDef(node.index, node.slot)));
          }
          if (control.has(node.index) || drop.has(node.index)) {
            this.warn('dangling-value', { block: block.id, at: node.index });
            return A.nil();
          }
          const value = render(definition(block, node));
          if (stmts[node.index].ordered) note(node.index);

          return A.isMultiValue(value) ? A.paren(value) : value;
        }
        const rendered = this.renderVm(node, ctx, render);

        return node.truncated && A.isMultiValue(rendered) ? A.paren(rendered) : rendered;
      };

      const emitted = body.filter((i) => {
        if (drop.has(i)) return false;
        const statement = stmts[i];
        if (statement.targets.some((target) => !target.reg)) return true;
        if (statement.targets.some((target, slot) => materialized.has(keyOf(i, slot)))) return true;
        return statement.targets.every((target, slot) => (counts.get(keyOf(i, slot)) || 0) === 0);
      });
      for (const i of emitted) {
        out.push(...this.renderStatement(i, stmts[i], ctx, { render, note, block }));
      }
      const condition = term.kind === 'branch' ? render(term.condition) : null;
      const returns = retAt === null ? null : render(stmts[retAt].exprs[0]);
      return {
        out, condition, returns, violation, violations, warnings: this.warnings.splice(mark),
      };
    };
    let pinned = new Set();
    let built = null;

    const rounds = body.length + 16;
    for (let attempt = 0; attempt < rounds; attempt += 1) {
      const decision = plan(pinned);
      const forced = hazards(decision);
      let grew = false;
      for (const key of forced) if (!pinned.has(key)) { pinned.add(key); grew = true; }
      if (grew) continue;
      built = build(decision);
      if (!built.violation) break;
      const inlinable = (i) => !decision.drop.has(i)
        && !decision.materialized.has(keyOf(i, 0));
      const pin = (i) => {
        for (let slot = 0; slot < stmts[i].targets.length; slot += 1) pinned.add(keyOf(i, slot));
      };
      let progress = false;
      for (const { small, large } of built.violations) {
        if (inlinable(small)) { pin(small); progress = true; } else if (inlinable(large)) {
          pin(large); progress = true;
        }
      }

      if (!progress) break;
    }
    if (!built) built = build(plan(pinned));

    if (built.violation) {
      const { small, large } = built.violation;
      this.warn('evaluation-order', { block: block.id, small, large });
    }
    this.warnings.push(...built.warnings);

    emitter.statements = built.out;
    emitter.condition = () => built.condition || A.nil();
    emitter.returns = () => {
      const value = built.returns;
      if (!value) return A.returnStatement([]);
      const list = resultList(value);
      if (list) return A.returnStatement(list);
      return A.returnStatement([A.call(A.name('unpack'), [value])]);
    };
  }

  renderStatement(index, statement, ctx, aux) {
    const vm = this.vm;
    const { render, note, block } = aux;
    const only = statement.targets.length === 1 ? statement.targets[0] : null;
    if (only && only.node && this.isUpvalueTable(peel(block, only.node.base))) {
      const cell = this.cellFor(ctx, ctx.tokenOf(only.node.index));
      if (cell) {
        const value = render(statement.exprs[0]);
        if (statement.ordered) note(index);
        return [A.assignment([A.name(cell)], [value])];
      }
    }
    const targets = statement.targets.map((target, slot) => (target.reg
      ? A.name(this.varFor(ctx, ctx.webs.find(defKey(block, index, slot))))
      : render(target.node)));
    const exprs = statement.exprs.map(render);

    if (targets.length === 1 && exprs.length === 1) exprs[0] = A.unparen(exprs[0]);
    if (statement.ordered) note(index);

    if (!targets.length) return exprs.length ? [A.callStatement(exprs[0])] : [];

    return [A.assignment(targets, exprs)];
  }

  isNeeded(block, statement, index, counts, pinned, lastWrite) {
    if (statement.ordered) return true;
    return statement.targets.some((target, slot) => {
      if (!target.reg) return true;
      if (pinned.has(`${index}.${slot}`)) return true;
      if (block.liveOutRegs.has(target.reg) && lastWrite(target.reg) === index) return true;
      return (counts.get(`${index}.${slot}`) || 0) > 0;
    });
  }

  labelFor(block, ctx) {
    if (!block) return [];
    const id = block.id;
    if (!ctx.structured.labels.has(id) || ctx.labelled.has(id)) return [];
    ctx.labelled.add(id);
    return [{ kind: Kind.Label, name: `L${id}` }];
  }

  emitRegion(region, ctx) {
    const out = [];
    if (!region || !region.items) return out;
    for (const item of region.items) {
      if (item.kind === 'block') {
        out.push(...this.labelFor(item.block, ctx));
        out.push(...this.prepareBlock(item.block, ctx).statements);
      } else if (item.kind === 'return') {
        out.push(this.prepareBlock(item.block, ctx).returns());
      } else if (item.kind === 'raw') {
        this.warn('unknown-exit', { block: item.block.id });
        out.push(A.returnStatement([]));
      } else if (item.kind === 'if') {
        const emitter = this.prepareBlock(item.block, ctx);
        out.push(A.ifStatement(
          negated(emitter.condition(), item.negate),
          A.block(this.emitRegion(item.then, ctx)),
          [],
          item.else ? A.block(this.emitRegion(item.else, ctx)) : null,
        ));
      } else if (item.kind === 'while') {
        out.push(...this.labelFor(item.loop && item.loop.header, ctx));
        out.push(...this.emitWhile(item, ctx));
      } else if (item.kind === 'repeat') {
        out.push(...this.labelFor(item.loop && item.loop.header, ctx));
        const emitter = this.prepareBlock(item.latch, ctx);
        const body = [...this.emitRegion(item.body, ctx), ...emitter.statements];
        out.push(A.repeatStatement(A.block(dropTailContinue(body)), negated(emitter.condition(), item.negate)));
      } else if (item.kind === 'loop') {
        out.push(...this.labelFor(item.loop && item.loop.header, ctx));
        out.push(A.whileStatement(
          A.boolean(true),
          A.block(dropTailContinue(this.emitRegion(item.body, ctx))),
        ));
      } else if (item.kind === 'break') {
        out.push(A.breakStatement());
      } else if (item.kind === 'continue') {
        out.push({ kind: Kind.Continue });
      } else if (item.kind === 'goto') {
        out.push({ kind: Kind.Goto, label: `L${item.target}` });
      } else if (item.kind === 'labelled') {
        ctx.labelled.add(item.id);
        out.push({ kind: Kind.Label, name: `L${item.id}` });
        out.push(...this.emitRegion(item.region, ctx));
      } else if (item.kind === 'seq') {
        out.push(...this.emitRegion(item, ctx));
      } else {
        this.warn('unhandled-region', { kind: item.kind });
      }
    }
    return out;
  }

  emitWhile(item, ctx) {
    const emitter = this.prepareBlock(item.header, ctx);
    const test = negated(emitter.condition(), item.negate);
    const body = this.emitRegion(item.body, ctx);
    const out = [];
    if (emitter.statements.length === 0) {
      out.push(A.whileStatement(test, A.block(dropTailContinue(body))));
    } else {
      out.push(A.whileStatement(A.boolean(true), A.block(dropTailContinue([
        ...emitter.statements,
        A.ifStatement(negated(test, true), A.block([A.breakStatement()]), [], null),
        ...body,
      ]))));
    }
    if (item.exitReturn) out.push(emitter.returns());
    return out;
  }

  liftFunction(fn, upvalues, depth) {
    if (depth > 200 || this.active.has(fn)) {
      this.warn('recursive-closure', { id: fn.id });
      return A.func([], A.block([]), false);
    }
    this.active.add(fn);
    const shape = analyzeArgs(this.vm, fn);
    const info = analyzeUpvalues(this.vm, fn);
    const structured = structureFunction(fn);
    for (const warning of structured.warnings) this.warn(warning.kind, { ...warning, fn: fn.id });

    const params = [];
    for (let i = 1; i <= shape.arity; i += 1) params.push(this.fresh('a'));
    const inLoop = new Set();
    for (const loop of structured.loops.values()) {
      for (const member of loop.members) inLoop.add(member.id);
    }
    const ctx = {
      fn,
      depth,
      params,
      structured,
      inLoop,
      labelled: new Set(),
      webs: buildWebs(fn),
      regVars: new Map(),
      cells: new Map(),
      cellToken: new Map(),
      used: new Set(),
      emitters: new Map(),
      block: fn.entry,
      tokenFrom: info.tokenFromExpression,
      tokenOf: null,
    };
    ctx.tokenOf = (node) => ctx.tokenFrom(
      ctx.block,
      node,
      ctx.block.upvalueEntry,
      ctx.block.upvalueTokens,
    );
    upvalues.forEach((name, i) => {
      if (name) ctx.cells.set(`param:${i + 1}`, name);
    });

    for (const block of fn.blocks) this.prepareBlock(block, ctx);
    const hoisted = this.declareCells(ctx, fn);
    const body = this.emitRegion(structured.region, ctx);
    const mentioned = new Set();
    walk(A.block(body), {
      enter(node) {
        if (node.kind === Kind.Name) mentioned.add(node.name);
        return undefined;
      },
    });
    const declared = [...ctx.regVars.values()].filter((name) => mentioned.has(name));
    const cells = hoisted.filter((name) => mentioned.has(name));
    if (declared.length || cells.length) {
      body.unshift(A.localDecl([...declared, ...cells], []));
    }
    this.active.delete(fn);
    return A.func(params, A.block(body), !!fn.vararg || shape.usesTable);
  }

  declareCells(ctx, fn) {
    const hoisted = [];
    const byId = new Map(fn.blocks.map((block) => [String(block.id), block]));
    for (const [name, token] of ctx.cellToken) {
      if (!ctx.used.has(name)) continue;
      const owner = byId.get(token.split(':')[1]);
      const emitter = owner ? ctx.emitters.get(owner) : null;
      if (owner && emitter && ctx.inLoop.has(owner.id)) {
        emitter.statements.unshift(A.localDecl([name], []));
      } else {
        hoisted.push(name);
      }
    }
    return hoisted;
  }

  lift() {
    const fn = this.byId.get(this.vm.entry.blockId);
    if (!fn) {
      this.warn('missing-entry', { id: this.vm.entry.blockId });
      return {
        body: A.block([]), params: [], isVararg: false, warnings: this.warnings, counter: 0,
      };
    }
    const lifted = this.liftFunction(fn, [], 0);
    return {
      body: unrepack(lifted.body),
      params: lifted.params,
      isVararg: lifted.isVararg,
      warnings: this.warnings,
      counter: this.counter,
    };
  }
}

function liftVm(vm, cfg, options = {}) {
  return new Lifter(vm, cfg, options).lift();
}

module.exports = { resultList, liftVm };
