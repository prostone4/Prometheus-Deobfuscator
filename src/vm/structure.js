'use strict';

const { dominators, dominates } = require('./dominators');

const EXIT = { id: 'EXIT' };

function fallsOut(block, members) {
  const term = block.terminator;
  if (term.kind === 'return' || term.kind === 'unknown') return true;
  if (term.kind === 'branch' && term.whenFalse === null) return true;
  return block.successors.filter((next) => members.has(next.id)).length === 0;
}

function adjacency(fn) {
  const succ = new Map([[EXIT, []]]);
  const pred = new Map([[EXIT, []]]);
  for (const block of fn.blocks) {
    succ.set(block, []);
    if (!pred.has(block)) pred.set(block, []);
  }
  const link = (from, to) => {
    succ.get(from).push(to);
    pred.get(to).push(from);
  };
  for (const block of fn.blocks) {
    for (const next of block.successors) {
      if (!fn.members.has(next.id)) continue;
      link(block, next);
    }
    if (fallsOut(block, fn.members)) link(block, EXIT);
  }
  return { succ, pred };
}

function findLoops(fn, idom, succ) {
  const loops = new Map();
  for (const block of fn.blocks) {
    for (const next of succ.get(block)) {
      if (next === EXIT) continue;
      if (!dominates(idom, next, block)) continue;
      let loop = loops.get(next);
      if (!loop) {
        loop = { header: next, latches: [], members: new Set([next]), follow: null, exits: [] };
        loops.set(next, loop);
      }
      loop.latches.push(block);
    }
  }
  for (const loop of loops.values()) {
    const stack = [...loop.latches];
    for (const latch of loop.latches) loop.members.add(latch);
    while (stack.length) {
      const block = stack.pop();
      if (block === loop.header) continue;
      for (const previous of block.predecessors) {
        if (!fn.members.has(previous.id)) continue;
        if (loop.members.has(previous)) continue;
        loop.members.add(previous);
        stack.push(previous);
      }
    }
    const candidates = new Set();
    for (const member of loop.members) {
      for (const next of succ.get(member)) {
        if (next === EXIT || loop.members.has(next)) continue;
        candidates.add(next);
        loop.exits.push({ from: member, to: next });
      }
    }
    if (candidates.size === 1) [loop.follow] = [...candidates];
    else loop.candidates = [...candidates];
  }
  return loops;
}

function structureFunction(fn) {
  const { succ, pred } = adjacency(fn);
  const forward = dominators(fn.entry, (n) => succ.get(n) || [], (n) => pred.get(n) || []);
  const backward = dominators(EXIT, (n) => pred.get(n) || [], (n) => succ.get(n) || []);
  const loops = findLoops(fn, forward.idom, succ);
  const rpo = forward.index;
  const warnings = [];
  const labels = new Set();
  const placed = new Set();

  for (const loop of loops.values()) {
    if (loop.follow || !loop.candidates || !loop.candidates.length) continue;
    const ranked = [...loop.candidates].sort((a, b) => (rpo.get(a) || 0) - (rpo.get(b) || 0));
    const after = ranked.find((c) => dominates(backward.idom, c, loop.header));
    const left = after || ranked.find((c) => (succ.get(loop.header) || []).includes(c));
    loop.follow = left || ranked[0];
    if (!left) {
      warnings.push({
        kind: 'multiple-loop-exits',
        header: loop.header.id,
        exits: ranked.map((c) => c.id),
      });
    }
  }

  const byId = new Map(fn.blocks.map((block) => [block.id, block]));
  const blockOf = (id) => {
    const found = byId.get(id);
    return found && fn.members.has(id) ? found : null;
  };

  const insideLoop = (loop, block) => {
    if (block === loop.follow || block === EXIT) return false;
    if (loop.members.has(block)) return true;
    if (!dominates(forward.idom, loop.header, block)) return false;
    return !loop.follow || !dominates(forward.idom, loop.follow, block);
  };

  const keywordFor = (target, ctx) => {
    const depth = ctx.loops.length - 1;
    for (let i = depth; i >= 0; i -= 1) {
      const loop = ctx.loops[i];
      if (target === loop.header) return i === depth ? { kind: 'continue', loop } : null;
      if (target === loop.follow) return i === depth ? { kind: 'break', loop } : null;
    }
    return null;
  };

  const jumpTo = (target, ctx) => {
    const keyword = keywordFor(target, ctx);
    if (keyword) return keyword;
    labels.add(target.id);
    return { kind: 'goto', target: target.id };
  };

  const emit = (start, follow, ctx, entering) => {
    const items = [];
    let current = start;
    for (let guard = 0; current && guard < 100000; guard += 1) {
      if (current === follow) break;

      if (!(entering && guard === 0)) {
        const keyword = keywordFor(current, ctx);
        if (keyword) {
          items.push(keyword);
          break;
        }
      }
      if (placed.has(current)) {
        items.push(jumpTo(current, ctx));
        break;
      }
      const loop = loops.get(current);
      if (loop && !ctx.loops.includes(loop)) {
        items.push(emitLoop(loop, ctx));
        current = loop.follow;
        continue;
      }
      placed.add(current);
      items.push({ kind: 'block', block: current });
      const term = current.terminator;
      if (term.kind === 'return' || term.kind === 'unknown') {
        items.push({ kind: term.kind === 'return' ? 'return' : 'raw', block: current });
        break;
      }
      if (term.kind === 'goto') {
        const target = blockOf(term.target);
        if (!target) {
          warnings.push({ kind: 'missing-target', from: current.id, to: term.target });
          break;
        }
        if (target === follow) break;
        const loopAt = loops.get(target);
        const jump = jumpTo(target, ctx);
        if (jump.kind === 'goto' && !placed.has(target)
          && (!loopAt || !ctx.loops.includes(loopAt))) {
          labels.delete(target.id);
          current = target;
          continue;
        }
        items.push(jump);
        break;
      }
      if (term.kind === 'branch') {
        const join = backward.idom.get(current);
        let limit = join && join !== EXIT && join !== current ? join : null;

        const inner = ctx.loops[ctx.loops.length - 1];
        if (limit && inner && !insideLoop(inner, limit)) limit = null;
        items.push(emitBranch(current, term, limit, ctx));
        if (!limit || limit === follow || placed.has(limit)) break;
        current = limit;
        continue;
      }
      break;
    }
    return { kind: 'seq', items };
  };
  const isEmpty = (region) => !region || !region.items || region.items.length === 0;

  const emitBranch = (block, term, limit, ctx) => {
    const whenTrue = blockOf(term.whenTrue);
    const whenFalse = term.whenFalse === null ? null : blockOf(term.whenFalse);
    const thenRegion = whenTrue ? emit(whenTrue, limit, ctx) : { kind: 'seq', items: [] };
    const elseRegion = whenFalse ? emit(whenFalse, limit, ctx)
      : { kind: 'seq', items: [{ kind: 'return', block }] };
    if (isEmpty(thenRegion) && !isEmpty(elseRegion)) {
      return {
        kind: 'if', block, condition: term.condition, negate: true, then: elseRegion, else: null,
      };
    }
    return {
      kind: 'if',
      block,
      condition: term.condition,
      negate: false,
      then: thenRegion,
      else: isEmpty(elseRegion) ? null : elseRegion,
    };
  };

  const emitLoop = (loop, ctx) => {
    const inner = { ...ctx, loops: [...ctx.loops, loop] };
    const header = loop.header;
    const term = header.terminator;

    if (term.kind === 'branch') {
      const whenTrue = blockOf(term.whenTrue);
      const whenFalse = term.whenFalse === null ? null : blockOf(term.whenFalse);
      const trueInside = whenTrue && loop.members.has(whenTrue);
      const falseInside = whenFalse && loop.members.has(whenFalse);
      const leaves = (node) => node === loop.follow || (node === null && loop.follow === null);
      if (trueInside && !falseInside && leaves(whenFalse)) {
        placed.add(header);
        return {
          kind: 'while',
          loop,
          header,
          condition: term.condition,
          negate: false,
          body: emit(whenTrue, header, inner, true),
          exitReturn: whenFalse === null,
        };
      }
      if (falseInside && !trueInside && leaves(whenTrue)) {
        placed.add(header);
        return {
          kind: 'while',
          loop,
          header,
          condition: term.condition,
          negate: true,
          body: emit(whenFalse, header, inner, true),
          exitReturn: false,
        };
      }
    }

    if (loop.latches.length === 1 && loop.latches[0] !== header) {
      const latch = loop.latches[0];
      const latchTerm = latch.terminator;
      if (latchTerm.kind === 'branch') {
        const whenTrue = blockOf(latchTerm.whenTrue);
        const whenFalse = latchTerm.whenFalse === null ? null : blockOf(latchTerm.whenFalse);
        const exitsTrue = whenFalse === header && whenTrue === loop.follow;
        const exitsFalse = whenTrue === header && whenFalse === loop.follow;
        if (exitsTrue || exitsFalse) {
          placed.add(latch);
          const body = emit(header, latch, inner, true);
          return {
            kind: 'repeat',
            loop,
            latch,
            condition: latchTerm.condition,
            negate: exitsFalse,
            body,
          };
        }
      }
    }

    warnings.push({ kind: 'unstructured-loop', header: header.id });
    return { kind: 'loop', loop, header, body: emit(header, null, inner, true) };
  };
  const region = emit(fn.entry, null, { loops: [] });

  const positionOf = new Map(fn.blocks.map((block, at) => [block, at]));
  const tails = [];
  for (let guard = 0; guard < 10000; guard += 1) {
    let pending = null;
    let earliest = Infinity;
    for (const id of labels) {
      const block = byId.get(id);
      if (!block || placed.has(block)) continue;
      const at = positionOf.has(block) ? positionOf.get(block) : Infinity;
      if (at < earliest) { earliest = at; pending = block; }
    }
    if (!pending) break;
    tails.push({ kind: 'labelled', id: pending.id, region: emit(pending, null, { loops: [] }) });
  }
  if (tails.length) region.items.push(...tails);

  const unplaced = fn.blocks.filter((block) => !placed.has(block));
  for (const block of unplaced) warnings.push({ kind: 'unplaced-block', block: block.id });

  return {
    fn, region, labels, loops, warnings, unplaced, dom: forward, postDom: backward,
  };
}

module.exports = { structureFunction };
