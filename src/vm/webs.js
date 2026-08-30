'use strict';

class Webs {
  constructor() {
    this.parent = new Map();
  }

  find(key) {
    let root = key;
    while (this.parent.has(root) && this.parent.get(root) !== root) {
      root = this.parent.get(root);
    }
    let node = key;
    while (this.parent.has(node) && this.parent.get(node) !== node) {
      const next = this.parent.get(node);
      this.parent.set(node, root);
      node = next;
    }
    if (!this.parent.has(key)) this.parent.set(key, root);
    return root;
  }

  union(a, b) {
    const ra = this.find(a);
    const rb = this.find(b);
    if (ra !== rb) this.parent.set(rb, ra);
  }
}

const entryKey = (block, reg) => `E${block.id}|${reg}`;

const defKey = (block, index, slot) => `D${block.id}|${index}.${slot}`;

function liveness(fn) {
  const liveIn = new Map();
  const liveOut = new Map();
  for (const block of fn.blocks) {
    liveIn.set(block, new Set(block.liveIn));
    liveOut.set(block, new Set());
  }
  const order = [...fn.blocks].reverse();
  for (let round = 0; round < 10000; round += 1) {
    let changed = false;
    for (const block of order) {
      const out = liveOut.get(block);
      const into = liveIn.get(block);
      for (const next of block.successors) {
        if (!fn.members.has(next.id)) continue;
        for (const reg of liveIn.get(next) || []) {
          if (out.has(reg)) continue;
          out.add(reg);
          changed = true;
        }
      }
      for (const reg of out) {
        if (block.written.has(reg) || into.has(reg)) continue;
        into.add(reg);
        changed = true;
      }
    }
    if (!changed) break;
  }
  return { liveIn, liveOut };
}

function exitKey(block, reg) {
  const stmts = block.statements;
  for (let i = stmts.length - 1; i >= 0; i -= 1) {
    const targets = stmts[i].targets;
    for (let slot = targets.length - 1; slot >= 0; slot -= 1) {
      if (targets[slot].reg === reg) return defKey(block, i, slot);
    }
  }
  return entryKey(block, reg);
}

function buildWebs(fn) {
  const webs = new Webs();
  const { liveIn } = liveness(fn);
  for (const block of fn.blocks) {
    for (const reg of liveIn.get(block) || []) {
      const key = entryKey(block, reg);
      webs.find(key);
      for (const pred of block.predecessors) {
        if (!fn.members.has(pred.id)) continue;
        webs.union(key, exitKey(pred, reg));
      }
    }
  }
  return webs;
}

module.exports = { buildWebs, entryKey, defKey, liveness };
