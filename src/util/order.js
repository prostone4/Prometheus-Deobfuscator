'use strict';

const { Kind } = require('../lua/ast');
const { framed } = require('../lua/walk');

class Positions {
  constructor(root) {
    this.paths = new Map();
    this.labelled = new Set();
    framed(root, (node, frame) => {
      if (node.kind !== Kind.Block) {
        this.paths.set(node, frame);
        return;
      }
      if (node.statements.some((statement) => statement.kind === Kind.Label)) {
        this.labelled.add(node);
      }
    });
  }

  path(node) {
    return this.paths.get(node) || null;
  }

  precedes(statement, node) {
    const before = this.path(statement);
    const after = this.path(node);
    if (!before || !after) return false;
    let low = before;
    let high = after;
    while (low.depth > high.depth) low = low.up;
    while (high.depth > low.depth) high = high.up;
    if (low === high) return false;
    while (low.up !== high.up) {
      low = low.up;
      high = high.up;
    }
    if (low !== before || low.block !== high.block) return false;
    if (low.at >= high.at) return false;
    if (this.labelled.has(low.block) && this.jumpedInto(low.block, low.at, high.at)) return false;
    return true;
  }

  jumpedInto(block, from, to) {
    const statements = block.statements;
    for (let at = from + 1; at <= to && at < statements.length; at += 1) {
      if (statements[at].kind === Kind.Label) return true;
    }
    return false;
  }
}

module.exports = { Positions };
