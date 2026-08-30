'use strict';

function reversePostorder(entry, succOf) {
  const visited = new Set([entry]);
  const post = [];
  const stack = [{ node: entry, successors: succOf(entry), index: 0 }];
  while (stack.length) {
    const frame = stack[stack.length - 1];
    if (frame.index < frame.successors.length) {
      const next = frame.successors[frame.index];
      frame.index += 1;
      if (visited.has(next)) continue;
      visited.add(next);
      stack.push({ node: next, successors: succOf(next), index: 0 });
      continue;
    }
    post.push(frame.node);
    stack.pop();
  }
  return post.reverse();
}

function dominators(entry, succOf, predOf) {
  const order = reversePostorder(entry, succOf);
  const index = new Map();
  order.forEach((node, i) => index.set(node, i));
  const idom = new Map([[entry, entry]]);

  const intersect = (a, b) => {
    let left = a;
    let right = b;
    while (left !== right) {
      while (index.get(left) > index.get(right)) left = idom.get(left);
      while (index.get(right) > index.get(left)) right = idom.get(right);
    }
    return left;
  };

  for (let round = 0; round < 10000; round += 1) {
    let changed = false;
    for (const node of order) {
      if (node === entry) continue;
      let candidate = null;
      for (const pred of predOf(node)) {
        if (!index.has(pred) || !idom.has(pred)) continue;
        candidate = candidate === null ? pred : intersect(pred, candidate);
      }
      if (candidate && idom.get(node) !== candidate) {
        idom.set(node, candidate);
        changed = true;
      }
    }
    if (!changed) break;
  }
  return { idom, order, index };
}

function dominates(idom, ancestor, node) {
  let current = node;
  for (let guard = 0; guard < 100000; guard += 1) {
    if (current === ancestor) return true;
    const next = idom.get(current);
    if (!next || next === current) return false;
    current = next;
  }
  return false;
}

module.exports = { reversePostorder, dominators, dominates };
