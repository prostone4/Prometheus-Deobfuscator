'use strict';

const { Kind } = require('../lua/ast');
const { walk } = require('../lua/walk');

function declaredIn(root) {
  const declared = new Set();
  walk(root, {
    enter: (node) => {
      for (const binding of node.bindings || []) if (binding) declared.add(binding);
      if (node.binding && (node.kind === Kind.LocalFunction || node.kind === Kind.NumericFor)) {
        declared.add(node.binding);
      }
      return undefined;
    },
  });
  return declared;
}

function asFunction(node) {
  let value = node;
  while (value && value.kind === Kind.Paren) value = value.expression;
  return value && value.kind === Kind.Function ? value : null;
}

class Writes {
  constructor(chunk, writesIn, readsIn) {
    this.writesIn = writesIn;
    this.readsIn = readsIn;
    this.carriers = new Map();
    this.direct = new Map();
    this.mentions = new Map();
    this.resolved = new Map();
    this.reachedReads = new Map();
    this.collect(chunk);
  }

  collect(chunk) {
    const carry = (binding, fn) => {
      if (!binding || !fn) return;
      if (!this.carriers.has(binding)) this.carriers.set(binding, new Set());
      this.carriers.get(binding).add(fn);
    };
    walk(chunk, {
      enter: (node) => {
        if (node.kind === Kind.LocalFunction) carry(node.binding, node.body);
        else if (node.kind === Kind.FunctionDeclaration) {
          if (node.target && node.target.kind === Kind.Name) carry(node.target.binding, node.body);
        } else if (node.kind === Kind.LocalDeclaration || node.kind === Kind.Assignment) {
          const slots = node.kind === Kind.LocalDeclaration ? (node.bindings || []) : null;
          (node.expressions || []).forEach((expression, index) => {
            const fn = asFunction(expression);
            if (!fn) return;
            if (slots) { carry(slots[index], fn); return; }
            const target = (node.targets || [])[index];
            if (target && target.kind === Kind.Name) carry(target.binding, fn);
          });
        }
        if (node.kind === Kind.Function) this.summarise(node);
        return undefined;
      },
    });
  }

  summarise(fn) {
    const own = declaredIn(fn);
    const keep = (bindings) => {
      const out = new Set();
      for (const binding of bindings) if (!own.has(binding)) out.add(binding);
      return out;
    };
    this.direct.set(fn, keep(this.writesIn(fn.body, true)));
    this.mentions.set(fn, keep(this.readsIn(fn.body)));
  }

  close() {
    if (this.closed) return;
    this.closed = true;
    for (const [fn, direct] of this.direct) this.resolved.set(fn, new Set(direct));
    for (const [fn, mentioned] of this.mentions) {
      this.reachedReads.set(fn, new Set(mentioned));
    }
    for (let growing = true; growing;) {
      growing = false;
      for (const [fn, mentioned] of this.mentions) {
        const written = this.resolved.get(fn);
        const read = this.reachedReads.get(fn);
        for (const binding of mentioned) {
          for (const other of this.carriers.get(binding) || []) {
            for (const one of this.resolved.get(other) || []) {
              if (written.has(one)) continue;
              written.add(one);
              growing = true;
            }
            for (const one of this.reachedReads.get(other) || []) {
              if (read.has(one)) continue;
              read.add(one);
              growing = true;
            }
          }
        }
      }
    }
  }

  readsOf(fn) {
    this.close();
    const read = this.reachedReads.get(fn);
    if (!read) return new Set();
    const written = this.resolved.get(fn) || new Set();
    const out = new Set();
    for (const binding of read) if (!written.has(binding)) out.add(binding);
    return out;
  }

  allReadsOf(fn) {
    this.close();
    return this.reachedReads.get(fn) || new Set();
  }

  carriersOf(binding) {
    return this.carriers.get(binding) || new Set();
  }

  writesOf(fn) {
    this.close();
    return this.resolved.get(fn) || new Set();
  }

  of(statement) {
    const total = new Set(this.writesIn(statement, false));
    for (const binding of this.readsIn(statement)) {
      for (const fn of this.carriers.get(binding) || []) {
        for (const written of this.writesOf(fn)) total.add(written);
      }
    }
    return total;
  }
}

module.exports = { Writes, declaredIn };
