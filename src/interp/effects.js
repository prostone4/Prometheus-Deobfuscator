'use strict';

let clock = 0;
const witnesses = [];
const META = { meta: true };

function fresh() {
  clock += 1;
  return clock;
}

function touch(stamp, owner, key) {
  for (let i = 0; i < witnesses.length; i += 1) {
    const witness = witnesses[i];
    if (witness.writes) witness.writes.add(owner);
    if (stamp <= witness.since) {
      witness.escaped = true;
      if (witness.older && witness.last !== owner) {
        witness.last = owner;
        witness.older.add(owner);
      }
    }
    if (witness.slots && key !== undefined) {
      let slots = witness.slots.get(owner);
      if (!slots) {
        slots = new Map();
        witness.slots.set(owner, slots);
      }
      if (!slots.has(key)) {
        slots.set(key, key === META ? owner.metatable : owner.map.get(key));
      }
    }
    if (!witness.saved || witness.saved.has(owner)) continue;
    if (owner && owner.map) witness.tables.add(owner);
    else if (owner) witness.saved.set(owner, owner.value);
  }
}

function undo(entry) {
  for (const [owner, value] of entry.saved) owner.value = value;
  for (const [owner, slots] of entry.slots) {
    for (const [key, value] of slots) {
      if (key === META) owner.metatable = value;
      else if (value === undefined) owner.map.delete(key);
      else owner.map.set(key, value);
    }
  }
  entry.saved.clear();
  entry.slots.clear();
}

function commit(entry) {
  for (const [owner, value] of entry.saved) owner.value = value;
  entry.saved.clear();
  entry.slots.clear();
}

function attempt(body) {
  const entry = {
    since: clock,
    escaped: false,
    value: undefined,
    saved: new Map(),
    tables: new Set(),
    slots: new Map(),
  };
  witnesses.push(entry);
  try {
    entry.value = body();
  } catch (error) {
    witnesses.pop();
    undo(entry);
    throw error;
  }
  witnesses.pop();
  return entry;
}

function witness(body) {
  const entry = {
    since: clock, escaped: false, older: new Set(), last: null,
  };
  witnesses.push(entry);
  try {
    return { value: body(), escaped: entry.escaped, older: entry.older };
  } finally {
    witnesses.pop();
  }
}

function record(body) {
  const entry = { since: -1, escaped: false, writes: new Set() };
  witnesses.push(entry);
  try {
    return { value: body(), writes: entry.writes };
  } finally {
    witnesses.pop();
  }
}

module.exports = {
  META, fresh, touch, attempt, undo, commit, record, witness,
};
