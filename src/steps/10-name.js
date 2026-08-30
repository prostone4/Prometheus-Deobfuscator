'use strict';

const rename = require('./08-vars');
const names = require('../beautify/names');

function plan(chunk, hints, taken) {
  const globals = new Set(taken);
  const next = rename.namer(taken);
  const word = names.allocator(taken);
  const chosen = new Map();
  let described = 0;
  for (const [binding, category] of rename.categories(chunk)) {
    const hint = hints.get(binding);
    if (hint && !globals.has(hint)) {
      chosen.set(binding, word(hint));
      described += 1;
    } else chosen.set(binding, next(category));
  }
  return { chosen, described };
}

function run(context) {
  context.resolve();
  const hints = names.suggest(context.chunk);
  const taken = rename.reserved(context.chunk);
  const { chosen, described } = plan(context.chunk, hints, taken);
  if (!chosen.size) return;
  const renamed = rename.apply(context.chunk, chosen);
  context.resolve();
  context.note(`named ${described} local(s) from the code`, described);
  context.bump('name.described', described);
  context.bump('name.bindings', chosen.size);
  context.bump('name.mentions', renamed);
}

module.exports = {
  name: '10-name',
  run,
  plan,
};
