'use strict';

const purity = require('../util/purity');
const { removeDead } = require('../util/dead-code');
const idioms = require('../vm/idioms');
const simplify = require('./07-opt');
const copies = require('../beautify/copies');
const hoist = require('../beautify/hoist');
const tuples = require('../beautify/tuples');
const declare = require('../beautify/declare');
const services = require('../beautify/services');
const shapes = require('../beautify/shapes');
const jumps = require('../beautify/jumps');
const loops = require('../beautify/loops');
const callbacks = require('../beautify/callbacks');

const ROUNDS = 8;

const PASSES = [
  ['named', (chunk) => hoist.nameCalled(chunk)],
  ['tuples', (chunk) => tuples.nameResults(chunk)],
  ['services', (chunk) => services.gather(chunk)],
  ['copies', (chunk) => copies.propagate(chunk)],
  ['temporaries', (chunk) => copies.inlineTemps(chunk)],
  ['declarations', (chunk) => declare.sink(chunk)],
  ['filled', (chunk) => declare.fill(chunk)],
  ['pushed', (chunk) => declare.pushIn(chunk)],
  ['moved', (chunk) => declare.slide(chunk)],
  ['husks', (chunk) => declare.dropEmpty(chunk)],
  ['functions', (chunk) => declare.localForm(chunk)],
  ['recursions', (chunk) => declare.recursiveForm(chunk)],
  ['assigned', (chunk) => declare.assignedForm(chunk)],
  ['methods', (chunk) => declare.methodForm(chunk)],
  ['callbacks', (chunk) => callbacks.inlineClosures(chunk)],
  ['iterators', (chunk) => loops.foldIterators(chunk)],
  ['tests', (chunk) => loops.raiseTest(chunk)],
  ['jumps', (chunk) => jumps.clean(chunk)],
  ['tails', (chunk) => jumps.pull(chunk)],
  ['returns', (chunk) => shapes.dropReturns(chunk)],
  ['otherwise', (chunk) => shapes.dropElse(chunk)],
  ['guards', (chunk) => shapes.liftElse(chunk)],
  ['branches', (chunk) => shapes.collapseElseIf(chunk)],
  ['parens', (chunk) => shapes.dropParens(chunk)],
  ['blocks', (chunk) => shapes.flatten(chunk)],
];

function tidy(context, counters) {
  let changed = 0;
  changed += idioms.run(context, counters);
  context.resolve();
  changed += simplify.eliminate(context.chunk, new purity.Facts(context.chunk), counters);
  context.resolve();
  const unwanted = removeDead(context.chunk, new purity.Facts(context.chunk));
  counters.unwanted += unwanted;
  changed += unwanted;
  context.resolve();
  changed += simplify.mergeDecls(context.chunk, counters);
  context.resolve();
  return changed;
}

function run(context) {
  const counters = { eliminated: 0, merged: 0, idioms: 0, unwanted: 0 };
  for (const [name] of PASSES) counters[name] = 0;
  context.resolve();
  for (let round = 0; round < ROUNDS; round += 1) {
    let changed = 0;
    for (const [name, pass] of PASSES) {
      const moved = pass(context.chunk);
      if (!moved) continue;
      counters[name] += moved;
      changed += moved;
      context.resolve();
    }
    changed += tidy(context, counters);
    if (!changed) break;
  }
  const moves = PASSES.reduce((total, [name]) => total + counters[name], 0);
  if (moves) {
    context.note(
      `put back ${counters.copies + counters.temporaries} value(s),`
      + ` ${counters.declarations + counters.filled} declaration(s),`
      + ` ${counters.named + counters.functions + counters.assigned + counters.methods} function form(s)`,
      moves,
    );
  }
  for (const key of Object.keys(counters)) {
    if (counters[key]) context.bump(`beautify.${key}`, counters[key]);
  }
}

module.exports = { name: '09-fmt', run, PASSES };
