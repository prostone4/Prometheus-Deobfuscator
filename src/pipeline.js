'use strict';

const { resolve } = require('./lua/scope');
const { unparse } = require('./lua/unparse');
const { matchWrapper } = require('./steps/01-wrap');
const { detect } = require('./vm/detect');

class Context {
  constructor(chunk, options = {}) {
    this.chunk = chunk;
    this.options = options;
    this.notes = [];
    this.stats = {};
    this.warnings = [];
    this.step = null;
    this.resolved = null;
  }

  note(message, count) {
    this.notes.push({ step: this.step, message, count });
  }

  warn(message) {
    this.warnings.push({ step: this.step, message });
  }

  bump(key, amount = 1) {
    this.stats[key] = (this.stats[key] || 0) + amount;
  }

  resolve() {
    this.resolved = resolve(this.chunk);
    return this.resolved;
  }

  reportProgress(event, data = {}) {
    if (typeof this.options.onProgress === 'function') {
      try {
        this.options.onProgress(event, { step: this.step, ...data, stats: this.stats });
      } catch (_) {}
    }
  }

  source() {
    return unparse(this.chunk, this.options.print);
  }
}

const STEPS = [
  require('./steps/01-wrap'),
  require('./steps/02-fold'),
  require('./steps/03-str'),
  require('./steps/04-lift'),
  require('./steps/05-if'),
  require('./steps/06-proxy'),
  require('./steps/07-opt'),
  require('./steps/08-vars'),
  require('./steps/09-fmt'),
  require('./steps/10-name'),
  require('./steps/11-scope'),
];

const SETTLE = ['03-str', '06-proxy', '07-opt'];
const FINAL = ['08-vars', '09-fmt', '10-name', '11-scope'];
const PASSES = 4;
const LAYERS = 8;

function runStep(context, step, options, pass, layer) {
  context.step = step.name;
  context.reportProgress('start', { step: step.name, pass, layer });
  const started = Date.now();
  try {
    step.run(context);
  } catch (error) {
    if (options.strict) throw error;
    context.warn(`step failed: ${error.message}`);
    if (options.verbose) console.error(error.stack);
  }
  context.bump(`time.${step.name}`, Date.now() - started);
  context.reportProgress('end', { step: step.name, pass, layer });
  if (options.trace) {
    const fs = require('fs');
    const path = require('path');
    fs.mkdirSync(options.trace, { recursive: true });
    const deep = layer > 1 ? `.layer${layer}` : '';
    const suffix = pass > 1 ? `.pass${pass}` : '';
    fs.writeFileSync(
      path.join(options.trace, `${step.name}${deep}${suffix}.lua`),
      context.source(),
      'latin1',
    );
  }
}

function settle(context, group, options, layer) {
  const enabling = new Set(['03-str', '06-proxy']);
  for (let pass = 2; pass <= PASSES; pass += 1) {
    const before = context.notes.length;
    let moved = false;
    for (const step of group) {
      const mark = context.notes.length;
      runStep(context, step, options, pass, layer);
      if (enabling.has(step.name) && context.notes.length > mark) moved = true;
    }
    if (context.notes.length === before || !moved) return;
  }
}

function stacked(context) {
  if (matchWrapper(context.chunk.body)) return true;
  context.resolve();
  try {
    return detect(context.chunk).instances.length > 0;
  } catch (_) {
    return false;
  }
}

function run(chunk, options = {}) {
  const context = new Context(chunk, options);
  const only = options.only ? new Set(options.only) : null;
  const skip = options.skip ? new Set(options.skip) : new Set();
  const wanted = STEPS.filter((step) => (!only || only.has(step.name)) && !skip.has(step.name));
  const early = wanted.filter((step) => !FINAL.includes(step.name));
  const last = wanted.filter((step) => FINAL.includes(step.name));
  const group = SETTLE.map((name) => early.find((step) => step.name === name)).filter(Boolean);
  const closes = group.length ? Math.max(...group.map((step) => early.indexOf(step))) : -1;

  for (let layer = 1; layer <= LAYERS && early.length; layer += 1) {
    const before = context.notes.length;
    for (let i = 0; i < early.length; i += 1) {
      runStep(context, early[i], options, 1, layer);
      if (i === closes) settle(context, group, options, layer);
    }
    if (context.notes.length === before) break;
    if (!stacked(context)) break;
    context.bump('layers.stacked');
  }

  for (const step of last) runStep(context, step, options, 1, 1);
  context.step = null;
  return context;
}
module.exports = { Context, STEPS, run };
