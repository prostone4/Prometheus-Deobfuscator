'use strict';

const { parse } = require('./lua/parser');
const { unparse } = require('./lua/unparse');
const { Context, STEPS, run } = require('./pipeline');
const { identify } = require('./detect/prometheus');

class NotPrometheusError extends Error {
  constructor(report) {
    super(`unsupported Prometheus payload: ${report.reasons.join('; ')}`);
    this.name = 'NotPrometheusError';
    this.report = report;
  }
}

function deobfuscate(source, options = {}) {
  const name = options.name || 'chunk';
  let chunk = null;
  let unparsable = null;
  try {
    chunk = parse(source, { name });
  } catch (error) {
    unparsable = error;
  }
  let report = null;
  if (options.detect !== false) {
    report = identify(source, chunk);
    if (!report.prometheus) throw new NotPrometheusError(report);
  }
  if (unparsable) throw unparsable;
  const context = run(chunk, options);
  return {
    code: context.source(),
    chunk,
    notes: context.notes,
    warnings: context.warnings,
    stats: context.stats,
    context,
    detected: report,
  };
}

module.exports = {
  deobfuscate,
  NotPrometheusError,
  identify,
  parse,
  unparse,
  run,
  Context,
  STEPS,
  ast: require('./lua/ast'),
  detect: require('./vm/detect').detect,
  liftVm: require('./vm/lift').liftVm,
};
