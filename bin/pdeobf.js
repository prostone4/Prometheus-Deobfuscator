#!/usr/bin/env node
'use strict';

const fs = require('fs');
const path = require('path');
const { deobfuscate, NotPrometheusError } = require('../src/index');

const USAGE = `usage: pdeobf <input.lua> [options]

  -o <file>   write output to file
  --force     skip prometheus detection
  -q          don't print notes/warnings
  -h          show this message
`;

const C = {
  reset:  '\x1b[0m',
  bold:   '\x1b[1m',
  gray:   '\x1b[90m',
  cyan:   '\x1b[36m',
  green:  '\x1b[32m',
  yellow: '\x1b[33m',
  red:    '\x1b[31m',
};

function parseArgs(argv) {
  const opts = {};
  const rest = [];
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    const next = () => {
      i++;
      if (i >= argv.length) throw new Error(`${arg}: missing value`);
      return argv[i];
    };
    if (arg === '-o') opts.out = next();
    else if (arg === '--force') opts.force = true;
    else if (arg === '-q') opts.quiet = true;
    else if (arg === '-h' || arg === '--help') opts.help = true;
    else if (arg.startsWith('-')) throw new Error(`unknown flag: ${arg}`);
    else rest.push(arg);
  }
  opts.input = rest[0];
  return opts;
}

function fmt(ms) {
  return ms < 1000 ? `${ms}ms` : `${(ms / 1000).toFixed(2)}s`;
}

function main(argv) {
  let opts;
  try {
    opts = parseArgs(argv);
  } catch (e) {
    process.stderr.write(`pdeobf: ${e.message}\n`);
    return 2;
  }

  if (opts.help || !opts.input) {
    process.stdout.write(USAGE);
    return opts.help ? 0 : 2;
  }

  const source = fs.readFileSync(opts.input, 'latin1');
  const tty = process.stderr.isTTY && !opts.quiet;

  let stepStart = null;
  let ticker = null;
  let curStep = null;

  function printCurrent(done) {
    const ms = Date.now() - stepStart;
    const mark = done
      ? `${C.green}✓${C.reset}`
      : `${C.yellow}…${C.reset}`;
    const time = `${C.gray}${fmt(ms)}${C.reset}`;
    const line = `  ${mark} ${C.cyan}${curStep}${C.reset}  ${time}`;
    process.stderr.write(`\r${line}   `);
    if (done) process.stderr.write('\n');
  }

  function onProgress(event, data) {
    if (!tty) return;
    if (event === 'start') {
      curStep = data.step;
      stepStart = Date.now();
      printCurrent(false);
      ticker = setInterval(() => printCurrent(false), 80);
    } else if (event === 'end') {
      clearInterval(ticker);
      ticker = null;
      printCurrent(true);
      stepStart = null;
    }
  }

  let result;
  try {
    result = deobfuscate(source, {
      name: path.basename(opts.input),
      detect: !opts.force,
      onProgress,
    });
  } catch (e) {
    if (ticker) clearInterval(ticker);
    if (!(e instanceof NotPrometheusError)) {
      process.stderr.write(`\npdeobf: ${e.message}\n`);
      return 1;
    }
    process.stderr.write(`\npdeobf: not prometheus\n`);
    return 3;
  }

  if (opts.out) {
    fs.writeFileSync(opts.out, result.code, 'latin1');
    if (tty) process.stderr.write(`\n${C.bold}done${C.reset} → ${C.cyan}${opts.out}${C.reset}\n`);
  } else {
    process.stdout.write(result.code);
  }

  return 0;
}

process.exitCode = main(process.argv.slice(2));
