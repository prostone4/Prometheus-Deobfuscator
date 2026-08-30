'use strict';

const scopes = require('../beautify/scopes');

function run(context) {
  context.resolve();
  const wrapped = scopes.fit(context.chunk, () => context.resolve());
  if (wrapped) {
    context.note(`narrowed ${wrapped} scope(s) to fit the local limit`, wrapped);
    context.bump('scope.narrowed', wrapped);
  }
}

module.exports = {
  name: '11-scope',
  run,
};
