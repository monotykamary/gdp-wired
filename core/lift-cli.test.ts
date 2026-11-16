import {expect, test} from 'bun:test'
import {parseLiftArguments} from './lift-cli.ts'
test('lift accepts exactly a capsule and a data source with explicit controls', () => {
  expect(parseLiftArguments(['cap', 'source.json', '--out', 'new-dir', '--emit-only', '--json', '--timeout-ms', '10'])).toEqual({capsule: 'cap', source: 'source.json', out: 'new-dir', emitOnly: true, json: true, timeoutMs: 10})
})
test('lift arguments reject ambiguity and invalid budgets without executing input', () => {
  for (const args of [[], ['cap'], ['cap', 'source', 'extra'], ['cap', 'source', '--unknown'], ['cap', 'source', '--out'], ['cap', 'source', '--json', '--json'], ['cap', 'source', '--sha256', 'bad'], ['cap', 'source', '--timeout-ms', 'NaN'], ['cap', 'source', '--timeout-ms', '0'], ['cap', 'source', '--timeout-ms', '7200001']]) expect(() => parseLiftArguments(args)).toThrow()
})
