import {expect, test} from 'bun:test'
import {n, same} from '../../core/machine.ts'
import {proveLeanAggregate} from './index.ts'
import {exactAxioms} from './audit.ts'
import {checkAdmissionControls} from './admission-controls.ts'

const row = (axioms: string) => `'aggregate_claim' depends on axioms: [${axioms}]`
test('aggregate audit requires the exact theorem and only fully qualified standard axioms', () => {
  expect(exactAxioms(row('propext, Classical.choice, Quot.sound'))).toEqual(['propext', 'Classical.choice', 'Quot.sound'])
  expect(exactAxioms("'aggregate_claim' does not depend on any axioms")).toEqual([])
  for (const output of ['', row('sorryAx'), row('Lean.ofReduceBool'), row('choice'), row('Bogus.choice'),
    row('propext').replace('aggregate_claim', 'auxiliary'), `${row('propext')}\n${row('propext')}`,
    `Aggregate.lean:1:0: error: failed\n${row('propext')}`, `Aggregate.lean:1:0: warning: declaration uses 'sorry'\n${row('propext')}`])
    expect(() => exactAxioms(output)).toThrow()
})

test('aggregate admission refuses hooks, provenance, and invalid source scope', async () => {
  await checkAdmissionControls()
})

test('unsupported inputs do not yield a native verdict or Lean receipt', async () => {
  const result = await proveLeanAggregate({name: 'control', params: [], inputs: [], state: {}, step: {}, counts: {}},
    {name: 'true', holds: same(n(0), n(0))})
  expect(result).toMatchObject({kind: 'not-checked', reason: 'unsupported'})
  expect(result).not.toHaveProperty('checked')
  expect(result).not.toHaveProperty('receipt')
})
