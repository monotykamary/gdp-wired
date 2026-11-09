import {expect, test} from 'bun:test'
import {linkFocusAudits} from './link-lane-b-focus-audits.ts'
const row = {name: 'pair', side: 'before', tag: 'p1', checked: true, units: 12, wallMs: 20, results: [{pass: 1, outcome: 'proof', units: 12}]}
const projection = () => ({range: [{...row}], early: [], followup: []})
const receipt = (changes = {}) => ({...row, ...changes, conditional: true, familyVerified: true, originalHarness: true})
const source = (record = receipt()) => ({path: 'audit/audit.log', exitCode: 0, text: 'INPUT=receipts/pair-before.json.gz\n' + JSON.stringify(record) + '\n'})
test('links the exact projected arm and retains conditional, nongate scope', () => {
  const linked = linkFocusAudits(projection(), [source()])
  expect(linked.independentAudit).toEqual({outcomes: 1, checked: 1, unknown: 0})
  expect(linked.range[0]!.audit.conditional).toBe(true)
  expect(linked.gateGreen).toBe(false)
  expect(linked.range[0]!.audit.logSha256).toMatch(/^[a-f0-9]{64}$/)
})
test('rejects omitted, repeated, extra, unbound and failed audits', () => {
  expect(() => linkFocusAudits(projection(), [])).toThrow()
  expect(() => linkFocusAudits(projection(), [source(), source()])).toThrow()
  expect(() => linkFocusAudits(projection(), [{...source(), text: source().text.replace('pair-before', 'other')}])).toThrow()
  expect(() => linkFocusAudits(projection(), [{...source(), text: JSON.stringify(receipt())}])).toThrow()
  expect(() => linkFocusAudits(projection(), [{...source(), exitCode: 1}])).toThrow()
})
test('rejects changed cost, outcome, target, pass sequence and family binding', () => {
  for (const changes of [{units: 13}, {wallMs: 21}, {checked: false}, {tag: 'other'}, {results: []}]) {
    expect(() => linkFocusAudits(projection(), [source(receipt(changes))])).toThrow()
  }
  for (const field of ['familyVerified', 'originalHarness']) {
    const record = {...receipt(), [field]: false}
    expect(() => linkFocusAudits(projection(), [source(record)])).toThrow()
  }
})
test('counts reconciled unknowns separately and does not claim a proof for them', () => {
  const p = projection(); p.range[0]!.checked = false
  const linked = linkFocusAudits(p, [source(receipt({checked: false}))])
  expect(linked.independentAudit).toEqual({outcomes: 1, checked: 0, unknown: 1})
  expect(linked.range[0]!.audit.checked).toBe(false)
})
