import {expect, test} from 'bun:test'
import {asked, answers, auditLiftLog, gate} from './axiom-audit.ts'
const source = '#print axioms lifted_source\n#print axioms lifted_family\n'
const good = "'lifted_source' depends on axioms: [propext, Classical.choice, Quot.sound]\n'lifted_family' does not depend on any axioms\n"
test('lift audit checks exact source and family names', () => {
  expect(asked(source)).toEqual(['lifted_source', 'lifted_family'])
  expect(answers(good)).toHaveLength(2)
  expect(auditLiftLog(good, [source], ['lifted_source', 'lifted_family'])).toHaveLength(2)
})
test('apostrophes in names and wrapped axiom lists remain exact', () => {
  const text = "'Scope'.source'' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n'family'' does not depend on any axioms\n"
  const names = ["Scope'.source'", "family'"]
  expect(answers(text).map(r => r.name)).toEqual(names)
  expect(auditLiftLog(text, [names.map(n => '#print axioms ' + n).join('\n')], names)).toHaveLength(2)
  expect(() => auditLiftLog(text + text, [], names)).toThrow('expected one')
  expect(answers("diagnostic: 'not_an_answer' does not depend on any axioms\n")).toEqual([])
})
test('another theorem or duplicated answer cannot cover the source theorem', () => {
  expect(() => auditLiftLog(good.replaceAll('lifted_source', 'another'), [source], ['lifted_source'])).toThrow('lifted_source')
  expect(() => auditLiftLog(good + good, [source], ['lifted_source'])).toThrow('expected one')
})
test('lift never accepts compiler axioms, custom axioms, sorry or errors', () => {
  for (const axiom of ['Lean.trustCompiler', 'Lean.ofReduceBool', 'unsafe_assumption']) expect(() => auditLiftLog(good.replace('propext', axiom), [source], ['lifted_source'])).toThrow()
  expect(() => auditLiftLog(good + "declaration uses 'sorry'", [source], ['lifted_source'])).toThrow()
  expect(() => auditLiftLog(good + 'error: failed', [source], ['lifted_source'])).toThrow()
})
test('empty coverage and changed baseline axiom sets refuse', () => {
  expect(() => auditLiftLog(good, [source], [])).toThrow('empty')
  expect(() => auditLiftLog(good, [source], ['lifted_source'], {lifted_source: []})).toThrow('axiom set changed')
  expect(auditLiftLog(good, [source], ['lifted_source'], {lifted_source: ['Quot.sound', 'propext', 'Classical.choice']})).toHaveLength(2)
})
test('legacy gate native opt-in remains separate from release lift policy', () => {
  const log = "'x' depends on axioms: [Lean.trustCompiler]"
  expect(gate(log, [], true)).toEqual([])
  expect(gate(log, [], false)).toHaveLength(1)
})
