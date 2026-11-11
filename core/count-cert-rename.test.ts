import {expect, test} from 'bun:test'
import {type E, get, n, x} from './machine.ts'
import {countCertificateRenamer} from './count-cert-rename.ts'
import {type CountCert, check, columnTerm, linear, termColumn} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
test('certificate renaming preserves map names, nested cells, products, and term expressions', () => {
  const term: E = {op: 'sub', a: get('table', x('witness')), b: x('read')}, oldTerm = termColumn(term)
  const cert: CountCert = {reads: [['read', 'read', x('witness')]], insts: [{wit: 'witness', below: n(3), terms: [[1, 'read']], unit: 0}], frames: [{post: 'read', pre: 'prior', when: [{'table[witness:1]*read': 2, [oldTerm]: 1}]}], tree: {leaf: [], squares: [{'table[witness:1]*read': 1}], products: [[0, 1]]}}
  const before = JSON.stringify(cert), rename = countCertificateRenamer(new Map([['read', 'freshRead'], ['witness', 'freshWitness']]), clock() + 100), out = rename.certificate(cert)
  expect(out.reads).toEqual([['freshRead', 'read', x('freshWitness')]])
  expect(out.insts[0]!.wit).toBe('freshWitness'); expect(out.insts[0]!.terms).toEqual([[1, 'freshRead']])
  expect(out.frames![0]!.when[0]!['freshRead*table[freshWitness:1]']).toBe(2)
  const newColumn = Object.keys(out.frames![0]!.when[0]!).find(key => key.startsWith('⟦'))!
  expect(columnTerm(newColumn)).toEqual(rename.expression(term))
  expect(JSON.stringify(cert)).toBe(before)
})
test('renamed ordinary proof checks on the correspondingly renamed goal', () => {
  const goal = {name: 'alpha proof', hyps: [{op: '<' as const, a: n(0), b: x('source')}, {op: '<=' as const, a: x('source'), b: n(0)}]}, result = grow(goal, new Map(), {nodes: 0, until: clock() + 100})
  expect('tree' in result).toBe(true)
  if ('tree' in result) {const rename = countCertificateRenamer(new Map([['source', 'target']]), clock() + 100); expect(check({...goal, hyps: goal.hyps.map(rename.condition)}, rename.tree(result.tree))).toBe(true)}
})
test('renaming preserves explicit zeros used by source path identities', () => {
  const rename = countCertificateRenamer(new Map([['source', 'target']]), clock() + 100)
  expect(rename.row({source: 1, '1': 0})).toEqual({target: 1, '1': 0})
})
test('an expired certificate rename does no work', () => {
  const rename = countCertificateRenamer(new Map(), clock() - 1)
  expect(() => rename.row(linear(x('v'), new Map())!)).toThrow('deadline')
})
