import {describe, expect, test} from 'bun:test'
import {assertExactCoverage, canonicalDefinitions, canonicalJobs} from './full-gate-runner'
import {readPackTar} from './full-gate-worker'

const h = 'a'.repeat(64)
const suite = [{name: 'first', cmd: 'true', cwd: '.', timeout: 42}, {name: 'second', cmd: 'false'}]

describe('full gate planning (not a release receipt)', () => {
  test('binds every canonical job without dropping fields', () => {
    const seen: unknown[] = []
    expect(canonicalDefinitions(suite, job => { seen.push(job); return h })).toEqual([
      {name: 'first', definitionSha256: h}, {name: 'second', definitionSha256: h},
    ])
    expect(seen).toEqual(suite)
  })
  test('rejects incomplete and unsafe archives', () => {
    expect(() => readPackTar(Buffer.alloc(512))).toThrow('tar length')
    expect(() => readPackTar(Buffer.alloc(1536))).toThrow('archive member')
  })
  test('rejects duplicates, unsafe cwd, and an incompatible backend', () => {
    expect(() => canonicalJobs([suite[0], suite[0]])).toThrow('duplicate')
    expect(() => canonicalJobs([{name: 'bad', cmd: 'true', cwd: '../outside'}])).toThrow('cwd')
    expect(() => canonicalJobs([{name: 'bad', cmd: 'true', backend: 'modal'}])).toThrow('non-boat')
  })
  test('rejects omitted, duplicate, unexpected, and changed jobs', () => {
    const expected = canonicalDefinitions(suite, () => h)
    expect(() => assertExactCoverage(expected, expected)).not.toThrow()
    expect(() => assertExactCoverage(expected, expected.slice(0, 1))).toThrow('missing')
    expect(() => assertExactCoverage(expected, [expected[0]!, expected[0]!])).toThrow('duplicate')
    expect(() => assertExactCoverage(expected, [...expected, {name: 'other', definitionSha256: h}])).toThrow('unexpected')
    expect(() => assertExactCoverage(expected, [expected[0]!, {...expected[1]!, definitionSha256: 'b'.repeat(64)}])).toThrow('mismatch')
  })
})
