import { describe, expect, test } from 'bun:test'
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import { canonicalJobHash } from './full-gate-contract'
import { extractFailureSignature, matchKnownFailure, validateKnownFailuresPolicy } from './known-failures'

const jobs = [{name: 'exists', cmd: 'bun test exists'}, {name: 'test', cmd: 'bun test a'}]
const hash = canonicalJobHash(jobs[1]!)
const signature = {failedTests: ['test A'], diagnostics: ['error: assertion failed']}
const policy = {schema: 'gdp-known-failures/v1', baselineCommit: 'a'.repeat(40), evidence: {triageSha256: 'b'.repeat(64), comparisonSha256: 'c'.repeat(64)}, entries: [{job: 'test', definitionSha256: hash, exitCode: 1, signature}], requiredPass: ['exists']}

describe('known failure signatures', () => {
  test('canonical keyed and JevFabric jobs bootstrap BridgeRules in dependency order', () => {
    const canonical = JSON.parse(readFileSync(new URL('../../supercomputer/suite.json', import.meta.url), 'utf8')) as {name: string; cmd: string}[]
    for (const name of ['lean-keyed', 'lean-jev-fabric']) {
      const job = canonical.find(job => job.name === name)!
      expect(job.cmd).toContain('export PATH=$PWD/../scripts/lean-gate:$PATH')
      const modules = /for f in ([^;]+); do/.exec(job.cmd)![1]!.split(' ')
      for (const module of ['History', 'Live', 'Cyclic', 'Bridge', 'Ghost', 'Refine', 'BridgeRules']) expect(modules).toContain(module)
      for (const [before, after] of [['Cyclic', 'Bridge'], ['Live', 'Ghost'], ['Ghost', 'Refine'], ['Bridge', 'BridgeRules'], ['Refine', 'BridgeRules'], ['History', 'BridgeRules']] as const) {
        expect(modules.indexOf(before)).toBeLessThan(modules.indexOf(after))
      }
    }
  })
  test('generic empty policy and exact signature', () => {
    expect(validateKnownFailuresPolicy({...policy, entries: []}, jobs).entries).toEqual([])
    const checked = validateKnownFailuresPolicy(policy, jobs)
    expect(matchKnownFailure(checked, 'test', hash, 1, signature).job).toBe('test')
    expect(extractFailureSignature('', 'error: assertion failed\n(fail) test A [12.34ms]\n 1 fail\n')).toEqual(signature)
  })
  test('wrong job, hash, exit, extra test, extra diagnostic, exists and empty signature reject', () => {
    for (const [name, h, code, sig] of [
      ['other', hash, 1, signature], ['test', 'f'.repeat(64), 1, signature], ['test', hash, 2, signature],
      ['test', hash, 1, {...signature, failedTests: ['test A', 'test B']}],
      ['test', hash, 1, {...signature, diagnostics: [...signature.diagnostics, 'error: new']}],
      ['exists', hash, 1, signature], ['test', hash, 1, {failedTests: [], diagnostics: []}],
    ] as const) expect(() => matchKnownFailure(policy as never, name, h, code, sig as never)).toThrow()
  })
  test('Bun footer and repeated markers do not collapse', () => {
    expect(() => extractFailureSignature('', 'error: assertion failed\n(fail) test A [1ms]\n 2 fail\n')).toThrow()
    const parsed = extractFailureSignature('', 'error: one\n(fail) same [1ms]\nerror: two\n(fail) same [2ms]\n 2 fail\n')
    expect(parsed.failedTests).toEqual(['same', 'same'])
    expect(parsed.diagnostics).toEqual(['error: one', 'error: two'])
    const withSummary = 'error: one\n(fail) same [1ms]\nerror: two\n(fail) same [2ms]\n2 tests failed:\n(fail) same [1ms]\n(fail) same [2ms]\n\n 2 fail\n'
    expect(extractFailureSignature('', withSummary, ['Lean version 4'])).toEqual(parsed)
    expect(() => extractFailureSignature('', withSummary.replace('(fail) same [2ms]\n\n', '(fail) extra [2ms]\n\n'))).toThrow()
    expect(() => extractFailureSignature('', '(FAIL) unknown\n 1 fail\n')).toThrow()
  })
  test('complete Lean reports retain blocks and reject extra errors and forbidden axioms', () => {
    const report = '/tmp/run/Proofs.lean:12:3: error: Type mismatch\n  actual\nbut is expected\n  wanted\n'
    const result = extractFailureSignature('', '', [report])
    expect(result.diagnostics).toEqual(['Proofs.lean:12:3: error: Type mismatch\n  actual\nbut is expected\n  wanted'])
    const extra = extractFailureSignature('', '', [report + 'Proofs.lean:13:2: error: extra\n'])
    expect(extra.diagnostics.length).toBe(2)
    const forbidden = extractFailureSignature('', '', ["'law' depends on axioms: [propext, Bad.axiom, Quot.sound]\naxiom-gate: bad\n"])
    expect(forbidden.diagnostics.length).toBe(2)
    const sorry = "Proofs.lean:1:1: warning: declaration uses 'sorry'\n"
    const oneSorry = extractFailureSignature('', '', [sorry])
    expect(oneSorry.diagnostics).toEqual([sorry.trim()])
    expect(extractFailureSignature('', '', [sorry, sorry]).diagnostics).toHaveLength(2)
    expect(extractFailureSignature('', '', ["'law' depends on axioms: []\n"]).diagnostics).toEqual([])
    const json = '{"id":"wo","tries":2,"search":{"verdict":"unknown","ms":123,"found":0}}'
    expect(extractFailureSignature(json + '\nnot-exported\n', '', ['Lean version 4']).diagnostics).toEqual([json.replace('123', '0'), 'not-exported'].sort())
    expect(extractFailureSignature('error: wrapper broke\n', '', [report]).diagnostics).toContain('error: wrapper broke')
    expect(extractFailureSignature(report, '', [report]).diagnostics).toEqual(result.diagnostics)
    expect(extractFailureSignature('', '', [report, report]).diagnostics).toEqual([...result.diagnostics, ...result.diagnostics])
    expect(() => extractFailureSignature('Proofs.lean:1:1: error: x\n', '')).toThrow()
  })
  test('Bun file context binds identical titles and summary markers preserve it', () => {
    const failure = 'error: assertion failed\n(fail) same title [1ms]\n'
    const baseline = extractFailureSignature('', 'a.test.ts:\n' + failure + ' 1 fail\n')
    const changed = extractFailureSignature('', 'b.test.ts:\n' + failure + ' 1 fail\n')
    expect(baseline.failedTests).toEqual(['a.test.ts :: same title'])
    const scoped = {...policy, entries: [{...policy.entries[0]!, signature: baseline}]}
    expect(() => matchKnownFailure(scoped as never, 'test', hash, 1, changed)).toThrow()
    const both = 'a.test.ts:\n' + failure + 'b.test.ts:\n' + failure + '2 tests failed:\n(fail) same title [1ms]\n(fail) same title [1ms]\n\n 2 fail\n'
    expect(extractFailureSignature('', both).failedTests).toEqual(['a.test.ts :: same title', 'b.test.ts :: same title'])
  })
  test('Lean mirrors are body-aware, filtered and one-to-one', () => {
    const report = 'Proofs.lean:12:3: error: Type mismatch\n  actual\nbut is expected\n  wanted\n'
    const original = extractFailureSignature('', '', [report])
    const filtered = 'Proofs.lean:12:3: error: Type mismatch\n  wanted\n'
    expect(extractFailureSignature(filtered, '', [report])).toEqual(original)
    const changed = report.replace('  wanted', '  different')
    expect(extractFailureSignature(changed, '', [report]).diagnostics).toHaveLength(2)
    expect(extractFailureSignature(report, report, [report]).diagnostics).toHaveLength(2)
    expect(extractFailureSignature(report, report, [report, report]).diagnostics).toHaveLength(2)
  })
  test('Keyed outbox identity binds section bytes and relative positions, not earlier certificates', () => {
    const section = 'def outbox_machine : Nat := 0\ntheorem law0 : True := by trivial\n'
    const source = 'import BridgeRules\n' + section
    const report = 'Keyed.lean:3:11: error: Type mismatch\n  actual\nbut is expected to have type\n  wanted\n'
    const evidence = [{file: 'Keyed.lean', source}]
    const original = extractFailureSignature(report, '', [report], evidence)
    const digest = createHash('sha256').update(section).digest('hex')
    expect(original.diagnostics[0]).toBe(`Keyed.lean:section=outbox_machine@${digest}:2:11: error: Type mismatch\n  actual\nbut is expected to have type\n  wanted`)
    const moved = report.replace(':3:11:', ':5:11:')
    expect(extractFailureSignature(moved, '', [moved], [{file: 'Keyed.lean', source: '-- prefix changed\n\n' + source}])).toEqual(original)
    expect(extractFailureSignature(moved, '', [moved])).not.toEqual(original)
    const scoped = {...policy, entries: [{...policy.entries[0]!, signature: original}]}
    for (const changed of [
      extractFailureSignature(report, '', [report], [{file: 'Keyed.lean', source: source.replace('Nat := 0', 'Nat := 1')}]),
      extractFailureSignature('', '', [report.replace(':3:11:', ':2:11:')], evidence),
      extractFailureSignature('', '', [report.replace(':3:11:', ':3:12:')], evidence),
      extractFailureSignature('', '', [report.replace('  wanted', '  different')], evidence),
      extractFailureSignature('', '', [report + 'Keyed.lean:1:1: error: new prefix failure\n'], evidence),
    ]) expect(() => matchKnownFailure(scoped as never, 'test', hash, 1, changed)).toThrow()
  })
  test('Keyed source evidence rejects ambiguity, invalid shape and impossible positions', () => {
    const source = 'def outbox_machine : Nat := 0\n'
    const report = 'Keyed.lean:1:1: error: mismatch\n'
    for (const evidence of [null, {}, [{file: '../Keyed.lean', source}], [{file: 'Keyed.lean', source, untrustedHash: 'x'}], [{file: 'Keyed.lean', source}, {file: 'Keyed.lean', source}], [{file: 'Keyed.lean', source: source + source}], [{file: 'Keyed.lean', source: 'no section'}]]) {
      expect(() => extractFailureSignature('', '', [report], evidence)).toThrow()
    }
    expect(() => extractFailureSignature('', '', [report.replace(':1:1:', ':100:1:')], [{file: 'Keyed.lean', source}])).toThrow()
    expect(extractFailureSignature('', '', ['Other.lean:7:1: error: unchanged\n'], [{file: 'Keyed.lean', source}]).diagnostics).toEqual(['Other.lean:7:1: error: unchanged'])
  })
  test('pending metadata and required exists fail closed', () => {
    expect(() => validateKnownFailuresPolicy({...policy, pending: 'missing Lean'}, jobs)).toThrow()
    expect(() => validateKnownFailuresPolicy({...policy, requiredPass: []}, jobs)).toThrow()
    expect(() => validateKnownFailuresPolicy({...policy, entries: [{...policy.entries[0], job: 'exists', definitionSha256: canonicalJobHash(jobs[0]!)}]}, jobs)).toThrow()
  })
})
