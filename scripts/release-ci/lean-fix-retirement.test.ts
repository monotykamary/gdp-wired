import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {canonicalJobHash} from './full-gate-contract'
import {validateKnownFailuresPolicy} from './known-failures'

const retired = ['lean-package-0', 'lean-package-1', 'lean-package-2', 'lean-package-3', 'lean-cyclic', 'lean-cycles', 'lean-cycles-loops', 'lean-protocols-sync', 'lean-jev-fabric', 'lean-ksteps']

test('repaired Lean jobs must pass and cannot return as known failures', () => {
  const jobs = JSON.parse(readFileSync(new URL('../../supercomputer/suite.json', import.meta.url), 'utf8')) as {name: string, cmd: string}[]
  const policy = validateKnownFailuresPolicy(JSON.parse(readFileSync(new URL('./known-failures.json', import.meta.url), 'utf8')), jobs)
  for (const name of retired) {
    expect(policy.requiredPass).toContain(name)
    expect(policy.entries.some(entry => entry.job === name)).toBe(false)
    const job = jobs.find(entry => entry.name === name)!
    expect(job).toBeDefined()
    const reintroduced = {...policy, entries: [...policy.entries, {job: name, definitionSha256: canonicalJobHash(job), exitCode: 1, signature: {failedTests: [], diagnostics: ['error: regression']}}]}
    expect(() => validateKnownFailuresPolicy(reintroduced, jobs)).toThrow('unexpected or duplicate job')
  }
})
