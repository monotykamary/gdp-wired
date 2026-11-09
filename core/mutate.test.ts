import {expect, test} from 'bun:test'
import {mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {checkMutations, type MutationConfig} from './mutate.ts'
import {main} from './cli.ts'

const source = '\ufeffexport const answer = true;\r\n'
const fixture = (run: (config: MutationConfig, dir: string) => void | Promise<void>) => async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-mutate-'))
  writeFileSync(join(dir, 'policy.ts'), source)
  const command = [process.execPath, '-e', "const fs = require('fs'); process.exit(fs.readFileSync('policy.ts', 'utf8').includes('= true') ? 0 : 1)"]
  const config: MutationConfig = {cwd: dir, lawSuite: 'laws', suites: [{name: 'examples', command: [process.execPath, '-e', 'process.exit(0)']}, {name: 'laws', command}], mutants: [{file: 'policy.ts', from: '= true', to: '= false', bug: 'wrong decision', name: 'flip'}]}
  try { await run(config, dir) } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('mutate: baseline, caught/missed table, repeatable edits, exact byte restoration', fixture((config, dir) => {
  config.mutants.push({...config.mutants[0]!, name: 'second', bug: 'line | break\nhere'})
  const before = readFileSync(join(dir, 'policy.ts'))
  const result = checkMutations(config)
  expect(result.passed).toBe(true)
  expect(result.rows).toHaveLength(2)
  expect(result.rows[0]!.suites.laws!.status).toBe('caught')
  expect(result.rows[0]!.suites.examples!.status).toBe('missed')
  expect(result.markdown).toContain('| flip | wrong decision | missed | caught |')
  expect(result.markdown).toContain('line \\| break here')
  expect(readFileSync(join(dir, 'policy.ts'))).toEqual(before)
}))

test('mutate: a surviving law mutant fails and CLI returns one', fixture(async (config, dir) => {
  config.suites[1]!.command = [process.execPath, '-e', 'process.exit(0)']
  expect(checkMutations(config).passed).toBe(false)
  writeFileSync(join(dir, 'mutants.json'), JSON.stringify({...config, cwd: '.'}))
  expect(await main(['mutate', join(dir, 'mutants.json')])).toBe(1)
  expect(readFileSync(join(dir, 'policy.ts'), 'utf8')).toBe(source)
}))

test('mutate: successful command-line check uses config-relative paths', fixture(async (config, dir) => {
  writeFileSync(join(dir, 'mutants.json'), JSON.stringify({...config, cwd: '.'}))
  expect(await main(['mutate', join(dir, 'mutants.json'), '--json'])).toBe(0)
}))

test('mutate: missing/ambiguous source and a broken baseline refuse before mutation', fixture((config, dir) => {
  config.mutants[0]!.from = 'absent'
  expect(() => checkMutations(config)).toThrow('from text not found')
  config.mutants[0]!.from = 'e'
  expect(() => checkMutations(config)).toThrow('ambiguous')
  config.mutants[0]!.from = '= true'
  config.suites[0]!.command = [process.execPath, '-e', 'process.exit(1)']
  expect(() => checkMutations(config)).toThrow('fails unmutated')
  expect(readFileSync(join(dir, 'policy.ts'), 'utf8')).toBe(source)
}))

test('mutate: timeout/spawn errors are not law kills and restore the file', fixture((config, dir) => {
  config.timeoutMs = 1000
  config.suites[1]!.command = [process.execPath, '-e', "const fs = require('fs'); if(fs.readFileSync('policy.ts','utf8').includes('= false')) while(true) {}"]
  const result = checkMutations(config)
  expect(result.passed).toBe(false)
  expect(result.rows[0]!.suites.laws!.status).toBe('error')
  expect(readFileSync(join(dir, 'policy.ts'), 'utf8')).toBe(source)
  config.suites[1]!.command = ['gdp-this-command-does-not-exist']
  expect(() => checkMutations(config)).toThrow('fails unmutated')
  expect(readFileSync(join(dir, 'policy.ts'), 'utf8')).toBe(source)
}))

test('mutate: rejects unsafe configs, no-op edits and source symlinks', fixture((config, dir) => {
  expect(() => checkMutations({...config, lawSuite: 'absent'})).toThrow('designated lawSuite')
  expect(() => checkMutations({...config, suites: [config.suites[0]!, config.suites[0]!]})).toThrow('unique suite names')
  expect(() => checkMutations({...config, timeoutMs: 0})).toThrow('timeoutMs')
  expect(() => checkMutations({...config, mutants: [{...config.mutants[0]!, name: ''}]})).toThrow('name must be')
  expect(() => checkMutations({...config, mutants: [{...config.mutants[0]!, to: '= true'}]})).toThrow('different to')
  symlinkSync(join(dir, 'policy.ts'), join(dir, 'link.ts'))
  expect(() => checkMutations({...config, mutants: [{...config.mutants[0]!, file: 'link.ts'}]})).toThrow('non-symlink')
  expect(readFileSync(join(dir, 'policy.ts'), 'utf8')).toBe(source)
}))
