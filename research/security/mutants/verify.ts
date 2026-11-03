import assert from 'node:assert/strict'
import {createHash} from 'node:crypto'
import {cpSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {mutate} from './operators.ts'
import {admit, fixtures, replaySource, summarize, type Measurement} from './run.ts'

const sha = (s: string) => createHash('sha256').update(s).digest('hex')
const json = (x: unknown): unknown => JSON.parse(JSON.stringify(x, (_k, v: unknown) => v instanceof Map ? {$map: [...v]} : v))
export async function verify(rows: Measurement[]) {
  assert.deepEqual(rows.map(r => r.fixture).sort(), fixtures, 'every owned fixture appears exactly once')
  const root = mkdtempSync(join(tmpdir(), 'security-replay-'))
  symlinkSync(resolve(import.meta.dir, '../../..', 'node_modules'), join(root, 'node_modules'), 'dir')
  let replayed = 0, witnesses = 0
  try {
    for (const row of rows) {
      const original = join(import.meta.dir, 'fixtures', row.fixture), file = join(original, row.file)
      assert.ok(/^module\.(ts|py)$/.test(row.file))
      const source = readFileSync(file, 'utf8'), language = row.file.endsWith('.ts') ? 'ts' : 'py'
      assert.equal(sha(source), row.baseline.sha256, 'unchanged clean source')
      const config = readdirSync(original).includes('gdp.toml') ? sha(readFileSync(join(original, 'gdp.toml'), 'utf8')) : undefined
      assert.equal(config, row.configSha256, 'exact deployment configuration')
      const generated = mutate(source, language)
      assert.deepEqual(row.mutants.map(m => m.id), generated.map(m => m.id), 'no missing, duplicate or selected mutants')
      for (const [i, mutation] of generated.entries()) {
        const saved = row.mutants[i]!
        assert.equal(sha(mutation.source), saved.side.sha256, 'exact regenerated mutant')
        assert.equal(saved.detected, admit(row.baseline, saved.side, saved.replays), 'recompute admission')
        assert.equal(saved.detected, true, 'every generated mutant must have a saved source refutation')
        const dir = join(root, `${row.fixture}-${mutation.id}`)
        mkdirSync(dir)
        for (const f of readdirSync(original)) cpSync(join(original, f), join(dir, f))
        const path = join(dir, row.file)
        writeFileSync(path, mutation.source)
        for (const record of saved.replays) {
          const law = saved.side.claims.find(l => l.entry === record.entry && l.name === record.law && l.expr === record.expr)!
          assert.ok(law?.run?.length && law.entry)
          const mutant = await replaySource(path, law, dir)
          const cleanLaw = row.baseline.claims.find(l => l.entry === law.entry && l.name === law.name && l.expr === law.expr)!
          const parent = await replaySource(file, {...cleanLaw, run: law.run, concreteOwner: law.concreteOwner}, dir, true)
          assert.deepEqual(json(mutant), json(record.mutant), 'saved mutant replay is reproduced exactly')
          assert.deepEqual(json(parent), json(record.parent), 'saved clean replay is reproduced exactly')
          assert.ok(mutant.ok && mutant.broken && parent.ok && !parent.broken)
          witnesses++
        }
        replayed++
      }
    }
    return {...summarize(rows), replayed, witnesses}
  } finally { rmSync(root, {recursive: true, force: true}) }
}

if (import.meta.main) {
  const input = process.argv[2]
  if (!input) throw new Error('usage: bun research/security/mutants/verify.ts measurement.json')
  const document = JSON.parse(readFileSync(input, 'utf8')) as {rows: Measurement[]}
  console.log(JSON.stringify(await verify(document.rows)))
}
