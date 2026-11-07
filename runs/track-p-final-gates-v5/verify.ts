// Recheck recorded acceptance evidence. No proof search or subprocess is run.
import assert from 'node:assert/strict'
import {readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {join} from 'node:path'
const root = process.argv[2] ?? 'runs/track-p-final-gates-v5'
const evidence = process.argv[3] ?? 'runs/track-p-final-evidence'
const revision = '699b5160938737deb7776a65858617e19a1fc13f'
const base = '40693c7a2e9adcae77c6558dedb8278bd5704ce7'
const text = (p: string) => readFileSync(p, 'utf8')
const json = (p: string) => JSON.parse(text(p))
const records = (p: string) => text(p).split('\n').filter(l => l.startsWith('{')).map(l => JSON.parse(l))
const sha = (p: string) => createHash('sha256').update(readFileSync(p)).digest('hex')
const gates = json(join(root, 'summary.json'))
assert.equal(gates.passes, true)
assert.deepEqual(gates.errors, [])
assert.equal(gates.ic3syn.pairs, 87)
assert.equal(gates.ic3syn.cand, 84)
assert.equal(gates.ic3syn.base, 81)
assert.deepEqual(gates.ic3syn.regressions, [])
assert.equal(gates.duoai.pairs, 10)
assert.equal(gates.duoai.cand, 10)
assert.equal(gates.duoai.base, 10)
assert.deepEqual(gates.duoai.regressions, [])
assert.equal(gates.broken.total, 29)
assert.deepEqual(gates.broken.proven, [])
assert.equal(gates.shards.rows.length, 7)
assert(gates.shards.rows.every((r: any) => r.exit === 0))
assert.equal(gates.shards.tests, 746)
const strict = [1, 2, 3].map(i => {
  const path = join(root, 'strict', `paxos-r${i}.log`)
  const r = records(path).find(r => r.id === 'paxos_epr')
  assert.equal(r.search.verdict, 'proven')
  assert(r.search.ms <= 60000)
  assert(text(path).includes('STRICT_EXIT=0'))
  return {repeat: i, ms: r.search.ms, retainedLaws: r.search.found.length}
})
const bar = json(join(root, 'quick-bar', 'report.json'))
assert.equal(bar.trees.cand.sha, revision)
assert.equal(bar.trees.base.sha, base)
assert.deepEqual(bar.coverageErrors, [])
assert.deepEqual(bar.results.map((r: any) => r.group).sort(), ['chc', 'its', 'sv', 'tip', 'f1', 'f2', 'rw', 'g332', 'onecpu', 'lean'].sort())
assert(bar.results.every((r: any) => r.cand && !r.error && r.metas.every((m: any) => m.code === 0)))
for (const r of bar.results) assert.equal(r.base.length, r.group === 'lean' ? 0 : ['g332', 'onecpu'].includes(r.group) ? 1 : 3, r.group + ' baseline repetitions')
const views = Object.entries(bar).filter(([, v]: any) => v && typeof v === 'object' && 'candidate' in v)
assert.equal(views.length, 11)
for (const [key, value] of views) {
  const v = value as any
  assert.equal(v.candidate.wrong ?? 0, 0, key + ' wrong answers')
  assert(!(v.tasks ?? []).some((t: any) => t.kind === 'wrong'), key + ' wrong comparison')
  assert(!(v.tasks ?? []).some((t: any) => t.kind === 'lost' && t.solid), key + ' solid loss')
}
assert.equal(bar.lean.candidate.checked, bar.lean.candidate.sampled)
assert.equal(bar.lean.candidate.checked, 6)
const onecpu = text(join(root, 'quick-bar', 'REPORT.md'))
assert(onecpu.includes('Failed jobs: candidate none; base none.'))
const family = records(join(evidence, 'family38.log')).find(r => r.kind === 'summary')
assert.equal(family.checked, 38)
assert.equal(family.total, 38)
assert.equal(family.closedFamily, true)
const certificates = records(join(evidence, 'certificates.log'))
assert.equal(certificates.length, 2)
for (const r of certificates) {
  assert.equal(r.checked, true)
  assert.equal(r.dropWitnessRejected, true)
  assert.equal(r.searchWork, 0)
  assert.deepEqual(r.nonzeroSearchCosts, {})
  assert.equal(r.goalSHA256, sha(join('runs/track-p-certs', r.id, 'goal.json')))
  assert.equal(r.proofSHA256, sha(join('runs/track-p-certs', r.id, 'proof.json')))
}
const files = (dir: string): string[] => readdirSync(dir, {withFileTypes: true}).flatMap(e => e.isDirectory() ? files(join(dir, e.name)) : [join(dir, e.name)])
const paths = [...files(root), ...files(evidence)].filter(p => !p.endsWith('/acceptance.json')).sort()
const result = {passes: true, revision, base, strict, ic3syn: {candidate: 84, base: 81, pairs: 87, losses: 0}, duoai: {candidate: 10, base: 10, pairs: 10}, broken: gates.broken, tests: 746, quickBar: {groups: 10, views: 11, wrong: 0, solidLosses: 0, leanChecked: 6}, family: {checked: 38, total: 38, closedFamily: true}, certificates, files: Object.fromEntries(paths.map(p => [p, sha(p)]))}
writeFileSync(join(root, 'acceptance.json'), JSON.stringify(result, null, 2) + '\n')
console.log(JSON.stringify({...result, certificates: certificates.map(r => ({id: r.id, checked: r.checked, searchWork: r.searchWork})), files: paths.length}))
