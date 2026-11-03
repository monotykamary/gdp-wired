import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {isDeepStrictEqual} from 'node:util'
import {budgetMs, cases, harness, materialize, prepare, replay, sha, type Row} from './run.ts'

const require = (ok: unknown, why: string) => { if (!ok) throw new Error(why) }
export function verify(rows: Row[]) {
  require(isDeepStrictEqual(rows.map(r => r.id).sort(), cases.map(c => c.id).sort()), 'incomplete or duplicated corpus')
  let witnesses = 0
  for (const c of cases) {
    const row = rows.find(r => r.id === c.id)!
    require(row.budgetMs === budgetMs && isDeepStrictEqual(row.harness, harness()), 'stale harness or budget')
    require(isDeepStrictEqual(row.provenance, c), 'provenance changed')
    const root = mkdtempSync(join(tmpdir(), 'verify-upstream-'))
    try {
      const source = prepare(c, root), parent = materialize(c, root, 'parent', source.source)
      require(row.baseline.sha256 === sha(source.source) && row.baseline.fullyRead && row.baseline.claims.length === c.policies.length && row.baseline.claims.every(l => l.verdict === 'proven'), 'clean baseline not fully proven')
      require(isDeepStrictEqual(row.mutants.map(m => m.id), source.mutations.map(m => m.id)), 'mutation denominator changed')
      for (const mutation of source.mutations) {
        const saved = row.mutants.find(m => m.id === mutation.id)!
        const {source: code, ...edit} = mutation
        for (const [key, value] of Object.entries(edit)) require(isDeepStrictEqual(saved[key as keyof typeof saved], value), 'mutation edit changed')
        require(saved.side.sha256 === sha(code) && saved.side.fullyRead && saved.detected, 'mutant not admitted')
        const target = materialize(c, root, mutation.id, code)
        require(saved.replays.length > 0, 'no saved replay')
        for (const recorded of saved.replays) {
          require(c.policies.some(p => isDeepStrictEqual(p, recorded.policy)), 'unknown policy')
          const law = saved.side.claims.find(l => l.name === recorded.policy.name && l.expr === recorded.policy.expr && l.verdict === 'broken')
          require(law?.run?.length, 'no counterexample')
          const mutant = replay(c, recorded.policy, target.file, law!.run!, target.directory)
          const clean = replay(c, recorded.policy, parent.file, law!.run!, parent.directory)
          require(mutant.ok && mutant.broken && mutant.steps.length > 0 && clean.ok && !clean.broken && clean.steps.length > 0, 'source witness did not reproduce')
          require(isDeepStrictEqual(mutant, recorded.mutant) && isDeepStrictEqual(clean, recorded.parent), 'source states changed')
          witnesses++
        }
      }
    } finally { rmSync(root, {recursive: true, force: true}) }
  }
  return {modules: rows.length, mutants: rows.reduce((n, r) => n + r.mutants.length, 0), witnesses, sourceReplays: witnesses * 2}
}

if (import.meta.main) {
  const document = JSON.parse(readFileSync(process.argv[2] ?? join(import.meta.dir, 'measurement.json'), 'utf8')) as {rows: Row[]}
  console.log(JSON.stringify(verify(document.rows)))
}
