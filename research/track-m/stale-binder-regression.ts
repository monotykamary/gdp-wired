// Correctness regression only: kind laws, not the 29 safety obligations, timings or counted-unit bars.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {protocols} from '../protocols/ic3syn/models.ts'
import {checkLaws} from '../../kernel/kernel.ts'
import {proveLaws, proveSetFast} from '../../kernel/prove.ts'

const outDir = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!outDir) throw Error('native exported output directory required')
mkdirSync(outDir, {recursive: true})
const selected = protocols
if (selected.length !== 29 || new Set(selected.map(p => p.id)).size !== 29 || !selected.some(p => p.id === 'mldr')) throw Error('expected exact original 29 including MLDR')
const rows: unknown[] = []
let failed = false
const summarize = (r: ReturnType<typeof proveSetFast>, machine: Parameters<typeof proveSetFast>[0], laws: Parameters<typeof proveSetFast>[1]) => ({proven: r.proven, checked: r.checked, independentlyChecked: !!r.proof && checkLaws(machine, laws, r.proof), failed: r.failed ?? null})
for (const p of selected) {
  const first = p.make(), firstLaws = first.kindLaws()
  const a = summarize(proveSetFast(first.machine, firstLaws), first.machine, firstLaws)
  const fresh = p.make(), laws = fresh.kindLaws()
  const b = summarize(proveSetFast(fresh.machine, laws), fresh.machine, laws)
  const ordinary = proveLaws(fresh.machine, laws)
  const c = {proven: ordinary.proven, checked: ordinary.checked, independentlyChecked: !!ordinary.proof && checkLaws(fresh.machine, laws, ordinary.proof), failed: ordinary.failed ?? null}
  const pass = [a, b, c].every(x => x.proven && x.checked && x.independentlyChecked)
  failed ||= !pass
  rows.push({protocol: p.id, kindLawCount: laws.length, freshLawTextChanged: JSON.stringify(firstLaws) !== JSON.stringify(laws), first: a, fresh: b, ordinary: c, pass})
  writeFileSync(join(outDir, 'kind-laws-regression.json'), JSON.stringify({schema: 'stale-binder-kind-regression/v1',alphaSetting: process.env.GDP_MEMO_ALPHA ?? 'default',scope: 'KIND_LAWS_ONLY_NOT_SAFETY_OR_PERFORMANCE',complete: rows.length === 29,pass: !failed,rows}, null, 2)+'\n')
  console.log(JSON.stringify({protocol: p.id, pass}))
}
if (failed) process.exitCode = 1
