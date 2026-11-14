// Correctness only: original kind laws, not safety obligations, timing or counted-unit bars.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {protocols} from '../protocols/ic3syn/models.ts'
import {admitCountedFamily} from '../../core/counts.ts'
import {checkCountedLaws, checkLaws} from '../../kernel/kernel.ts'
import {clock, proveLaws, proveSetFast} from '../../kernel/prove.ts'

const outDir = process.env.SUPERCOMPUTER_OUTPUT_DIR
if (!outDir) throw Error('native exported output directory required')
mkdirSync(outDir, {recursive: true})
if (protocols.length !== 29 || new Set(protocols.map(p => p.id)).size !== 29 || !protocols.some(p => p.id === 'mldr')) throw Error('expected original 29 including MLDR')
const rows: unknown[] = []
let failed = false
const prove = (r: ReturnType<(typeof protocols)[number]['make']>, ordinary = false) => {
  const laws = r.kindLaws(), machine = r.machine
  // The plain prover correctly refuses counted machines. Keep them intact and use
  // the native counted-family prover/checker; no stripped/projected machine is tested.
  if (Object.keys(machine.counts ?? {}).length) {
    const out = admitCountedFamily(machine, laws, laws, new Set(), clock() + 10000)
    const originalMachine = JSON.stringify(out.m) === JSON.stringify(machine)
    const callerCovered = laws.every(l => out.laws.some(x => x.name === l.name && JSON.stringify(x) === JSON.stringify(l)))
    return {route: 'counted-family', proven: out.proven, checked: !!out.proof && checkCountedLaws(out.m, out.laws, out.proof), originalMachine, callerCovered, emittedLawNames: out.laws.map(l => l.name), why: out.why ?? null}
  }
  const out = ordinary ? proveLaws(machine, laws) : proveSetFast(machine, laws)
  return {route: ordinary ? 'plain-ordinary' : 'plain-fast', proven: out.proven, checked: out.checked && !!out.proof && checkLaws(machine, laws, out.proof), originalMachine: true, callerCovered: true, failed: out.failed ?? null}
}
for (const p of protocols) {
  try {
    const first = p.make(), firstLaws = first.kindLaws(), a = prove(first)
    const fresh = p.make(), laws = fresh.kindLaws(), b = prove(fresh), c = prove(fresh, true)
    const pass = [a, b, c].every(x => x.proven && x.checked && x.originalMachine && x.callerCovered)
    failed ||= !pass
    rows.push({protocol: p.id, kindLawCount: laws.length, freshLawTextChanged: JSON.stringify(firstLaws) !== JSON.stringify(laws), first: a, fresh: b, reference: c, pass})
    console.log(JSON.stringify({protocol: p.id, pass}))
  } catch (error) {
    failed = true
    const message = error instanceof Error ? error.stack : String(error)
    rows.push({protocol: p.id, pass: false, error: message})
    console.error(JSON.stringify({protocol: p.id, pass: false, error: message}))
  }
  const complete = rows.length === 29
  writeFileSync(join(outDir, 'kind-laws-regression.json'), JSON.stringify({schema: 'stale-binder-kind-regression/v2',alphaSetting: process.env.GDP_MEMO_ALPHA ?? 'default',scope: 'ORIGINAL_KIND_LAWS_ONLY_NOT_SAFETY_OR_PERFORMANCE',complete,observedRowsPass: !failed,pass: complete && !failed,rows}, null, 2)+'\n')
}
if (failed) process.exitCode = 1
