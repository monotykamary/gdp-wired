// The prover's time, across every proof in the repo's examples: each domain's rules (and their broken variants),
// decisions and loops, and the examples of records and variants, recurrences, carried lists and folds. Each root goal's
// time, nodes and solver calls (kernel/prove.ts `profile`), the slowest goals, and the totals.
//   bun research/perf/prover-bench.ts [out.json] [--only domain,...]
import {writeFileSync} from 'node:fs'
import {profile} from '../../kernel/prove.ts'
import {type Verdict, proveDecision, proveFold, proveLeadsTo, proveLoop, proveSteps} from '../../core/dsl.ts'
import {domains} from '../../examples/index.ts'
import * as D from '../../examples/datatypes.ts'
import * as L from '../../examples/lemmas.ts'
import * as I from '../../examples/invoices.ts'
import * as F from '../../examples/folds.ts'

type Item = {item: string, ms: number, proven: boolean, goals: number}
const items: Item[] = []
profile.on = true
const run = (item: string, f: () => Verdict | {proven: boolean}) => {
  const g0 = profile.goals.length, t = performance.now()
  let proven = false
  try { proven = f().proven } catch (e) { proven = false; console.error(`${item}: ${(e as Error).message.slice(0, 120)}`) }
  items.push({item, ms: performance.now() - t, proven, goals: profile.goals.length - g0})
  for (const g of profile.goals.slice(g0)) (g as {item?: string}).item = item
}
const only = process.argv.includes('--only') ? process.argv[process.argv.indexOf('--only') + 1]!.split(',') : undefined
for (const d of domains) {
  if (only && !only.includes(d.domain)) continue
  for (const c of d.cases) {
    const name = `${d.domain}/${c.name}`
    if (c.kind === 'rule') {
      run(name, () => proveSteps(c.rule, c.laws, c.steps ?? []))
      for (const b of c.broken) run(`${name} (${b.name})`, () => proveSteps(b.rule, b.laws, b.steps ?? []))
    } else if (c.kind === 'decisions') {
      c.decisions.forEach((dec, j) => run(`${name} #${j}`, () => proveDecision(dec)))
      for (const b of c.broken) run(`${name} (${b.name})`, () => proveDecision(b.decision))
    } else {
      run(name, () => proveLoop(c.loop, c.laws))
      for (const b of c.broken) run(`${name} (${b.name})`, () => proveLoop(b.loop, b.laws))
    }
  }
}
if (!only) {
  run('datatypes/hold', () => proveSteps(D.hold(), D.holdLaws(), D.holdSteps()))
  run('datatypes/accounts', () => proveSteps(D.accounts(), D.accountLaws(), D.accountSteps()))
  run('datatypes/seats', () => proveSteps(D.seats(), D.seatLaws(), D.seatSteps()))
  run('datatypes/jobs', () => proveSteps(D.jobs(), D.jobLaws(), D.jobSteps()))
  D.approveLaws().forEach((d, j) => run(`datatypes/approve #${j}`, () => proveDecision(d)))
  run('lemmas/retries', () => proveSteps(L.retries(), L.retryLaws(), L.retrySteps()))
  run('lemmas/filled (made)', () => L.filled().verdict)
  run('lemmas/fill meter', () => proveSteps(L.fillMeter(), L.fillMeterLaws(), []))
  run('lemmas/ledger', () => proveSteps(L.ledger(), L.ledgerLaws(), []))
  run('lemmas/escalation', () => proveSteps(L.escalation(), L.escalationLaws(), []))
  run('lemmas/ladder', () => proveSteps(L.ladder(), L.ladderLaws(), []))
  run('lemmas/tank', () => proveSteps(L.tank(), L.tankLaws(), []))
  run('lemmas/area', () => proveSteps(L.area(), L.areaLaws(), []))
  run('lemmas/pump', () => proveLeadsTo(L.pump(), [], L.pumpLive()))
  run('invoices', () => proveSteps(I.invoices(), I.invoiceLaws(), I.invoiceSteps()))
  run('folds/rollup', () => proveFold(F.rollup(), F.rollupLaws()))
  run('folds/signoffs', () => proveFold(F.signoffs(), F.signoffLaws()))
}
const total = items.reduce((a, x) => a + x.ms, 0)
const goals = profile.goals as (typeof profile.goals[number] & {item: string})[]
console.log(`${items.length} items, ${goals.length} goals, ${(total / 1000).toFixed(1)} s; solver ${(profile.solveMs / 1000).toFixed(1)} s in ${profile.solves} calls, rows ${(profile.rowsMs / 1000).toFixed(1)} s`)
console.log('slowest items:')
for (const x of [...items].sort((a, b) => b.ms - a.ms).slice(0, 15)) console.log(`  ${x.ms.toFixed(0).padStart(7)} ms  ${x.proven ? 'proven ' : 'refused'}  ${x.item}`)
console.log('slowest goals:')
for (const g of [...goals].sort((a, b) => b.ms - a.ms).slice(0, 25)) console.log(`  ${g.ms.toFixed(0).padStart(7)} ms  ${String(g.nodes).padStart(6)} nodes  ${String(g.solves).padStart(6)} solves  solver ${g.solveMs.toFixed(0)} rows ${g.rowsMs.toFixed(0)}  ${g.proven ? '' : 'UNPROVEN '}${g.item}: ${g.name}`)
const out = process.argv[2] && !process.argv[2].startsWith('--') ? process.argv[2] : undefined
if (out) writeFileSync(out, JSON.stringify({items, goals, solveMs: profile.solveMs, rowsMs: profile.rowsMs, solves: profile.solves}, null, 1))
