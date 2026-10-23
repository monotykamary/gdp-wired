// Where a depth's time goes: `bun research/bmc2/time.ts <task.smt2> <k>`
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {bmcGoal, fixed, reduce, relax} from '../../core/bmc.ts'
const b = build(parseChc(readFileSync(process.argv[2]!, 'utf8')))
const k = Number(process.argv[3])
let t = performance.now()
const lap = (what: string) => { const n = performance.now(); console.log(what, Math.round(n - t)); t = n }
const g = bmcGoal(b.rule.machine, [b.law], k); lap('goal')
const f = fixed(g.hyps)!; lap('fixed')
const r = relax(f.hyps); lap('relax')
const d = reduce(r ?? f.hyps); lap(`reduce ${f.hyps.length} -> ${d?.hyps.length}`)
import {growCdcl, cdclStats} from '../../kernel/cdcl.ts'
import {counted, clock} from '../../kernel/prove.ts'
for (const [label, hyps] of [['relaxed', d!.hyps]] as const) {
  for (const key of Object.keys(cdclStats)) if (typeof (cdclStats as any)[key] === 'number') (cdclStats as any)[key] = 0
  cdclStats.on = true
  const t1 = performance.now()
  let used = 0
  const out = counted(200, () => { const s = clock(); const o = growCdcl({name: g.name, hyps}, new Map(), {nodes: 0, until: clock() + 60000}, {model: true, wall: performance.now() + 30000}); used = clock() - s; return o })
  const {nodes, decisions, conflicts, rowsMs, orderMs, boundMs, lpMs, solveMs, pivots, coreMs} = cdclStats
  console.log(label, JSON.stringify({out: 'tree' in out ? 'tree' : [out.stuck, out.why], wall: Math.round(performance.now() - t1), counted: Math.round(used), nodes, decisions, conflicts, rowsMs: Math.round(rowsMs), orderMs: Math.round(orderMs), boundMs: Math.round(boundMs), lpMs: Math.round(lpMs), solveMs: Math.round(solveMs), coreMs: Math.round(coreMs), pivots}))
}
