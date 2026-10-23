// The CDCL search the same with reader.ts's clean values kept and without: `bun research/bmc2/same.ts <task.smt2>... `
// prints, per bounded-run goal (depths 1 to 6, relaxed and as it is), the search's counts; run with GDP_READER_CLEAN=0
// and without, and compare.
import {readFileSync} from 'node:fs'
import {parseChc} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {bmcGoal, fixed, reduce, relax} from '../../core/bmc.ts'
import {growCdcl, cdclStats} from '../../kernel/cdcl.ts'
import {counted, clock} from '../../kernel/prove.ts'
const depth = Number(process.env.DEPTH ?? 6), nodes = Number(process.env.NODES ?? 3000)
for (const file of process.argv.slice(2)) {
  let b
  try { b = build(parseChc(readFileSync(file, 'utf8'))) } catch { continue }
  for (let k = 1; k <= depth; k++) {
    let g
    try { g = bmcGoal(b.rule.machine, [b.law], k) } catch { break }
    const f = fixed(g.hyps)
    if (!f) continue
    for (const [label, hyps] of [['exact', f.hyps], ['relaxed', relax(f.hyps)]] as const) {
      if (!hyps) continue
      const r = reduce(hyps)
      if (!r) continue
      for (const key of Object.keys(cdclStats)) if (typeof (cdclStats as unknown as Record<string, unknown>)[key] === 'number') (cdclStats as unknown as Record<string, number>)[key] = 0
      const budget = {nodes: 200_000 - nodes}
      const out = counted(200, () => growCdcl({name: g.name, hyps: r.hyps}, new Map(), {...budget, until: clock() + 1e12}, {model: true}))
      const {decisions, conflicts, leaves, resolved, coreSize, boundRounds} = cdclStats
      console.log(JSON.stringify([file.split('/').pop(), k, label, 'tree' in out ? 'tree' : out.stuck, 'tree' in out ? '' : out.why, budget.nodes, decisions, conflicts, leaves, resolved, coreSize, boundRounds, 'tree' in out ? '' : Object.keys(out.witness ?? {}).length]))
    }
  }
}
