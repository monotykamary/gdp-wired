// The dumped root goals (research/query/dump.ts) asked again, each within $LAB_MS (60 s) of the wall: grow as it ships
// (a tree, else a model), or the CDCL search for a model alone (`asked`: as the dump asked it), on the goal or a part of it ($LAB_PARTS: all; few, its
// first two hypotheses and the conclusion; cells, the conclusion and the hypotheses sharing a cell with it; busy1, all
// and busy = 1); outcome, time, counted work, and whether a model found holds every hypothesis. Research tooling.
//   bun research/query/wide-lab.ts <file.json>...
import {readFileSync, writeFileSync} from 'node:fs'
import {type C, type E, walkOnce} from '../../core/machine.ts'
import {clock, counted, fullRate, fullWork, grow, usedHyps, wideHook, wideStats, withWall} from '../../kernel/prove.ts'
import {check} from '../../kernel/kernel.ts'
import {growCdcl} from '../../kernel/cdcl.ts'

const ms = Number(process.env.LAB_MS ?? 60_000), modes = (process.env.LAB_MODES ?? 'grow,model').split(','), parts = (process.env.LAB_PARTS ?? 'all').split(',')
const cellsOf = (c: unknown): Set<string> => { const s = new Set<string>(); const w = (e: any) => { if (!e || typeof e !== 'object') return; if (e.op === 'get') s.add(e.map + JSON.stringify(e.key)); for (const v of Object.values(e)) w(v) }; w(c); return s }
const partOf = (hyps: C[], p: string): C[] => {
  const last = hyps.at(-1)!
  if (p === 'few') return [hyps[0]!, hyps[1]!, last]
  if (p === 'busy1') return [...hyps.slice(0, -1), {op: '=', a: {op: 'var', name: 'busy'} as E, b: {op: 'const', value: 1} as E} as C, last]
  if (p === 'cells') { const lc = cellsOf(last); return [...hyps.slice(0, -1).filter((h, i) => i < 2 || [...cellsOf(h)].some(x => lc.has(x))), last] }
  return hyps
}
// ($LAB_DUMP: each part left unknown written there)
if (process.env.LAB_DUMP) { let n = 0; wideHook.on = (g, out) => { if (!('tree' in out) && out.stuck === 'unknown') writeFileSync(`${process.env.LAB_DUMP}/part-${n++}.json`, JSON.stringify({kind: 'grow', ms: 0, outcome: 'unknown', goal: g})) } }
for (const f of process.argv.slice(2)) {
  const d = JSON.parse(readFileSync(f, 'utf8'))
  for (const p of parts) for (const mode of modes) {
    const goal = {name: d.goal.name, hyps: partOf(d.goal.hyps, p)}
    const t = performance.now(), w = fullWork()
    const out = withWall(performance.now() + ms, () => counted(fullRate, () => mode === 'model' || (mode === 'asked' && d.kind === 'model')
      ? growCdcl(goal, new Map(), {nodes: 0, until: clock() + ms}, {model: true, core: true})
      : grow(goal, new Map(), {nodes: 0, until: clock() + ms}), true))
    const took = Math.round(performance.now() - t), used = 'tree' in out ? usedHyps(goal, out.tree).size : undefined, ok = 'tree' in out ? check(goal, out.tree) : undefined, ws = {...wideStats}
    Object.assign(wideStats, {goals: 0, trees: 0, models: 0, rounds: 0})
    const holds = undefined
    let size = 0
    walkOnce(goal.hyps, () => { size++ })
    console.log(JSON.stringify({f: f.split('/').at(-1), part: p, mode, hyps: goal.hyps.length, size, was: `${d.kind} ${d.outcome} ${d.ms}`,
      now: 'tree' in out ? 'tree' : `${out.stuck} ${out.why?.slice(0, 40) ?? ''}`, ms: took, work: Math.round(fullWork() - w), used, ok, ws, holds, of: d.goal.hyps.length}))
  }
}
