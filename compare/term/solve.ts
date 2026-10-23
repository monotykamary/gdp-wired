// One ARI integer transition system through gdp-wired: `bun compare/term/solve.ts <task.ari> [--limit 60]`.
// Prints one JSON line per stage and a last one with the answer:
//   - terminates: a rank (or a tuple, in order) and the invariants it needs, found by proveLoop's search (core/cycles.ts's
//     findRank: linear ranks from the runs, the exact LP, degree 2 one product at a time, inferLaws for the invariants),
//     every goal's tree checked by the kernel, and checked again here (loopObligations of the loop as translated); its
//     certificate (`cert`) the cyclic proof those trees translate to where it is made within the limit
//     (kernel/prove.ts's certLoop), else the usual trees (`usual`, and why)
//   - nonterminating: a lasso, a run of the translated loop (gdp-wired's interpreter, random turns) that comes back to a
//     state it was in, replayed as the task's own steps and confirmed by ari.ts's evaluator, which uses no gdp-wired code
//   - unknown (and why: the rank the runs gave and the goal the kernel refused, or no rank), or unsupported (and why)
// The time: a lasso search first (2 s), then the rank search with all but a margin of the limit, then lassos again with
// what is left. `--scc`: the rank search on each strongly connected component of the locations, chained, from any
// state at its cut points (scc.ts: a stronger statement, counted apart); a task with no cycle of locations is proven
// whole. The lassos are always the task's own runs.
import {readFileSync} from 'node:fs'
import {Unsupported, checkLasso, parseAri, type Step} from './ari.ts'
import {type Built, build, stepOf} from './translate.ts'
import {components} from './scc.ts'
import {findRank, showE} from '../../core/cycles.ts'
import {interpret} from '../../core/machine.ts'
import {check, loopMachine, loopObligations} from '../../kernel/kernel.ts'
import {certLoop, withDeadline} from '../../kernel/prove.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const limit = opt('--limit', 60), lassoMs = opt('--lasso-ms', 2000), margin = opt('--margin', 9), scc = args.includes('--scc')
const t0 = performance.now(), ms = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({ms: ms(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

let task, b: Built
try {
  task = parseAri(readFileSync(file, 'utf8'))
  b = build(task, file.split('/').pop()!)
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `import failed: ${(e as Error).message.slice(0, 200)}`, error: true})
}
const loop = b!.loop
say({stage: 'import', locations: b!.locs.length, rules: b!.plans.length, slots: b!.slots, fixed: b!.fixed.size, inputs: b!.nInputs, features: b!.features})

// --- lassos -------------------------------------------------------------------------------------------------------------
const run = interpret(loopMachine(loop))
let seed = 7
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const out = new Map<number, number>()
for (const p of b!.plans) out.set(p.from, (out.get(p.from) ?? 0) + 1)
const pair = (x: number) => [Math.max(x, 0), Math.max(-x, 0)] as const
let runs = 0, turns = 0, refusedWitness = 0
function lassos(until: number): void {
  const bounds = [1, 2, 4, 8, 16, 64]
  while (performance.now() < until) {
    runs++
    const bound = bounds[runs % bounds.length]!, draw = () => rand(2 * bound + 1) - bound
    const start = Array.from({length: b!.slots}, draw)
    const ps: Record<string, number> = {}
    start.forEach((x, j) => { [ps[`a${j}`], ps[`a${j}$n`]] = pair(x) })
    let st = run.init(ps)
    const seen = new Map<string, number>(), trace: {scalars: Record<string, number>, input: Record<string, number>}[] = []
    for (let turn = 0; turn < 3000 && performance.now() < until; turn++) {
      const key = JSON.stringify(st.scalars)
      const at = seen.get(key)
      if (at !== undefined) {
        const steps: Step[] = trace.map(x => stepOf(b!, ps, x.scalars, x.input))
        const w = {start: start.map(String), stem: steps.slice(0, at), cycle: steps.slice(at)}
        const bad = checkLasso(task!, w)
        if (!bad) done('nonterminating', {by: 'lasso', stem: w.stem.length, cycle: w.cycle.length, witness: w, runs, turns})
        refusedWitness++
        say({stage: 'lasso', refused: bad})
        break
      }
      seen.set(key, turn)
      const k = out.get(st.scalars.pc!) ?? 0
      if (!k) break
      let next, input: Record<string, number> | undefined
      for (let tries = 0; tries < 40 && !next; tries++) {
        input = {t: rand(k)}
        for (let m = 0; m < b!.nInputs; m++) {
          // an input: small, or a value the state holds (x' = x is a common way back)
          const pick = rand(4) === 0 && b!.slots ? (st.scalars[`s${rand(b!.slots)}`] ?? ps[`a${rand(b!.slots)}`] ?? 0) * (rand(2) ? 1 : -1) : draw();
          [input[`i${m}`], input[`i${m}$n`]] = pair(pick)
        }
        try { next = run.step(ps, st, input) } catch { next = undefined }
      }
      if (!next) break
      trace.push({scalars: st.scalars, input: input!})
      turns++
      st = next
    }
  }
}
lassos(Math.min(t0 + lassoMs, t0 + limit * 1000))
say({stage: 'lassos', runs, turns, refused: refusedWitness})

// --- the rank ---------------------------------------------------------------------------------------------------------
// findRank on a loop, then the kernel again on the loop as translated: every goal of its halting, with the rank and the
// laws found.
function prove(l: typeof loop, ms: number, tag: object = {}): {ok: boolean, rank?: string, laws?: string[], goals?: number, cert?: string, why?: string} {
  let f
  try { f = findRank(l, [], {ms}) } catch (e) { say({stage: 'rank', ...tag, error: (e as Error).message.slice(0, 300)}); return {ok: false, why: 'rank search threw'} }
  say({stage: 'rank', ...tag, proven: f.proven, checked: f.checked, ...(f.found ? {rank: f.found.rank, laws: f.found.laws} : {}), ...(f.goal ? {goal: f.goal, stuck: String(f.stuck).slice(0, 200)} : {}), ...(f.why ? {why: f.why} : {})})
  if (f.proven && f.checked && f.rank && f.trees) {
    const goals = loopObligations(l, f.laws ?? [], f.rank)
    const missing = goals.filter(g => !f.trees![g.name] || !check(g, f.trees![g.name]!)).map(g => g.name)
    if (!missing.length) {
      const c0 = performance.now(), c = withDeadline(t0 + (limit - 2) * 1000, () => certLoop(l, f.laws ?? [], f.rank!, f.trees!))
      say({stage: 'cert', ...tag, cert: c?.checked ? 'cyclic' : 'usual', certMs: Math.round(performance.now() - c0), ...(c && !c.checked ? {why: c.why.slice(0, 200)} : {})})
      return {ok: true, rank: `(${f.rank.map(showE).join(', ')})`, laws: f.found?.laws ?? [], goals: goals.length, cert: c?.checked ? 'cyclic' : 'usual'}
    }
    say({stage: 'recheck', ...tag, missing})
    return {ok: false, why: 'the kernel refused a tree on the recheck'}
  }
  return {ok: false, why: f.why ?? 'no rank'}
}
const left = () => (limit - margin) * 1000 - ms()
let why = 'no rank'
const comps = scc ? components(task!) : []
if (scc && comps.length) {
  // each component on its own, from any state at its cut points; every one must halt
  say({stage: 'components', components: comps.map(c => ({locations: c.locations, rules: c.rules, chained: c.chained}))})
  const sizes: object[] = []
  const ranks: string[] = []
  let all = true, cyclic = true
  for (const [k, c] of comps.entries()) {
    let bc
    try { bc = build(c.task, `component ${k}`, {starts: c.starts, slice: true}) } catch (e) { why = `component ${k}: ${(e as Error).message.slice(0, 200)}`; all = false; break }
    sizes.push({slots: bc.slots, dropped: bc.dropped.size, fixed: bc.fixed.size})
    const out = prove(bc.loop, Math.max(1000, left() / (comps.length - k)), {component: k, slots: bc.slots, dropped: bc.dropped.size, fixed: bc.fixed.size})
    if (!out.ok) { why = `component ${k}: ${out.why}`; all = false; break }
    ranks.push(out.rank!)
    cyclic &&= out.cert === 'cyclic'
  }
  if (all) done('terminates', {by: 'components', ranks, components: comps.length, sizes, cert: cyclic ? 'cyclic' : 'usual'})
} else {
  const out = prove(loop, Math.max(1000, left()))
  if (out.ok) done('terminates', {by: 'rank', rank: out.rank, laws: out.laws, goals: out.goals, cert: out.cert})
  why = out.why!
}
lassos(t0 + (limit - 2) * 1000)
say({stage: 'lassos', runs, turns, refused: refusedWitness})
done('unknown', {why})
