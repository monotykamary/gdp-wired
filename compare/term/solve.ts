// One ARI integer transition system through gdp-wired: `bun compare/term/solve.ts <task.ari> [--limit 60]`.
// Prints one JSON line per stage and a last one with the answer:
//   - terminates: a rank (or a tuple, in order) and the invariants it needs, found by proveLoop's search (core/cycles.ts's
//     findRank: linear ranks from the runs, the exact LP, degree 2 one product at a time, inferLaws for the invariants),
//     every goal's tree checked by the kernel, and checked again here (loopObligations of the loop as translated); its
//     certificate (`cert`) the cyclic proof those trees translate to where it is made within the limit
//     (kernel/prove.ts's certLoop), else the usual trees (`usual`, and why); the answer is printed once the trees are
//     checked again, and again with the certificate once it is made (`not made` where the limit came first)
//   - nonterminating: a lasso, a run of the translated loop (gdp-wired's interpreter, random turns) that comes back to a
//     state it was in, replayed as the task's own steps and confirmed by ari.ts's evaluator, which uses no gdp-wired code;
//     or a recurrent set (core/nonterm.ts's findNeverEnds: a closed set of states, the turn from each given by terms, a
//     start and a stem into it), its closure goal's tree checked by the kernel (kernel.ts's checkRecur), the certificate
//     printed (`recur`) for NonTerm.lean's never_ends_of; a large program's set closed by its cases, one per location
//     (`cases`: kernel.ts's checkRecurCases, NonTerm.lean's never_ends_of_cases); a lasso among them replayed by ari.ts's
//     evaluator too
//   - unknown (and why: the rank the runs gave and the goal the kernel refused, or no rank), or unsupported (and why)
// The time: a lasso search first (2 s), a recurrent set (4 s, `--recur-ms`; an accelerated set a stem reaches up to 10 s
// before the limit), then the rank search with 70% of what is left before a margin of the limit, then a recurrent set
// again (3/5 of what is left; such a set 85% of it) and lassos with the rest.
// `--scc`: the rank search on each strongly connected component of the locations, chained, from any state at its cut
// points (scc.ts: a stronger statement, counted apart); a task with no cycle of locations is proven whole. The lassos
// are always the task's own runs.
// `--want terminates` or `--want nonterminating`: only that answer is searched for (c2ari.py's two translations of a
// recursive C program, each exact for one answer).
import {readFileSync} from 'node:fs'
import {type Ari, type Lasso, Unsupported, checkLasso, parseAri, type Step} from './ari.ts'
import {type Facts, deadRules, facts, lift, without} from './facts.ts'
import {factLawSets, factLaws, rankOnTask, recurOnTask} from './ontask.ts'
import type {Law} from '../../core/machine.ts'
import {type Built, build, stepOf} from './translate.ts'
import {components} from './scc.ts'
import {findRank, showE} from '../../core/cycles.ts'
import {interpret} from '../../core/machine.ts'
import {type Tree, check, loopMachine, loopObligations} from '../../kernel/kernel.ts'
import {certLoop, proveLaws, withDeadline} from '../../kernel/prove.ts'
import {findNeverEnds} from '../../core/nonterm.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const limit = opt('--limit', 60), lassoMs = opt('--lasso-ms', 2000), margin = opt('--margin', 9), scc = args.includes('--scc'), ntMs = opt('--recur-ms', 4000)
const want = args.includes('--want') ? args[args.indexOf('--want') + 1] : ''
const t0 = performance.now(), ms = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({ms: ms(), ...o}))
const done = (answer: string, o: object = {}) => { say({stage: 'answer', answer, ...o}); process.exit(0) }

let task, task0: Ari, f: Facts | undefined, b: Built, b0: Built, dead0 = 0
const name = file.split('/').pop()!
try {
  task = task0 = parseAri(readFileSync(file, 'utf8'))
  b = b0 = build(task0, name)
  // the facts at locations (facts.ts), the task rewritten with them, where the searches look (`--no-facts` without;
  // `--split`, research's, splits locations by a residue, whose answers the task's own loop can't take); every answer
  // made again on the task's own loop (ontask.ts)
  f = args.includes('--no-facts') ? undefined : facts(task0, args.includes('--split') ? 8 : 1)
  if (f) { task = f.task; b = build(task, name, {fixed: b0.fixed, active: b0.active}) }
  // and the rules the kernel shows never fire, left out (facts.ts's deadRules)
  const dead = args.includes('--no-facts') ? new Set<number>() : deadRules(b)
  if (dead.size) { f = without(task0, f, dead); task = f.task; b = build(task, name, {fixed: b0.fixed, active: b0.active}) }
  dead0 = dead.size
} catch (e) {
  if (e instanceof Unsupported) done('unsupported', {why: e.message})
  done('unsupported', {why: `import failed: ${(e as Error).message.slice(0, 200)}`, error: true})
}
const loop = b!.loop
// a lasso as the task's own steps, replayed by ari.ts's evaluator on the task as written
const replayed = (w: Lasso): string | undefined => {
  if (!f) return checkLasso(task0!, w)
  const all = lift(task0!, f, w.start, [...w.stem, ...w.cycle])
  return checkLasso(task0!, {start: w.start, stem: all.slice(0, w.stem.length), cycle: all.slice(w.stem.length)})
}
say({stage: 'import', ...(f ? {facts: {split: f.split, fixed: f.fixed, dropped: f.dropped, dead: dead0, locations: f.task.funs.size}} : {}), locations: b!.locs.length, rules: b!.plans.length, slots: b!.slots, fixed: b!.fixed.size, inputs: b!.nInputs, features: b!.features})

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
        const bad = replayed(w)
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
if (want !== 'terminates') {
  lassos(Math.min(t0 + lassoMs, t0 + limit * 1000))
  say({stage: 'lassos', runs, turns, refused: refusedWitness})
}

// --- runs that never end: a closed recurrent set with its turn given (core/nonterm.ts), its closure goal's tree checked
// by the kernel (kernel.ts's checkRecur; NonTerm.lean's never_ends_of). Where the set is a lasso's, the lasso is also
// turned back into the task's steps and replayed by ari.ts's evaluator.
function neverEnds(ms: number, tag: string, extend = ms, accel?: number, l = loop): void {
  if (ms < 200) return
  let v
  try { v = findNeverEnds(l, {ms, extend, cases: true, ...(accel ? {accel} : {})}) } catch (e) { say({stage: 'recur', tag, error: (e as Error).message.slice(0, 300)}); return }
  const {ms: searchMs, ...counts} = v.stats
  say({stage: 'recur', tag, proven: v.proven, checked: v.checked, ...(v.by ? {by: v.by} : {}), ...(v.why ? {why: v.why} : {}), searchMs, ...counts})
  let r = v.recur ?? v.cases
  if (!(v.proven && v.checked && r)) return
  // (on the task's own loop, where the set is the rewritten task's: else only a lasso replayed on the task answers)
  let onTask = 'as written'
  if (f && l !== b0!.loop) {
    const r0 = f.split ? undefined : recurOnTask(b0!, b!, task0!, f, r, t0 + (limit - 1) * 1000)
    onTask = r0 ? 'made again' : 'not made'
    say({stage: 'on task', onTask})
    r = r0 ?? r
  }
  const size = JSON.stringify(r.set).length + JSON.stringify(r.wit).length
  let replay: string | undefined
  if (v.lasso) {
    try {
      const ps = v.lasso.params
      let st = run.init(ps)
      const steps: Step[] = []
      for (const input of [...v.lasso.stem, ...v.lasso.cycle]) { steps.push(stepOf(b!, ps, st.scalars, input)); st = run.step(ps, st, input) }
      const start = Array.from({length: b!.slots}, (_, j) => String((ps[`a${j}`] ?? 0) - (ps[`a${j}$n`] ?? 0)))
      replay = replayed({start, stem: steps.slice(0, v.lasso.stem.length), cycle: steps.slice(v.lasso.stem.length)}) ?? 'confirmed'
    } catch (e) { replay = `not replayed: ${(e as Error).message.slice(0, 120)}` }
  }
  // (not made there and no lasso: the search again, on the task's own loop, in the same time)
  if (onTask === 'not made' && replay !== 'confirmed') { if (l !== b0!.loop) neverEnds(ms, tag, extend, accel, b0!.loop); return }
  done('nonterminating', {by: onTask === 'not made' ? 'lasso' : 'recurrent set', kind: v.by, ...('cases' in r ? {cases: r.cases.length} : {}), stem: r.stem.length, setSize: size, ...(replay ? {replay} : {}), ...(f ? {onTask} : {}), recur: size < 200_000 && onTask !== 'not made' ? r : undefined})
}
// (the accelerated cycles have 75% of the first search after its runs; a set of theirs that a stem reaches may take
// until 10 s before the limit: its cycle keeps it, by the closed forms, and a run gets there, so its loop is very likely
// not to halt, and the rank search would find nothing)
if (want !== 'terminates') neverEnds(Math.min(ntMs, limit * 1000 - ms() - 1000), 'first', (limit - 10) * 1000 - ms(), 0.75)

// --- the rank ---------------------------------------------------------------------------------------------------------
// findRank on a loop, then the kernel again on the loop as translated: every goal of its halting, with the rank and the
// laws found.
type Proven = {ok: boolean, rank?: string, laws?: string[], goals?: number, cert?: () => string, why?: string}
// `given`: laws the search may read and the kernel proves with the rank; `onTask`: the task's own loop, where the rank
// found on the rewritten one is proven again (with the facts as laws).
function prove(l: typeof loop, ms: number, tag: object = {}, given: Law[] = [], onTask?: {b: Built, laws: Law[][]}): Proven {
  let f
  try { f = findRank(l, given, {ms}) } catch (e) { say({stage: 'rank', ...tag, error: (e as Error).message.slice(0, 300)}); return {ok: false, why: 'rank search threw'} }
  say({stage: 'rank', ...tag, proven: f.proven, checked: f.checked, ...(f.found ? {rank: f.found.rank, laws: f.found.laws} : {}), ...(f.goal ? {goal: f.goal, stuck: String(f.stuck).slice(0, 200)} : {}), ...(f.why ? {why: f.why} : {})})
  if (f.proven && f.checked && f.rank && f.trees) {
    let lc = l, laws = [...given, ...f.laws ?? []], trees = f.trees
    if (onTask) {
      // (with the facts it needs first, then every one, each its share of the time)
      lc = onTask.b.loop
      let t2: Record<string, Tree> | undefined
      const own = laws
      for (const [i, facts] of onTask.laws.entries()) {
        const now = performance.now(), end = t0 + (limit - 1) * 1000, until = i === onTask.laws.length - 1 ? end : now + (end - now) / 2
        laws = [...facts, ...own]
        t2 = withDeadline(until, () => rankOnTask(onTask.b, laws, f.rank!, until))
        if (t2) break
      }
      say({stage: 'on task', ...tag, onTask: t2 ? 'made again' : 'not made'})
      // (not made there: the search again on the task's own loop, in the time left)
      if (!t2) return left() > 1000 ? prove(onTask.b.loop, left(), tag) : {ok: false, why: `rank ${f.found?.rank} of the rewritten task, not proven on the task`}
      trees = t2
    }
    const goals = loopObligations(lc, laws, f.rank)
    const missing = goals.filter(g => !trees[g.name] || !check(g, trees[g.name]!)).map(g => g.name)
    if (!missing.length) {
      // the certificate later, once the answer is printed (making it has no clock of its own)
      const cert = () => {
        const c0 = performance.now(), c = withDeadline(t0 + (limit - 2) * 1000, () => certLoop(lc, laws, f.rank!, trees))
        say({stage: 'cert', ...tag, cert: c?.checked ? 'cyclic' : 'usual', certMs: Math.round(performance.now() - c0), ...(c && !c.checked ? {why: c.why.slice(0, 200)} : {})})
        return c?.checked ? 'cyclic' : 'usual'
      }
      return {ok: true, rank: `(${f.rank.map(showE).join(', ')})`, laws: f.found?.laws ?? [], goals: goals.length, cert}
    }
    say({stage: 'recheck', ...tag, missing})
    return {ok: false, why: 'the kernel refused a tree on the recheck'}
  }
  return {ok: false, why: f.why ?? 'no rank'}
}
// the rank search's time: 70% of what is left before the margin (the recurrent set's second search has the rest)
const rankUntil = ms() + (want === 'terminates' ? 1 : 0.7) * ((limit - margin) * 1000 - ms()), left = () => rankUntil - ms()
let why = 'no rank'
// (per component, the task's own components, each from a state at its cut points where the task's facts hold: the
// facts proven the task's invariants by the kernel first, and its laws in each component; none where they aren't)
const comps = scc ? components(task0!) : []
let sccFacts = new Map<string, Map<number, bigint>>()
if (scc && comps.length && f && !f.split && f.consts.size && want !== 'nonterminating') {
  const laws = factLaws(b0!, f.consts), v = laws.length ? withDeadline(t0 + Math.min(10_000, left() / 4), () => proveLaws(loopMachine(b0!.loop), laws)) : undefined
  if (v?.proven && v.checked) sccFacts = f.consts
  say({stage: 'facts', laws: laws.length, proven: !!(v?.proven && v.checked)})
}
if (want === 'nonterminating') why = 'no rank searched (--want nonterminating)'
else if (scc && comps.length) {
  // each component on its own, from any state at its cut points; every one must halt
  say({stage: 'components', components: comps.map(c => ({locations: c.locations, rules: c.rules, chained: c.chained}))})
  const sizes: object[] = []
  const ranks: string[] = [], certs: (() => string)[] = []
  let all = true
  for (const [k, c] of comps.entries()) {
    let bc
    try { bc = build(c.task, `component ${k}`, {starts: c.starts, slice: true, facts: sccFacts}) } catch (e) { why = `component ${k}: ${(e as Error).message.slice(0, 200)}`; all = false; break }
    sizes.push({slots: bc.slots, dropped: bc.dropped.size, fixed: bc.fixed.size})
    const out = prove(bc.loop, Math.max(1000, left() / (comps.length - k)), {component: k, slots: bc.slots, dropped: bc.dropped.size, fixed: bc.fixed.size}, factLaws(bc, sccFacts))
    if (!out.ok) { why = `component ${k}: ${out.why}`; all = false; break }
    ranks.push(out.rank!)
    certs.push(out.cert!)
  }
  if (all) {
    const o = {by: 'components', ranks, components: comps.length, sizes}
    say({stage: 'answer', answer: 'terminates', ...o, cert: 'not made'})
    done('terminates', {...o, cert: certs.map(c => c()).every(c => c === 'cyclic') ? 'cyclic' : 'usual'})
  }
} else {
  const out = prove(loop, Math.max(1000, left()), {}, [], f ? {b: b0!, laws: f.split ? [[]] : factLawSets(b0!, task0!, f)} : undefined)
  if (out.ok) {
    // the answer as soon as the kernel has checked every tree again; then the certificate, and the answer with it
    const o = {by: 'rank', rank: out.rank, laws: out.laws, goals: out.goals}
    say({stage: 'answer', answer: 'terminates', ...o, cert: 'not made'})
    done('terminates', {...o, cert: out.cert!()})
  }
  why = out.why!
}
if (want !== 'terminates') {
  neverEnds(((limit - 2) * 1000 - ms()) * 0.6, 'again', ((limit - 2) * 1000 - ms()) * 0.85)
  lassos(t0 + (limit - 2) * 1000)
  say({stage: 'lassos', runs, turns, refused: refusedWitness})
}
done('unknown', {why})
