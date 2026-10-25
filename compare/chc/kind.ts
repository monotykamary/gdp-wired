// The container's second CPU: `bun compare/chc/kind.ts <task.smt2> --ms <budget> --parent <pid> [--bmc 0]`, started by
// solve.ts once the task is read. Two searches in turn, neither knowing beforehand whether the task is sat or unsat:
// k-induction (core/kind.ts: the law over k = 2, 3, ... steps in a row with the rule's kinds assumed), and bounded runs
// (core/bmc.ts's boundedSearch: a deterministic loop's forced run, then a model of a k-step goal from the start to
// error, k = 1, 2, ..., its CDCL session kept between turns). Each turn a slice of wall time, k-induction first, the
// slices doubling after each pair (2 s each, then 4, 8, 16, ...), a search that is over leaving the rest to the other;
// a search cut by its slice goes on from where it stopped (k-induction from the depth it was asking, the bounded runs
// from their depth and session). k-induction proven and checked by the kernel's checkKInduction, or a bounded run that
// translate.ts's checkDerivation confirms against the CHC step by step, stops solve.ts (whose answer would come later,
// if at all) and prints the answer as solve.ts would; else this prints its stages and ends, and solve.ts goes on.
// `--bmc 0`: k-induction alone, as before (solve.ts then runs the bounded runs itself). `--imc 1`: interpolation over the
// unrolling (core/interp.ts's imcSearch) takes its turn too, after the bounded runs, going on from its depth and R; its
// fixed point is an invariant the kernel proves with the law (proveRule, no search), its run one checkDerivation
// confirms. `--kind 0`: no k-induction.
import {readFileSync} from 'node:fs'
import {parseChc} from './chc.ts'
import {type Raw, build, checkDerivation, requestOf, stepsOf} from './translate.ts'
import {type KindResult, proveKInduction} from '../../core/kind.ts'
import {boundedSearch} from '../../core/bmc.ts'
import {compress, imcSearch} from '../../core/interp.ts'
import {proveRule} from '../../core/dsl.ts'
import {clock, counted, fullRate, withDeadline} from '../../kernel/prove.ts'
import {expand, invOf, liftProven, prepare} from './compose.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const t0 = performance.now(), budget = opt('--ms', 50_000), parent = opt('--parent', 0), withBmc = opt('--bmc', 1) !== 0, withImc = opt('--imc', 0) !== 0, withKind = opt('--kind', 1) !== 0
const end = t0 + budget, ms = () => Math.round(performance.now() - t0)
const say = (o: object) => console.log(JSON.stringify({task: file, ms: ms(), ...o}))
// `--compose 1`: the bounded runs and interpolation read the composed rule (compose.ts), their runs expanded and their
// invariants lifted to the original rule, each checked there; k-induction reads the original (its proof has no
// invariant to lift).
const chc = parseChc(readFileSync(file, 'utf8')), bo = build(chc), cc = prepare(chc, {slice: opt('--slice', 0) !== 0, chains: opt('--compose', 0) !== 0})
const b = cc ? build(cc.chc) : bo, m = b.rule.machine, mo = bo.rule.machine
// A run of the rule searched, as the original's requests (expanded where composed), checked against the CHC.
const confirmed = (trace: Record<string, unknown>[]): {raws: Raw[]} | {bad: string} => {
  try {
    const raws = trace.map(t => requestOf(b, t)), orig = cc ? expand(bo, b, cc, stepsOf(b, raws)) : raws
    if (typeof orig === 'string') return {bad: orig}
    const bad = checkDerivation(bo, chc, stepsOf(bo, orig))
    return bad ? {bad} : {raws: orig}
  } catch (e) { return {bad: `not replayed: ${(e as Error).message.slice(0, 80)}`} }
}
const stop = () => { if (parent) { try { process.kill(parent, 'SIGKILL') } catch { /* gone */ } } }

// k-induction, a slice at a time. The track's limit is wall time, as for every solver: the wall stop is the slice, the
// counted one a bound twenty times it (a CDCL search for a tree counts each node's rows as it reads them, which on these
// goals runs the counted clock about twenty times past wall time: compare/chc/prof/kind-tree.ts, runs/kind/tree1).
const kindDepths: KindResult['depths'] = []
let kindFrom = 2, kindLive = withKind, kindWhy = ''
const kindTurn = (slice: number) => {
  const wall = Math.min(end, performance.now() + slice)
  const kd = proveKInduction(mo, bo.rule.kindLaws(), bo.law, {ms: 20 * slice, wall, from: kindFrom})
  kindDepths.push(...kd.depths)
  if (kd.proven && kd.checked) {
    stop()
    say({stage: 'kind', proven: true, checked: true, k: kd.k, depths: kindDepths})
    say({stage: 'answer', answer: 'sat', by: 'kind', k: kd.k})
    process.exit(0)
  }
  kindWhy = kd.why ?? (kd.proven ? 'not checked' : '')
  // Cut by its budget (a goal undecided, no tree, or no k within the slice): on from the depth it was asking (the next,
  // where it had just stepped past one) at its next turn; else over.
  const lastK = kd.depths.at(-1), cut = !kd.proven && /unknown|within the budget/.test(kindWhy)
  if (cut && wall < end) kindFrom = lastK ? (lastK[1] === 's' ? lastK[0] + 1 : lastK[0]) : kindFrom
  else kindLive = false
  if (kindFrom > 64) kindLive = false
}

// The bounded runs, a slice at a time (core/bmc.ts's budget: counted, bmcRate units a ms, beside the wall stop; the
// forced run 4.5 s of wall time in all, what it had as 30% of solve.ts's 15 s stage).
const bmcDepths: [number, string, number, number][] = []
let w0 = performance.now()
const bs = withBmc ? boundedSearch(m, [b.law], {forcedMs: 4500, progress: (k, o, c) => { bmcDepths.push([k, o[0]!, c, Math.round(performance.now() - w0)]); w0 = performance.now() }}) : undefined
let bmcLive = !!bs
const bmcTurn = (slice: number) => {
  w0 = performance.now()
  const out = bs!.run(slice, Math.min(end, performance.now() + slice))
  if (out === 'paused') return
  bmcLive = false
  say({stage: 'bmc', depth: bmcDepths.at(-1)?.[0] ?? 0, found: typeof out === 'object', depths: bmcDepths, by: 'second'})
  if (typeof out !== 'object') return
  const ok = confirmed(out.trace as Record<string, unknown>[])
  if ('bad' in ok) { say({stage: 'bmc', refused: ok.bad}); return }
  stop()
  say({stage: 'answer', answer: 'unsat', by: 'bmc', steps: ok.raws.length})
  process.exit(0)
}

// Interpolation over the unrolling, a slice at a time (counted as the bounded runs are, beside the wall stop).
const imcDepths: [number, string][] = []
const is = withImc ? imcSearch(m, b.law, {kinds: b.rule.kindLaws().map(l => l.holds), progress: (k, what) => { imcDepths.push([k, what[0]!]) }}) : undefined
let imcLive = !!is
const imcTurn = (slice: number) => {
  const wall = Math.min(end, performance.now() + slice)
  const out = counted(fullRate, () => is!.run(clock() + 20 * slice, wall), true)
  if (out === 'paused') return
  imcLive = false
  say({stage: 'imc', depths: imcDepths, k: out.k, ...('why' in out ? {why: out.why.slice(0, 80)} : {}), by: 'second'})
  if ('run' in out) {
    const ok = confirmed(out.run.trace as Record<string, unknown>[])
    if ('bad' in ok) { say({stage: 'imc', refused: ok.bad}); return }
    stop()
    say({stage: 'answer', answer: 'unsat', by: 'imc', steps: ok.raws.length})
    process.exit(0)
  }
  if ('inv' in out) {
    // (the invariant made a few clauses first, core/interp.ts's compress, each a law for the kernel; else as it is)
    const t1 = performance.now(), small = counted(fullRate, () => compress(m, b.law, out.inv, b.rule.kindLaws().map(l => l.holds), {until: Infinity, wall: end}), true)
    say({stage: 'imc', small: small?.length ?? -1, smallMs: Math.round(performance.now() - t1)})
    // (where the clauses aren't proven, the invariant as it is, in the time left)
    let proven = false
    for (const laws of [...(small ? [small.map((holds, j) => ({name: `imc ${j}`, holds}))] : []), [{name: 'imc', holds: out.inv}]]) {
      if (proven || performance.now() >= end) break
      const v = cc ? liftProven(cc, bo, invOf([b.law, ...b.rule.kindLaws(), ...laws])!, end) : withDeadline(end, () => proveRule(b.rule, [b.law, ...laws], {search: false}))
      proven = v.proven && (!('checked' in v) || v.checked)
      say({stage: 'imc', proven, parts: out.parts, laws: laws.length, ...('liftMs' in v ? {why: v.why, liftMs: v.liftMs, proveMs: v.proveMs} : {checked: v.checked})})
    }
    if (!proven) return
    stop()
    say({stage: 'answer', answer: 'sat', by: 'imc', k: out.k})
    process.exit(0)
  }
}

// Each live search its slice in turn; the last one live, the rest of the time.
// `--imc 2`: k-induction and interpolation share k-induction's slice, half each, the bounded runs' as before.
const half = opt('--imc', 0) === 2
for (let slice = 2000; performance.now() < end && (kindLive || bmcLive || imcLive); slice *= 2) {
  const share = (others: boolean, part = slice) => (others ? part : end - performance.now())
  const kindPart = half && imcLive ? slice / 2 : slice, imcPart = half && kindLive ? slice / 2 : slice
  if (kindLive) kindTurn(share(bmcLive || imcLive, kindPart))
  if (bmcLive && performance.now() < end) bmcTurn(share(kindLive || imcLive))
  if (imcLive && performance.now() < end) imcTurn(share(kindLive || bmcLive, imcPart))
}
if (withKind) say({stage: 'kind', proven: false, checked: false, depths: kindDepths, ...(kindWhy ? {why: kindWhy.slice(0, 120)} : {})})
if (bmcLive) say({stage: 'bmc', depth: bmcDepths.at(-1)?.[0] ?? 0, found: false, depths: bmcDepths, by: 'second'})
if (imcLive) say({stage: 'imc', depths: imcDepths, found: false, by: 'second'})
