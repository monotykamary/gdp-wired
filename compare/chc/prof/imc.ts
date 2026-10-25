// Interpolation over the unrolling alone (core/interp.ts's imc): `bun compare/chc/prof/imc.ts <task.smt2> [--ms 55000]`
// (`--tools imc` in modal_chc.py). Answers as solve.ts does, each answer checked the same way: sat where the kernel
// proves the law with the fixed point as a law beside it (proveRule, no search), unsat where translate.ts's
// checkDerivation confirms the run against the CHC. What it measures: the search alone, on the second CPU's budget.
import {readFileSync} from 'node:fs'
import {parseChc} from '../chc.ts'
import {build, checkDerivation, requestOf, stepsOf} from '../translate.ts'
import {compress, imc} from '../../../core/interp.ts'
import type {C} from '../../../core/machine.ts'
import {expand, liftProven, prepare} from '../compose.ts'
import {proveRule} from '../../../core/dsl.ts'
import {counted, withDeadline} from '../../../kernel/prove.ts'

// (GDP_CHC_ARGS: more flags, as solve.ts reads them; `--compose`, `--slice`: the search on the system compose.ts makes,
// its answers expanded and lifted to the original rule and checked there)
// (the kernel's usual trees as a sat answer's certificate, as solve.ts has them)
process.env.GDP_CERT ??= 'usual'
const args = [...process.argv.slice(2), ...(process.env.GDP_CHC_ARGS ?? '').split(' ').filter(Boolean)], file = args[0]!
const ms = Number(args[args.indexOf('--ms') + 1] ?? 55_000) || 55_000, t0 = performance.now(), wall = t0 + ms
const say = (o: object) => { console.log(JSON.stringify({task: file, ms: Math.round(performance.now() - t0), ...o})); if ((o as {stage?: string}).stage === 'answer') process.exit(0) }
const chc0 = parseChc(readFileSync(file, 'utf8')), on = (f: string) => args.includes(f) && args[args.indexOf(f) + 1] !== '0'
const cc = prepare(chc0, {slice: on('--slice'), chains: on('--compose')}), bo = build(chc0), b = cc ? build(cc.chc) : bo, r = b.rule, m = r.machine
// (each query: its depth, its outcome's letter, the frontiers so far, its ms)
const steps: [number, string, number, number][] = []
let q0 = performance.now()
const out = counted(250, () => imc(m, b.law, {until: Infinity, wall, kinds: r.kindLaws().map(l => l.holds), progress: (k, what, info) => { const now = performance.now(); steps.push([k, what[0]!, info.parts!, Math.round(now - q0)]); q0 = now }}), true)
say({stage: 'imc', depths: steps, ...('why' in out ? {why: out.why} : {}), k: out.k})
if ('run' in out) {
  const raws = out.run.trace.map(t => requestOf(b, t as Record<string, unknown>)), orig = cc ? expand(bo, b, cc, stepsOf(b, raws)) : raws
  const bad = typeof orig === 'string' ? orig : checkDerivation(bo, chc0, stepsOf(bo, orig))
  if (bad) say({stage: 'imc', refused: bad})
  else say({stage: 'answer', answer: 'unsat', by: 'imc', steps: (orig as unknown[]).length})
} else if ('inv' in out) {
  const t1 = performance.now()
  // (GDP_IMC_SMALL=1: the invariant made a few clauses first, core/interp.ts's compress, each a law)
  const small = process.env.GDP_IMC_SMALL === '1' ? counted(250, () => compress(m, b.law, out.inv, r.kindLaws().map(l => l.holds), {until: Infinity, wall}), true) : undefined
  if (process.env.GDP_IMC_SMALL === '1') say({stage: 'small', clauses: small?.length ?? -1, ms: Math.round(performance.now() - t1)})
  const inv: C = small ? {op: 'and', xs: small} : out.inv, laws = small ? small.map((c, j) => ({name: `imc ${j}`, holds: c})) : [{name: 'imc', holds: out.inv}]
  const v = cc ? liftProven(cc, bo, {op: 'and', xs: [b.law.holds, ...r.kindLaws().map(l => l.holds), inv]}, wall) : withDeadline(wall, () => proveRule(r, [b.law, ...laws], {search: false}))
  const proven = v.proven && (!('checked' in v) || v.checked)
  say({stage: 'prove', proven, parts: out.parts, proveMs: Math.round(performance.now() - t1), ...('liftMs' in v ? {why: v.why, liftMs: v.liftMs} : {})})
  if (proven) say({stage: 'answer', answer: 'sat', by: 'imc', k: out.k})
}
say({stage: 'answer', answer: 'unknown'})
