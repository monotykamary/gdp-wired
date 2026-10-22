// A bounded model check over a CHC task's rule: `bun research/dag/bmc.ts <task.smt2> [--k 10] [--ms 240000]
// [--no-z3]`. For k = 1, 2, ..., the rule (compare/chc/translate.ts's build) unrolled k steps from its start as one
// kernel goal (kernel.ts's substE/substC: step j's request named input@j, its assumption a hypothesis, the state after
// it the step's terms over the state before; the last hypothesis that the run is at error after step k). The goal's
// hypotheses hold together exactly when some run of k requests reaches error.
//   - the prototype (cdcl.ts) decides it: refuted (no run of k steps; its DAG checked by check-dag.ts) or a model, whose
//     requests are replayed on the compiled rule and checked against the CHC itself (translate.ts's checkDerivation);
//   - z3 (a reference, labelled so) decides the goal's SMT-LIB (goalio.ts), and a model it gives is replayed and checked
//     the same way.
// Prints one JSON line per k and engine, and a last line with the first k each engine found a checked run at.
import {readFileSync, writeFileSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {parseChc} from '../../compare/chc/chc.ts'
import {type Step, build, checkDerivation} from '../../compare/chc/translate.ts'
import type {C, E} from '../../core/machine.ts'
import {type Goal, type Subst, substC, substE} from '../../kernel/kernel.ts'
import {toSmt} from './goalio.ts'
import {cdcl} from './cdcl.ts'
import {checkDag} from './check-dag.ts'

const file = process.argv[2]!
const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const K = Number(arg('--k') ?? 10), ms = Number(arg('--ms') ?? 240000), z3 = !process.argv.includes('--no-z3')
const t0 = performance.now()
const chc = parseChc(readFileSync(file, 'utf8')), b = build(chc), r = b.rule, m = r.machine
const say = (o: object) => console.log(JSON.stringify({ms: Math.round(performance.now() - t0), ...o}))

const k0 = (value: number): E => ({op: 'const', value})
const varE = (name: string): E => ({op: 'var', name})
// The unrolled goal: the state after j steps as terms over the params and the requests before.
function unrolled(k: number): {goal: Goal, inputs: string[][]} {
  const hyps: C[] = []
  if (m.pre) hyps.push(m.pre)
  let state: Record<string, E> = {...m.state}
  const inputs: string[][] = []
  for (let j = 0; j < k; j++) {
    const names = m.inputs.map(n => `${n}@${j}`)
    inputs.push(names)
    const vars: Record<string, E> = {...state, ...Object.fromEntries(m.inputs.map((n, q) => [n, varE(names[q]!)]))}
    const flags: Record<string, C> = {}
    for (const [f, c] of Object.entries(m.step.flags ?? {})) flags[f] = substC(c, {vars, maps: {}, flags})
    const s: Subst = {vars, maps: {}, flags}
    if (m.assume) hyps.push(substC(m.assume, s))
    if (m.pre) hyps.push(m.pre)
    // Every request's yes/no values are 0 or 1 and its clause one of the clauses (what encodeInput makes of a request).
    for (let q = 0; q < b.inBool; q++) hyps.push({op: '<=', a: varE(`y${q}@${j}`), b: k0(1)})
    hyps.push({op: '<', a: varE(`c@${j}`), b: k0(b.clauseNames.length)})
    state = Object.fromEntries(Object.entries(state).map(([n, e]) => [n, m.step.state?.[n] ? substE(m.step.state[n]!, s) : e]))
  }
  hyps.push(substC({op: 'not', x: b.law.holds}, {vars: state, maps: {}, flags: {}}))
  return {goal: {name: `reach error in ${k} steps`, hyps}, inputs}
}
// A model's requests, replayed on the compiled rule and checked against the CHC.
const g = r.compiled()
function check(k: number, w: Record<string, number>): string | undefined {
  try {
    let st = g.init({})
    const steps: Step[] = []
    for (let j = 0; j < k; j++) {
      const raw: Record<string, number | boolean | string> = {c: b.clauseNames[w[`c@${j}`] ?? 0]!}
      for (let q = 0; q < b.inInt; q++) raw[`x${q}`] = (w[`x${q}@${j}`] ?? 0) - (w[`x${q}$neg@${j}`] ?? 0)
      for (let q = 0; q < b.inBool; q++) raw[`y${q}`] = (w[`y${q}@${j}`] ?? 0) === 1
      const before = r.decode(st), next = g.step({}, st, r.encodeInput(raw as never))
      steps.push({clause: Number(String(raw.c).slice(1)), input: raw, before, after: r.decode(next)})
      st = next
    }
    return checkDerivation(b, chc, steps)
  } catch (e) { return `replay: ${(e as Error).message.slice(0, 100)}` }
}
// z3's model: the requests' values, by (get-value).
function z3Run(goal: Goal, inputs: string[][], limit: number): {answer: string, seconds: number, w?: Record<string, number>} {
  const names = inputs.flat()
  const text = toSmt(goal).replace('(check-sat)\n', `(check-sat)\n(get-value (${names.map(n => `|${n}|`).join(' ')}))\n`)
  writeFileSync('/tmp/bmc.smt2', text)
  const t = performance.now(), p = spawnSync('timeout', [String(Math.max(1, Math.round(limit / 1000))), 'z3', '-smt2', '/tmp/bmc.smt2'], {encoding: 'utf8', maxBuffer: 1 << 28})
  const seconds = Math.round(performance.now() - t) / 1000, out = p.stdout ?? ''
  const answer = out.split('\n')[0]?.trim() || (p.status === 124 ? 'timeout' : 'error')
  if (answer !== 'sat') return {answer, seconds}
  const w: Record<string, number> = {}
  // (z3 writes a symbol in bars only where it needs them: c@0 is a simple symbol)
  for (const mm of out.matchAll(/\((\|[^|]+\||[^\s()|]+) (\(- (\d+)\)|\d+)\)/g)) w[mm[1]!.replace(/^\|(.*)\|$/, '$1')] = mm[3] !== undefined ? -Number(mm[3]) : Number(mm[2])
  return {answer, seconds, w}
}

const found: Record<string, number | undefined> = {prototype: undefined, z3: undefined}
const until = t0 + ms
for (let k = 1; k <= K && performance.now() < until; k++) {
  const {goal, inputs} = unrolled(k)
  if (found.prototype === undefined) {
    const t = performance.now(), left = until - t
    const per = Math.min(left, Math.max(5000, left / (K - k + 1)))
    const out = cdcl(goal, {until: t + per})
    const o = out.out as {stuck?: string, witness?: Record<string, number>, root?: number}
    let verdict: string, why: string | undefined
    if (o.root !== undefined) { const c = checkDag(goal, {nodes: out.nodes, root: o.root}); verdict = c.ok ? 'no run (DAG checked)' : 'no run (DAG REJECTED)'; why = c.ok ? undefined : c.why }
    else if (o.stuck === 'sat' && o.witness) { why = check(k, o.witness); verdict = why ? 'a model, not a run' : 'a run (checkDerivation)'; if (!why) found.prototype = k }
    else verdict = o.stuck ?? '?'
    say({k, engine: 'prototype', verdict, ...(why ? {why} : {}), searchMs: Math.round(performance.now() - t), hyps: goal.hyps.length, conflicts: out.stats.conflicts, decisions: out.stats.decisions})
  }
  if (z3 && found.z3 === undefined) {
    const z = z3Run(goal, inputs, Math.min(60000, until - performance.now()))
    let why: string | undefined
    if (z.w) { why = check(k, z.w); if (!why) found.z3 = k }
    say({k, engine: 'z3 (reference)', answer: z.answer, seconds: z.seconds, ...(z.w ? {run: why ? 'not a run' : 'a run (checkDerivation)'} : {}), ...(why ? {why} : {})})
  }
  if (found.prototype !== undefined && (found.z3 !== undefined || !z3)) break
}
say({done: true, prototypeK: found.prototype ?? null, z3K: found.z3 ?? null})
process.exit(0)
