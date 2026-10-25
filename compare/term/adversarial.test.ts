// Adversarial ITS programs (adversarial/*.ari, written by the independent check of the ranks, research/verify-ranks
// on verify/ranks): small tasks at the translation's edges (negative values, truncated differences, div and mod,
// repeated or constant arguments, exists, slicing, constants past 2^53 folded). Each that some run never ends
// ("; expect: nonterminating") is never answered terminates: on the task's statement (one loop) and per component
// (scc.ts), the translation refuses it or the search gives no rank the kernel takes. Each terminating one, where it is
// proven, is proven by the kernel as any is, and none is answered nonterminating (no recurrent set the kernel checks).
// Each is read as solve.ts reads it: through the facts at its locations (facts.ts) where they change it, as written
// too.
import {expect, test} from 'bun:test'
import {readFileSync, readdirSync} from 'node:fs'
import {Unsupported, parseAri} from './ari.ts'
import {build} from './translate.ts'
import {components} from './scc.ts'
import {findRank} from '../../core/cycles.ts'
import {check, loopMachine, loopObligations, type Loop} from '../../kernel/kernel.ts'
import {findNeverEnds} from '../../core/nonterm.ts'
import {facts} from './facts.ts'
import {factLaws, rankOnTask, recurOnTask} from './ontask.ts'
import {proveLaws} from '../../kernel/prove.ts'
import type {Law} from '../../core/machine.ts'

const dir = `${import.meta.dir}/adversarial`
const files = readdirSync(dir).filter(f => f.endsWith('.ari')).sort()
// proven: a rank, its trees checked again by the kernel on the loop as translated (solve.ts's recheck); with the facts
// (facts.ts), as solve.ts reads them: the rank searched on the rewritten task and proven on the task's own loop with
// the facts as laws (ontask.ts), per component from states where the facts the kernel proved hold
const proven = (l: Loop, given: Law[] = []): boolean => {
  const f = findRank(l, given, {ms: 1500})
  return !!(f.proven && f.checked && f.rank && f.trees && loopObligations(l, [...given, ...f.laws ?? []], f.rank).every(g => f.trees![g.name] && check(g, f.trees![g.name]!)))
}
const halts = (text: string, scc: boolean, withFacts = false): boolean => {
  try {
    const task0 = parseAri(text), b0 = build(task0, 'task'), fs = withFacts ? facts(task0) : undefined
    if (!scc || !components(task0).length) {
      if (!fs) return proven(b0.loop)
      const r = findRank(build(fs.task, 'task', {fixed: b0.fixed, active: b0.active}).loop, [], {ms: 1500})
      return !!(r.proven && r.checked && r.rank && rankOnTask(b0, [...factLaws(b0, fs.consts), ...r.laws ?? []], r.rank, performance.now() + 5000))
    }
    const laws = fs ? factLaws(b0, fs.consts) : [], ok = laws.length ? proveLaws(loopMachine(b0.loop), laws) : undefined, cs = ok?.proven && ok.checked ? fs!.consts : new Map()
    return components(task0).every((c, k) => { const bc = build(c.task, `component ${k}`, {starts: c.starts, slice: true, facts: cs}); return proven(bc.loop, factLaws(bc, cs)) })
  } catch (e) {
    if (e instanceof Unsupported) return false
    throw e
  }
}

test('adversarial ITS programs: none that runs forever is answered terminates, on either statement', () => {
  const nonterm = files.filter(f => /expect:\s*nonterminating/.test(readFileSync(`${dir}/${f}`, 'utf8')))
  expect(nonterm.length).toBeGreaterThanOrEqual(37)
  for (const f of nonterm) {
    const text = readFileSync(`${dir}/${f}`, 'utf8')
    expect([f, halts(text, false), halts(text, true), halts(text, false, true), halts(text, true, true)]).toEqual([f, false, false, false, false])
  }
}, 480_000)

test('adversarial ITS programs: none whose runs all end is answered nonterminating, through the facts or not', () => {
  const term = files.filter(f => /expect:\s*terminates/.test(readFileSync(`${dir}/${f}`, 'utf8')))
  expect(term.length).toBeGreaterThanOrEqual(12)
  for (const f of term) {
    const task0 = parseAri(readFileSync(`${dir}/${f}`, 'utf8'))
    let b0
    try { b0 = build(task0, f) } catch (e) { if (e instanceof Unsupported) continue; throw e }
    const v = findNeverEnds(b0.loop, {ms: 1500, cases: true})
    expect([f, v.proven && v.checked]).toEqual([f, false])
    const fs = facts(task0)
    if (!fs) continue
    const bR = build(fs.task, f, {fixed: b0.fixed, active: b0.active}), w = findNeverEnds(bR.loop, {ms: 1500, cases: true}), r = w.recur ?? w.cases
    expect([f, !!(w.proven && w.checked && r && recurOnTask(b0, bR, task0, fs, r, performance.now() + 3000))]).toEqual([f, false])
  }
}, 240_000)

test('the facts at locations: constants as laws on the task, a residue a split only research reads', () => {
  const read = (f: string) => parseAri(readFileSync(`${dir}/${f}`, 'utf8'))
  expect(facts(read('facts_parity_nt.ari'))?.split ?? 0).toBe(0)
  expect(facts(read('facts_parity_nt.ari'), 8)?.split).toBe(1)
  expect(halts(readFileSync(`${dir}/facts_pin.ari`, 'utf8'), false, true)).toBe(true)
  // a constant after the start, a recurrent set on the rewritten task made again on the task's own loop
  const t = read('facts_const_nt.ari'), b0 = build(t, 'c'), fs = facts(t)!, bR = build(fs.task, 'c', {fixed: b0.fixed, active: b0.active})
  const w = findNeverEnds(bR.loop, {ms: 4000, cases: true}), r = w.recur ?? w.cases
  expect(!!(r && recurOnTask(b0, bR, t, fs, r, performance.now() + 4000))).toBe(true)
}, 60_000)

test('constants past 2^53 are refused, not rounded', () => {
  for (const f of ['n36_float_fold.ari', 'n37_float_fold_var.ari']) expect(() => build(parseAri(readFileSync(`${dir}/${f}`, 'utf8')), f)).toThrow(Unsupported)
})
