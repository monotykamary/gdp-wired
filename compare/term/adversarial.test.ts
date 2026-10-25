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
import {check, loopObligations, type Loop} from '../../kernel/kernel.ts'
import {findNeverEnds} from '../../core/nonterm.ts'
import {facts} from './facts.ts'

const dir = `${import.meta.dir}/adversarial`
const files = readdirSync(dir).filter(f => f.endsWith('.ari')).sort()
// proven: a rank, its trees checked again by the kernel on the loop as translated (solve.ts's recheck)
const proven = (l: Loop): boolean => {
  const f = findRank(l, [], {ms: 1500})
  return !!(f.proven && f.checked && f.rank && f.trees && loopObligations(l, f.laws ?? [], f.rank).every(g => f.trees![g.name] && check(g, f.trees![g.name]!)))
}
const halts = (text: string, scc: boolean, withFacts = false): boolean => {
  try {
    const task0 = parseAri(text), task = withFacts ? facts(task0)?.task ?? task0 : task0
    if (!scc) return proven(build(task, 'task').loop)
    const cs = components(task)
    if (!cs.length) return proven(build(task, 'task').loop)
    return cs.every((c, k) => proven(build(c.task, `component ${k}`, {starts: c.starts, slice: true}).loop))
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
    for (const task of [task0, facts(task0)?.task ?? task0]) {
      let l: Loop
      try { l = build(task, f).loop } catch (e) { if (e instanceof Unsupported) continue; throw e }
      const v = findNeverEnds(l, {ms: 1500, cases: true})
      expect([f, v.proven && v.checked]).toEqual([f, false])
    }
  }
}, 240_000)

test('the facts at locations: a parity read as a location, a value fixed after the start as a constant', () => {
  const read = (f: string) => parseAri(readFileSync(`${dir}/${f}`, 'utf8'))
  expect(facts(read('facts_parity_nt.ari'))?.split).toBe(1)
  expect(halts(readFileSync(`${dir}/facts_parity_t.ari`, 'utf8'), false, true)).toBe(true)
  const nt = facts(read('facts_parity_nt.ari'))!.task
  const v = findNeverEnds(build(nt, 'parity').loop, {ms: 4000, cases: true})
  expect(v.proven && v.checked).toBe(true)
  expect(halts(readFileSync(`${dir}/facts_pin.ari`, 'utf8'), false, true)).toBe(true)
}, 60_000)

test('constants past 2^53 are refused, not rounded', () => {
  for (const f of ['n36_float_fold.ari', 'n37_float_fold_var.ari']) expect(() => build(parseAri(readFileSync(`${dir}/${f}`, 'utf8')), f)).toThrow(Unsupported)
})
