// Adversarial ITS programs (adversarial/*.ari, written by the independent check of the ranks, research/verify-ranks
// on verify/ranks): small tasks at the translation's edges (negative values, truncated differences, div and mod,
// repeated or constant arguments, exists, slicing, constants past 2^53 folded). Each that some run never ends
// ("; expect: nonterminating") is never answered terminates: on the task's statement (one loop) and per component
// (scc.ts), the translation refuses it or the search gives no rank the kernel takes. Each terminating one, where it is
// proven, is proven by the kernel as any is.
import {expect, test} from 'bun:test'
import {readFileSync, readdirSync} from 'node:fs'
import {Unsupported, parseAri} from './ari.ts'
import {build} from './translate.ts'
import {components} from './scc.ts'
import {findRank} from '../../core/cycles.ts'
import {check, loopObligations, type Loop} from '../../kernel/kernel.ts'

const dir = `${import.meta.dir}/adversarial`
const files = readdirSync(dir).filter(f => f.endsWith('.ari')).sort()
// proven: a rank, its trees checked again by the kernel on the loop as translated (solve.ts's recheck)
const proven = (l: Loop): boolean => {
  const f = findRank(l, [], {ms: 1500})
  return !!(f.proven && f.checked && f.rank && f.trees && loopObligations(l, f.laws ?? [], f.rank).every(g => f.trees![g.name] && check(g, f.trees![g.name]!)))
}
const halts = (text: string, scc: boolean): boolean => {
  try {
    const task = parseAri(text)
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
    expect([f, halts(text, false), halts(text, true)]).toEqual([f, false, false])
  }
}, 240_000)

test('constants past 2^53 are refused, not rounded', () => {
  for (const f of ['n36_float_fold.ari', 'n37_float_fold_var.ari']) expect(() => build(parseAri(readFileSync(`${dir}/${f}`, 'utf8')), f)).toThrow(Unsupported)
})
