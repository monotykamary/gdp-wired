// Runs that never end (core/nonterm.ts, kernel.ts's checkRecur): the examples' loops proven to have one, their twins
// proven to halt and not to have one; no loop proven both ways (NonTerm.lean's halts_not_never_ends says none can be);
// the certificates exported for Lean. The tampered certificates are core/conformance.test.ts's.
import {expect, test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {join} from 'node:path'
import {loop, nat, proveLoop, proveNeverEnds, yes} from './dsl.ts'
import {findNeverEnds} from './nonterm.ts'
import {checkRecur, loopObligations} from '../kernel/kernel.ts'
import {findRank} from './cycles.ts'
import {toLean} from '../lean-kernel/emit.ts'
import {pagesMayBeEmpty, pagesNonEmpty, retryCapped, retryForever, ringReader, sweepOnce} from '../examples/nonterm.ts'
import {parseAri} from '../compare/term/ari.ts'
import {build} from '../compare/term/translate.ts'

const climb = loop('climb').params({n: nat}).state({x: ({n}) => n}).while(({x}) => x.atLeast(1)).body(({x}) => ({x: x.plus(1)}))
const countdown = loop('countdown').params({n: nat}).state({x: ({n}) => n}).while(({x}) => x.atLeast(1)).body(({x}) => ({x: x.minus(1)})).rank(({x}) => x)
const mayStall = loop('may stall').params({n: nat}).inputs({w: nat}).state({x: ({n}) => n}).assume(({w}) => w.atMost(1))
  .while(({x}) => x.atLeast(1)).body(({x, w}) => ({x: x.minus(w)}))
const spin = loop('spin').state({x: 0}).while(() => yes).body(({x}) => ({x}))
const task = (file: string) => build(parseAri(readFileSync(join(import.meta.dir, '../research/frontier2/tasks', file), 'utf8')), file).loop

test('the examples: each never-ending loop proven so, its twin proven to halt and not to', () => {
  type L = Parameters<typeof proveLoop>[0]
  for (const l of [pagesMayBeEmpty, retryForever, ringReader, climb, mayStall, spin] as L[]) {
    const v = proveNeverEnds(l, {ms: 5000})
    expect(v.proven && v.checked, l.loop.name).toBe(true)
    expect(checkRecur(v.loop!, v.recur!)).toBe(true)
  }
  for (const l of [pagesNonEmpty, retryCapped, sweepOnce, countdown] as L[]) {
    expect(proveNeverEnds(l, {ms: 1000}).proven, l.loop.name).toBe(false)
    const h = proveLoop(l, [])
    expect(h.proven && h.checked, l.loop.name).toBe(true)
  }
  // `from`: among the params where it holds. Where the loop doesn't run at all, no run of it goes on.
  expect(proveNeverEnds(mayStall, {ms: 1000, from: ({n}) => n.atMost(0)}).proven).toBe(false)
  expect(proveNeverEnds(mayStall, {ms: 5000, from: ({n}) => n.atLeast(5)}).proven).toBe(true)
}, 120_000)

// A loop proven to halt (a rank the kernel checked) and a certificate that some run never ends would contradict each
// other (NonTerm.lean's halts_not_never_ends): on loops of both kinds and their twins, never both.
test('no loop is proven both to halt and to have a run that never ends', () => {
  const halting = [countdown.loop, pagesNonEmpty.loop, retryCapped.loop, sweepOnce.loop], never = [climb.loop, mayStall.loop, spin.loop, pagesMayBeEmpty.loop, retryForever.loop, ringReader.loop]
  const tasks = ['its/toy2.t2.ari', 'its/toy2.t2.broken.ari', 'its/Choose.jar-obl-8.ari', 'its/Choose.jar-obl-8.broken.ari', 'its/NO_10.jar-obl-8.ari', 'its/NO_10.jar-obl-8.broken.ari'].map(task)
  for (const l of [...halting, ...never, ...tasks]) {
    const r = findRank(l, [], {ms: 4000})
    const h = !!(r.proven && r.checked && r.rank && r.trees && loopObligations(l, r.laws ?? [], r.rank).length)
    const n = findNeverEnds(l, {ms: 3000})
    expect(h && n.proven && n.checked, l.name).toBe(false)
    if (halting.includes(l)) expect(h, `${l.name} halts`).toBe(true)
    // (the tasks' originals: LoAT answers NO on each; their twins terminate)
    if (never.includes(l) || (tasks.includes(l) && !l.name.includes('broken'))) expect(n.proven && n.checked, `${l.name} never ends`).toBe(true)
  }
}, 300_000)

test('a certificate goes to Lean as Kern.never_ends_of, its tampered twins as checks computed to false', () => {
  const v = proveNeverEnds(climb, {ms: 5000})
  const text = toLean([{id: 'climb', neverEnds: v.loop!, recur: v.recur!, tampered: [{what: 'the set every state', recur: {...v.recur!, set: {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}}}]}])
  expect(text).toContain('import NonTerm')
  expect(text).toContain('theorem climb_never_ends : NeverEnds climb_loop :=')
  expect(text).toContain('example : checkRecur climb_loop climb_tampered0 = false')
})
