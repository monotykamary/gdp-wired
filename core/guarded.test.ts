// Calls shorter only under a guard (core/data.ts's guardedLaws): a selection sort and a merge sort by halves taken, each
// decrease through a guarded size law and the guard at the call; a remove and a take whose guarded laws hold only where
// the runs reach refused. Apart from data.test.ts: their searches take tens of seconds on one vCPU.
import {expect, test} from 'bun:test'
import {evalX, proveData, showValue} from './data.ts'
import {checkCyclic} from '../kernel/cyclic.ts'
import {List, guardedAdversarial, guardedSorts, msortTD, refusal, ssort} from '../examples/data.ts'

const list = (...xs: number[]): {c: number, f: unknown[]} => xs.reduceRight<{c: number, f: unknown[]}>((t, h) => ({c: 1, f: [h, t]}), {c: 0, f: []})
const run = (call: {x: unknown}, env: Record<string, unknown>) => evalX(call.x as never, new Map(Object.entries(env)) as never, {})

test('a call shorter only under a guard: a selection sort (the item removed is in the list) and a merge sort by halves (two items or more), a decrease through a guarded size law and the guard at the call, every one checked by the kernel', () => {
  for (const [f, guarded] of [[ssort, /^size law under reach_remove_\d\(y0, xs1\): size\(remove\(y0, xs1\)\) \+ 1 <= size\(xs1\)/], [msortTD, /^size law under .*size\((take|drop)\(n0, xs1\)\) \+ 1 <= size\(xs1\)/]] as const) {
    const t = f.fn.termination!
    expect(t.text).toBe('size(xs)')
    for (const o of t.obligations) {
      expect(o.proof?.proven && checkCyclic(o.proof.proof)).toBe(true)
      expect(o.lemmaLaws!.map(q => q.name)).toEqual(expect.arrayContaining(o.lemmas))
    }
    // a guarded law (and the guard at the call, a law over the call's path) read by a decrease: take's at half the
    // length (drop's call needs none: drop at 1 + n of x :: xs unfolds to drop at n of xs)
    expect(t.obligations.some(o => o.lemmas.some(n => guarded.test(n))), f.fn.name).toBe(true)
  }
  for (const mk of Object.values(guardedSorts)) { const v = proveData(mk()); expect(v.proven && v.checked && v.proof?.proven && checkCyclic(v.proof.proof)).toBe(true) }
  expect(showValue(List, run({x: {op: 'call', fn: 'ssort', args: [{op: 'var', name: 'xs'}]}}, {xs: list(3, 1, 2, 1)}) as never)).toBe('cons(1, cons(1, cons(2, cons(3, nil))))')
  expect(showValue(List, run({x: {op: 'call', fn: 'msortTD', args: [{op: 'var', name: 'xs'}]}}, {xs: list(3, 1, 2, 1)}) as never)).toBe('cons(1, cons(1, cons(2, cons(3, nil))))')
}, 120_000)

test('a remove and a take whose guarded size laws hold only where the runs reach: refused, the call not proven to lower the measure', () => {
  for (const [name, mk] of Object.entries(guardedAdversarial)) expect(refusal(mk), name).toMatch(/no measure is proven to fall at every call.*(doesn't lower it|not proven to lower it)/)
}, 240_000)
