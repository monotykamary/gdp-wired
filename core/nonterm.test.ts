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

// Accelerated cycles (core/accel.ts): sets from the relation's cycles, stems from runs with their loops taken n times at
// once. Each task here is LoAT's NO with no lasso and no fitted set at 0.23.0; its twin terminates, and isn't proven
// never to end.
const ari = (name: string, rules: string) => build(parseAri(`(format LCTRS)\n(theory Ints)\n${['l0', 'l1', 'l2'].map(f => `(fun ${f} (-> Int Int))`).join('\n')}\n(entrypoint l0)\n${rules}`), name).loop
// x alternates sign and grows: x > 0 gives −x − 1, x < 0 gives −x + 1 (two turns: x + 2); the set x ≠ 0 at l1 is no
// conjunction. The twin's |x| falls by one each turn.
const alternate = ari('alternate', '(rule (l0 x0) (l1 x0))\n(rule (l1 x0) (l1 y0) :guard (and (> x0 0) (= y0 (- (- 0 x0) 1))))\n(rule (l1 x0) (l1 y0) :guard (and (< x0 0) (= y0 (+ (- 0 x0) 1))))')
const alternateTwin = ari('alternate, falling', '(rule (l0 x0) (l1 x0))\n(rule (l1 x0) (l1 y0) :guard (and (> x0 0) (= y0 (+ (- 0 x0) 1))))\n(rule (l1 x0) (l1 y0) :guard (and (< x0 0) (= y0 (- (- 0 x0) 1))))')
// a value chosen each turn: x' free with x' >= 0, and the loop runs while x = 14 (the choice 14, a model's constant)
const choose = ari('choose 14', '(rule (l0 x0) (l1 x0))\n(rule (l1 x0) (l1 y0) :guard (and (= x0 14) (>= y0 0)))')
const chooseTwin = ari('choose 14, then below', '(rule (l0 x0) (l1 x0))\n(rule (l1 x0) (l1 y0) :guard (and (= x0 14) (>= y0 0) (< y0 14)))')
// a stem of 5,000 turns: x counts from 0 to 5,000 at l1, then climbs at l2 for ever (a random run, or a bounded one of
// 24 turns, never gets there); the twin climbs down at l2 instead.
const longStem = ari('a long stem', '(rule (l0 x0) (l1 y0) :guard (= y0 0))\n(rule (l1 x0) (l1 y0) :guard (and (< x0 5000) (= y0 (+ x0 1))))\n(rule (l1 x0) (l2 x0) :guard (>= x0 5000))\n(rule (l2 x0) (l2 y0) :guard (and (>= x0 5000) (= y0 (+ x0 1))))')
const longStemTwin = ari('a long stem, then down', '(rule (l0 x0) (l1 y0) :guard (= y0 0))\n(rule (l1 x0) (l1 y0) :guard (and (< x0 5000) (= y0 (+ x0 1))))\n(rule (l1 x0) (l2 x0) :guard (>= x0 5000))\n(rule (l2 x0) (l2 y0) :guard (and (>= x0 5000) (= y0 (- x0 1))))')

// Two values (l0 to l2 of two arguments).
const ari2 = (name: string, rules: string) => build(parseAri(`(format LCTRS)\n(theory Ints)\n${['l0', 'l1', 'l2'].map(f => `(fun ${f} (-> Int Int Int))`).join('\n')}\n(entrypoint l0)\n${rules}`), name).loop
// a product: y := (x + 1)² while y > 9, x counting up (Velroyen08-complInterv's): the set needs x ≥ 4, a bound on the
// product's factor, and the product's facts to keep y > 9. The twin squares x and counts y down.
const square = ari2('a square', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l1 y0 y1) :guard (and (> x1 9) (> x0 (- 1)) (= y0 (+ x0 1)) (= y1 (* (+ x0 1) (+ x0 1)))))')
const squareTwin = ari2('a square, counting down', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l1 y0 y1) :guard (and (> x1 9) (> x0 (- 1)) (= y0 (* x0 x0)) (= y1 (- x1 1))))')
// an inner loop: y counts from 0 to 12 at l2 for each turn of x at l1 (KnapsackDP's), twelve choices of a path at l2 in
// each round, past the six the cycles are enumerated to; the twin's x stops at 100.
const inner = ari2('an inner loop', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l2 x0 y1) :guard (= y1 0))\n(rule (l2 x0 x1) (l2 x0 y1) :guard (and (< x1 12) (= y1 (+ x1 1))))\n(rule (l2 x0 x1) (l1 y0 x1) :guard (and (>= x1 12) (= y0 (+ x0 1))))')
const innerTwin = ari2('an inner loop, x below 100', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l2 x0 y1) :guard (= y1 0))\n(rule (l2 x0 x1) (l2 x0 y1) :guard (and (< x1 12) (= y1 (+ x1 1))))\n(rule (l2 x0 x1) (l1 y0 x1) :guard (and (>= x1 12) (< x0 100) (= y0 (+ x0 1))))')

test('accelerated cycles with a product and with an inner loop: each found and checked, its twin halting and not found', () => {
  for (const l of [square, inner]) {
    const n = findNeverEnds(l, {ms: 8000})
    expect(n.proven && n.checked, l.name).toBe(true)
    expect(n.by, l.name).toBe('accelerated')
    expect(checkRecur(l, n.recur!), l.name).toBe(true)
  }
  for (const l of [squareTwin, innerTwin]) {
    expect(findNeverEnds(l, {ms: 2000}).proven, l.name).toBe(false)
    const r = findRank(l, [], {ms: 8000})
    expect(r.proven && r.checked, `${l.name} halts`).toBe(true)
  }
}, 120_000)

test('accelerated cycles: each found and checked, its twin halting and not found', () => {
  for (const l of [alternate, choose, longStem]) {
    const n = findNeverEnds(l, {ms: 4000})
    expect(n.proven && n.checked, l.name).toBe(true)
    expect(n.by, l.name).toBe('accelerated')
    expect(checkRecur(l, n.recur!), l.name).toBe(true)
  }
  expect(findNeverEnds(longStem, {ms: 4000}).recur!.stem.length).toBeGreaterThan(5000)
  for (const l of [alternateTwin, chooseTwin, longStemTwin]) {
    expect(findNeverEnds(l, {ms: 2000}).proven, l.name).toBe(false)
    const r = findRank(l, [], {ms: 4000})
    expect(r.proven && r.checked, `${l.name} halts`).toBe(true)
  }
  // without the stage, none of the three (the lassos, policies and fitted sets miss them)
  for (const l of [alternate, longStem]) expect(findNeverEnds(l, {ms: 2000, accel: 0}).proven, l.name).toBe(false)
}, 120_000)

// The closed forms' engine (core/accel.ts): inner loops taken to their end by their metering function, products with a
// turn's input in the cases that fix the state value, stems found by deepening. Each a loop with no lasso, found by the
// accelerated stage (at 0.26.0 the first two by a fitted set only, the third not at all); its twin isn't proven never to
// end, and the first two twins are proven to halt.
const ariN = (name: string, n: number, k: number, rules: string) => build(parseAri(`(format LCTRS)\n(theory Ints)\n${Array.from({length: n}, (_, i) => `(fun l${i} (-> ${'Int '.repeat(k)}Int))`).join('\n')}\n(entrypoint l0)\n${rules}`), name).loop
// y counts from 0 to x at l2 for each turn of x at l1 (MysteriousProgram's display loop): the inner loop's count x grows
// with every round, which no cycle of bounded turns takes; the twin's x stops at 100.
const toX = ari2('an inner loop to x', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l2 x0 y1) :guard (= y1 0))\n(rule (l2 x0 x1) (l2 x0 y1) :guard (and (< x1 x0) (= y1 (+ x1 1))))\n(rule (l2 x0 x1) (l1 y0 x1) :guard (and (>= x1 x0) (= y0 (+ x0 1))))')
const toXTwin = ari2('an inner loop to x, x below 100', '(rule (l0 x0 x1) (l1 x0 x1))\n(rule (l1 x0 x1) (l2 x0 y1) :guard (= y1 0))\n(rule (l2 x0 x1) (l2 x0 y1) :guard (and (< x1 x0) (= y1 (+ x1 1))))\n(rule (l2 x0 x1) (l1 y0 x1) :guard (and (>= x1 x0) (< x0 100) (= y0 (+ x0 1))))')
// the next y a choice with x·y' = y (RandomHard's arg2 = arg3·x): linear at x = 1, where y' = y, z counting up; the
// twin's z stops at 50
const byChoice = ariN('a product with a choice', 2, 3, '(rule (l0 x0 x1 x2) (l1 x0 x1 x2))\n(rule (l1 x0 x1 x2) (l1 x0 y1 y2) :guard (and (> x1 0) (= x1 (* x0 y1)) (= y2 (+ x2 1))))')
const byChoiceTwin = ariN('a product with a choice, z below 50', 2, 3, '(rule (l0 x0 x1 x2) (l1 x0 x1 x2))\n(rule (l1 x0 x1 x2) (l1 x0 y1 y2) :guard (and (> x1 0) (< x2 50) (= x1 (* x0 y1)) (= y2 (+ x2 1))))')
// the climb at l29 is open once a side chain of 27 turns, each a value the guard pins by two bounds, has set f (fun9's
// stem of 30 turns): past the stems' depth of 8 and a bounded run's 24; the twin's climb stops at 100
const side = (stop: string) => ariN(`a side chain${stop ? ', then down' : ''}`, 30, 2, ['(rule (l0 x0 x1) (l1 x0 y1) :guard (= y1 0))', '(rule (l1 x0 x1) (l29 x0 x1) :guard (= x1 1))',
  '(rule (l1 x0 x1) (l2 y0 x1) :guard (and (= x1 0) (> y0 x0) (< y0 (+ x0 2))))', ...Array.from({length: 26}, (_, i) => `(rule (l${i + 2} x0 x1) (l${i + 3} y0 x1) :guard (and (> y0 x0) (< y0 (+ x0 2))))`),
  '(rule (l28 x0 x1) (l1 x0 y1) :guard (= y1 1))', `(rule (l29 x0 x1) (l29 y0 x1) :guard (and ${stop} (= y0 (+ x0 1))))`].join('\n'))

test('closed forms: an inner loop to its end, a product fixed by a case, a stem by deepening; each twin not found', () => {
  for (const l of [toX, byChoice, side('')]) {
    const n = findNeverEnds(l, {ms: 8000})
    expect(n.proven && n.checked, l.name).toBe(true)
    expect(n.by, l.name).toBe('accelerated')
    expect(checkRecur(l, n.recur!), l.name).toBe(true)
  }
  expect(findNeverEnds(side(''), {ms: 8000}).recur!.stem.length).toBeGreaterThanOrEqual(30)
  for (const l of [toXTwin, byChoiceTwin, side('(< x0 100)')]) expect(findNeverEnds(l, {ms: 2000}).proven, l.name).toBe(false)
  for (const l of [toXTwin, byChoiceTwin]) { const r = findRank(l, [], {ms: 8000}); expect(r.proven && r.checked, `${l.name} halts`).toBe(true) }
}, 120_000)
