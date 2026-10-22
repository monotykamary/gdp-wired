// Cyclic proofs nobody shaped, found by core/cycles.ts: for the suite (`bun examples/cycles.ts`), core/cycles.test.ts
// and research/frontier's cycle track. Each states what is (facts and claims, a loop, a rule and its laws) and nothing a
// proof needs: no rank, no back-edge, no lemma. Each has a broken variant the search must refuse.
//   - claims over functions defined by their equations: McCarthy's 91 (rank 101 − n, back-edges at n + 11 and at
//     f(n + 11)), Ackermann's (m, n) in order, subtractive gcd (x + y), an accumulator and two (g(x, 0) = 2x proven
//     through g(x, a) = a + 2x), three functions in a ring and one read through another (a companion about the other)
//   - loops with no rank: two and three phases ((x, y), (x, y, z)), every other turn (2x − p, with p <= 1), subtractive
//     gcd with no invariant (a + b, with 1 <= a and 1 <= b found)
//   - rules reading functions known by their facts (defined in Lean, say): the lemma the law needs, found and proven
//   - past the linear ranks with coefficients up to 4: an exchange (six tokens for a coin, a coin for five) whose rank
//     11·x + 2·y the exact LP gives, a count up to a square (n·n − i, a rank of degree 2), a triangle (y reset to x as x
//     drops: x·x + y, or (x, y) in order, which the search gives), as claims and loops; a rule reading a function of two
//     arguments (fill(k, j) ≤ k found); liveness with no rank stated ((waiting, items), 2·inbox + outbox found)
import type {C, E, Law, Machine} from '../core/machine.ts'
import type {Cyclic, Fact} from '../kernel/cyclic.ts'
import type {Liveness, Loop} from '../kernel/kernel.ts'
import {type Claim, argsKey, cycleLemmas, findCycles, findLeadsTo, findRank} from '../core/cycles.ts'
import {type Verdict, fn, forall, loop, min, nat, oneOf, proveLeadsTo, proveLoop, proveRule, rule, when, yes} from '../core/dsl.ts'
import {batchLaws, batches} from './liveness.ts'

export type Case = {name: string, facts: Fact[], claims: Claim[]}
const v = (name: string): E => ({op: 'var', name}), k = (value: number): E => ({op: 'const', value})
const add = (a: E, b: E): E => ({op: 'add', a, b}), sub = (a: E, b: E): E => ({op: 'sub', a, b}), mul = (f: number, a: E): E => ({op: 'mul', k: f, a})
const get = (map: string, key: E): E => ({op: 'get', map, key})
const le = (a: E, b: E): C => ({op: '<=', a, b}), lt = (a: E, b: E): C => ({op: '<', a, b}), eq = (a: E, b: E): C => ({op: '=', a, b})
const ite = (c: C, then: E, otherwise: E): E => ({op: 'if', c, then, else: otherwise})
const and = (...xs: C[]): C => ({op: 'and', xs})
const times = (a: E, b: E): E => ({op: 'prod', a, b})
const kk = v('k'), n = v('n'), m = v('m'), x = v('x'), y = v('y'), a = v('a'), b = v('b')

// --- claims over functions defined by their equations ----------------------------------------------------------------

// f(k) = k − 10 above 100, else f(f(k + 11)): every f meeting it is 91 at every n <= 101.
export const mccarthy = (claim = 91): Case => {
  const f = (key: E) => get('f', key)
  return {name: `McCarthy's 91${claim === 91 ? '' : ` (claims ${claim})`}`, facts: [{name: 'f(k) = k − 10 above 100, else f(f(k + 11))', keys: ['k'], holds: eq(f(kk), ite(lt(k(100), kk), sub(kk, k(10)), f(f(add(kk, k(11))))))}],
    claims: [{name: `f(n) = ${claim} for n <= 101`, hyps: [le(n, k(101))], concl: eq(f(n), k(claim))}]}
}
// Ackermann's function, two arguments paired: above its second argument, by (m, n) in order.
export const ackermann = (bug?: 'claims ack(m, n) > n + 1'): Case => {
  const A = (p: E, q: E) => get('ack', argsKey([p, q]))
  return {name: `Ackermann${bug ? ` (${bug})` : ''}`, facts: [{name: 'ack(0, b) = b + 1, ack(a + 1, 0) = ack(a, 1), ack(a + 1, b + 1) = ack(a, ack(a + 1, b))', keys: ['a', 'b'],
    holds: eq(A(a, b), ite(eq(a, k(0)), add(b, k(1)), ite(eq(b, k(0)), A(sub(a, k(1)), k(1)), A(sub(a, k(1)), A(a, sub(b, k(1)))))))}],
  claims: [{name: bug ? 'ack(m, n) > n + 1' : 'ack(m, n) > n', concl: lt(bug ? add(n, k(1)) : n, A(m, n))}]}
}
// gcd by subtraction: at least 1 and at most its first argument, for arguments at least 1 (with y = 0 allowed, the
// equation gcd(x, 0) = gcd(x, 0) holds of any value: no proof).
export const gcd = (bug?: 'drops y >= 1'): Case => {
  const G = (p: E, q: E) => get('gcd', argsKey([p, q])), hyps = [le(k(1), x), ...(bug ? [] : [le(k(1), y)])]
  return {name: `gcd by subtraction${bug ? ` (${bug})` : ''}`, facts: [{name: 'gcd(a, b) = a if a = b, else gcd(a − b, b) if b < a, else gcd(a, b − a)', keys: ['a', 'b'],
    holds: eq(G(a, b), ite(eq(a, b), a, ite(lt(b, a), G(sub(a, b), b), G(a, sub(b, a)))))}],
  claims: [{name: 'gcd(x, y) >= 1', hyps, concl: le(k(1), G(x, y))}, {name: 'gcd(x, y) <= x', hyps, concl: le(G(x, y), x)}]}
}
// A loop as a function with an accumulator: g(k, c) = c at k = 0, else g(k − 1, c + 2). g(x, 0) = 2x needs g(x, a) =
// a + 2x: the induction at x − 1 is about g(x − 1, 2), not g(x − 1, 0).
export const accumulator = (bug?: 'claims 2x + 1'): Case => {
  const g = (p: E, q: E) => get('g', argsKey([p, q])), c = v('c')
  return {name: `an accumulator${bug ? ` (${bug})` : ''}`, facts: [{name: 'g(k, c) = c at k = 0, else g(k − 1, c + 2)', keys: ['k', 'c'], holds: eq(g(kk, c), ite(eq(kk, k(0)), c, g(sub(kk, k(1)), add(c, k(2)))))}],
    claims: [{name: bug ? 'g(x, 0) = 2x + 1' : 'g(x, 0) = 2x', concl: eq(g(x, k(0)), bug ? add(mul(2, x), k(1)) : mul(2, x))}]}
}
// Two accumulators: h(k, a, b) = a + b at k = 0, else h(k − 1, a + 1, b + 2); h(x, 0, 0) = 3x.
export const accumulators = (bug?: 'claims 4x'): Case => {
  const h = (p: E, q: E, r: E) => get('h', argsKey([p, q, r]))
  return {name: `two accumulators${bug ? ` (${bug})` : ''}`, facts: [{name: 'h(k, a, b) = a + b at k = 0, else h(k − 1, a + 1, b + 2)', keys: ['k', 'a', 'b'], holds: eq(h(kk, a, b), ite(eq(kk, k(0)), add(a, b), h(sub(kk, k(1)), add(a, k(1)), add(b, k(2)))))}],
    claims: [{name: bug ? 'h(x, 0, 0) = 4x' : 'h(x, 0, 0) = 3x', concl: eq(h(x, k(0), k(0)), mul(bug ? 4 : 3, x))}]}
}
// Three functions in a ring: a from b, b from c, c from a; a(x) <= x needs what b is (the induction on a alone reads
// b(x − 1), whose bound nothing states).
export const ring = (bug?: 'c steps by 2'): Case => {
  const A = (key: E) => get('a', key), B = (key: E) => get('b', key), Cc = (key: E) => get('c', key)
  return {name: `three functions in a ring${bug ? ` (${bug})` : ''}`, facts: [
    {name: 'a(0) = b(0) = c(0) = 0', keys: [], holds: and(eq(A(k(0)), k(0)), eq(B(k(0)), k(0)), eq(Cc(k(0)), k(0)))},
    {name: `a(k + 1) = b(k) + 1, b(k + 1) = c(k) + 1, c(k + 1) = a(k) + ${bug ? 2 : 1}`, keys: ['k'], holds: and(eq(A(add(kk, k(1))), add(B(kk), k(1))), eq(B(add(kk, k(1))), add(Cc(kk), k(1))), eq(Cc(add(kk, k(1))), add(A(kk), k(bug ? 2 : 1))))},
  ], claims: [{name: 'a(x) <= x', concl: le(A(x), x)}]}
}
// One function read through another at twice its argument: a(k + 1) = b(2k) + 1, b counting by 1 on its own;
// a(x) <= 2x needs what b is (a's induction at x − 1 says something of b(2x − 4), not of b(2x − 2)).
export const readThrough = (bug?: 'b steps by 2'): Case => {
  const A = (key: E) => get('a', key), B = (key: E) => get('b', key)
  return {name: `one function read through another${bug ? ` (${bug})` : ''}`, facts: [
    {name: 'a(0) = b(0) = 0', keys: [], holds: and(eq(A(k(0)), k(0)), eq(B(k(0)), k(0)))},
    {name: `a(k + 1) = b(2k) + 1, b(k + 1) = b(k) + ${bug ? 2 : 1}`, keys: ['k'], holds: and(eq(A(add(kk, k(1))), add(B(mul(2, kk)), k(1))), eq(B(add(kk, k(1))), add(B(kk), k(bug ? 2 : 1))))},
  ], claims: [{name: 'a(x) <= 2x', concl: le(A(x), mul(2, x))}]}
}
// An exchange: six tokens buy a coin, a coin sells for five; ex(x, y) the tokens left once nothing more is traded, at
// most 5. Each trade loses a token, so 11·x + 2·y drops by one on either (no coefficient up to 4 does: a component
// that never rises needs 5·x + y). With the bug a coin sells for six: (1, 0) trades to (0, 6) and back, and the
// equation no longer determines ex there.
export const exchange = (bug?: 'a coin for six'): Case => {
  const X = (p: E, q: E) => get('ex', argsKey([p, q]))
  return {name: `an exchange${bug ? ` (${bug})` : ''}`, facts: [{name: `ex(a, b) = ex(a + 1, b − 6) if 6 <= b, else ex(a − 1, b + ${bug ? 6 : 5}) if a > 0, else b`, keys: ['a', 'b'],
    holds: eq(X(a, b), ite(le(k(6), b), X(add(a, k(1)), sub(b, k(6))), ite(lt(k(0), a), X(sub(a, k(1)), add(b, k(bug ? 6 : 5))), b)))}],
  claims: [{name: 'ex(x, y) <= 5', concl: le(X(x, y), k(5))}]}
}
// Counting up to a square: up(i, n) = up(i + 1, n) while i < n·n, else i; at least n·n, by the rank n·n − i (of degree
// 2: no linear rank bounds i's climb to n·n). With the bug it claims n·n + 1.
export const countUp = (bug?: 'claims n·n + 1'): Case => {
  const U = (p: E, q: E) => get('up', argsKey([p, q])), i = v('i')
  return {name: `counting up to a square${bug ? ` (${bug})` : ''}`, facts: [{name: 'up(a, b) = up(a + 1, b) while a < b·b, else a', keys: ['a', 'b'], holds: eq(U(a, b), ite(lt(a, times(b, b)), U(add(a, k(1)), b), a))}],
    claims: [{name: bug ? 'up(i, n) >= n·n + 1' : 'up(i, n) >= n·n', concl: le(bug ? add(times(n, n), k(1)) : times(n, n), U(i, n))}]}
}
export const claimCases = (): [Case, boolean][] => [
  [mccarthy(), true], [mccarthy(92), false], [ackermann(), true], [ackermann('claims ack(m, n) > n + 1'), false],
  [gcd(), true], [gcd('drops y >= 1'), false], [accumulator(), true], [accumulator('claims 2x + 1'), false],
  [accumulators(), true], [accumulators('claims 4x'), false], [ring(), true], [ring('c steps by 2'), false],
  [readThrough(), true], [readThrough('b steps by 2'), false],
  [exchange(), true], [exchange('a coin for six'), false], [countUp(), true], [countUp('claims n·n + 1'), false],
]

// --- loops with no rank ----------------------------------------------------------------------------------------------

// An inner count y down to 0, then x down by one and y back to N (with the bug, x never drops).
export const phases = (bug?: 'x never drops') => loop(`two phases${bug ? ` (${bug})` : ''}`).params({N: nat, X: nat}).state({x: ({X}) => X, y: ({N}) => N})
  .while(({x, y}) => x.plus(y).gt(0)).body(({x, y, N}) => ({y: when(y.gt(0), y.minus(1), N), x: when(y.gt(0), x, bug ? x : x.minus(1))}))
export const threePhases = (bug?: 'y resets with z') => loop(`three phases${bug ? ` (${bug})` : ''}`).params({N: nat, M: nat, X: nat}).state({x: ({X}) => X, y: ({M}) => M, z: ({N}) => N})
  .while(({x, y, z}) => x.plus(y).plus(z).gt(0))
  .body(({x, y, z, N, M}) => ({z: when(z.gt(0), z.minus(1), N), y: when(z.gt(0), bug ? M : y, when(y.gt(0), y.minus(1), M)), x: when(z.gt(0).or(y.gt(0)), x, x.minus(1))}))
// x drops every other turn, p the turn's parity (with the bug, x drops on neither).
export const everyOther = (bug?: 'x never drops') => loop(`every other turn${bug ? ` (${bug})` : ''}`).params({X: nat}).state({x: ({X}) => X, p: 0})
  .while(({x}) => x.gt(0)).body(({x, p}) => ({p: when(p.eq(0), 1, 0), x: when(p.eq(1).and(bug ? p.eq(0) : p.eq(1)), x.minus(1), x)}))
// gcd by subtraction with no invariant stated: a + b drops only while both stay at least 1 (with the bug, B may be 0).
export const euclid = (bug?: 'B may be 0') => loop(`gcd by subtraction${bug ? ` (${bug})` : ''}`).params({A: nat, B: nat}).state({a: ({A}) => A, b: ({B}) => B})
  .pre(({A, B}) => (bug ? A.atLeast(1) : A.atLeast(1).and(B.atLeast(1))))
  .while(({a, b}) => a.ne(b)).body(({a, b}) => ({a: when(a.gt(b), a.minus(b), a), b: when(b.gt(a), b.minus(a), b)}))
// A triangle: y counts down, then x drops and y starts again from x; x·x + y drops on every turn, and so does (x, y) in
// order, which is linear (with the bug, x never drops).
export const triangle = (bug?: 'x never drops') => loop(`a triangle${bug ? ` (${bug})` : ''}`).params({X: nat}).state({x: ({X}) => X, y: ({X}) => X})
  .while(({x, y}) => x.plus(y).gt(0)).body(({x, y}) => ({y: when(y.gt(0), y.minus(1), bug ? x : x.minus(1)), x: when(y.gt(0), x, bug ? x : x.minus(1))}))
// The exchange as a loop: x coins, y tokens; six tokens buy a coin, else a coin sells for five (with the bug, six).
export const exchangeLoop = (bug?: 'a coin for six') => loop(`an exchange${bug ? ` (${bug})` : ''}`).params({X: nat, Y: nat}).state({x: ({X}) => X, y: ({Y}) => Y})
  .while(({x, y}) => x.gt(0).or(y.atLeast(6))).body(({x, y}) => ({y: when(y.atLeast(6), y.minus(6), y.plus(bug ? 6 : 5)), x: when(y.atLeast(6), x.plus(1), x.minus(1))}))
// Counting up to N·M: the rank M·N − (i + 1), of degree 2 (with the bug, the count stops at N).
export const toProduct = (bug?: 'stops at N') => loop(`counting up to a product${bug ? ` (${bug})` : ''}`).params({N: nat, M: nat}).state({i: 0})
  .while(({i, N, M}) => i.lt(N.mul(M))).body(({i, N}) => ({i: bug ? when(i.lt(N), i.plus(1), i) : i.plus(1)}))
export type LoopCase = Parameters<typeof proveLoop>[0]
export const loopCases = (): [LoopCase, boolean][] => [
  [phases(), true], [phases('x never drops'), false], [threePhases(), true], [threePhases('y resets with z'), false],
  [everyOther(), true], [everyOther('x never drops'), false], [euclid(), true], [euclid('B may be 0'), false],
  [triangle(), true], [triangle('x never drops'), false], [exchangeLoop(), true], [exchangeLoop('a coin for six'), false],
  [toProduct(), true], [toProduct('stops at N'), false],
] as never

// --- rules reading functions known by their facts --------------------------------------------------------------------

// McCarthy's function, defined elsewhere (its JavaScript the closed form the runtimes call): the output is 91 for every
// n <= 101 (with the bug, n up to 102, where it is 92).
export const ninetyOne = (bug?: 'reads n up to 102') => {
  const r = rule(`ninety-one${bug ? ` (${bug})` : ''}`).inputs({n: nat}).state({out: 91})
    .fns({f: fn(1, 'k => k > 100 ? k - 10 : 91', {facts: f => ({'f(k) = k − 10 above 100, else f(f(k + 11))': forall(q => f(q).eq(when(q.gt(100), q.minus(10), f(f(q.plus(11))))))})})})
    .assume(({n}) => n.atMost(bug ? 102 : 101))
    .step(({n, f}) => ({out: f(n)}))
  return {r, laws: [r.law('the output is 91', ({out}) => out.eq(91))]}
}
// A function given by its recurrence's facts alone (as Lean defines it): the value kept is twice the count (with the
// bug, read one ahead).
export const doubling = (bug?: 'reads one ahead') => {
  const r = rule(`doubling${bug ? ` (${bug})` : ''}`).inputs({}).state({count: 0, value: 0})
    .fns({twice: fn(1, 'k => 2 * k', {facts: f => ({'twice 0 = 0': f(0).eq(0), 'twice (k + 1) = twice k + 2': forall(q => f(q.plus(1)).eq(f(q).plus(2)))})})})
    .step(({count, twice}) => ({count: count.plus(1), value: twice(count.plus(bug ? 2 : 1))}))
  return {r, laws: [r.law('the value is twice the count', ({value, count}) => value.eq(count.times(2)))]}
}
// A function of two arguments known by its equation (fill(k, c): k steps of one, capped at c): the level kept is at
// most the steps, by the lemma fill(k, j) ≤ k (with the bug, read one step ahead).
export const cappedFill = (bug?: 'reads one ahead') => {
  const r = rule(`capped fill${bug ? ` (${bug})` : ''}`).params({cap: nat}).inputs({}).state({n: 0, level: 0})
    .fns({fill: fn(2, (q: number, c: number) => Math.min(q, c), {facts: f => ({'fill(k, c) = 0 at k = 0, else min(fill(k − 1, c) + 1, c)': forall((q, c) => f(q, c).eq(when(q.eq(0), 0, min(f(q.minus(1), c).plus(1), c))))})})})
    .step(({n, cap, fill}) => ({n: n.plus(1), level: fill(n.plus(bug ? 2 : 1), cap)}))
  return {r, laws: [r.law('the level is at most the steps', ({level, n}) => level.atMost(n))]}
}
export type RuleCase = {r: Parameters<typeof proveRule>[0], laws: Law[]}
export const ruleCases = (): [RuleCase, boolean][] => [[ninetyOne(), true], [ninetyOne('reads n up to 102'), false], [doubling(), true], [doubling('reads one ahead'), false],
  [cappedFill(), true], [cappedFill('reads one ahead'), false]] as never

// --- liveness with no rank ---------------------------------------------------------------------------------------------

// examples/liveness.ts's batches with its rank left out: (waiting, items) in order, found (with the bug, work stalls on
// the last item). A pipeline: `move` takes a job from the inbox to the outbox, `ship` ships one; every job ships, by
// 2·inbox + outbox (a move keeps inbox + outbox; with the bug, ship waits for two in the outbox).
export const pipeline = (bug?: 'ships only with two waiting') => rule(`pipeline${bug ? ` (${bug})` : ''}`).params({N: nat}).inputs({op: oneOf('move', 'ship')}).state({inbox: ({N}) => N, outbox: 0})
  .flags(({op, inbox, outbox}) => ({moving: op.is('move').and(inbox.gt(0)), shipping: op.is('ship').and(bug ? outbox.gt(1) : outbox.gt(0))}))
  .step(({inbox, outbox, moving, shipping}) => ({inbox: when(moving, inbox.minus(1), inbox), outbox: when(moving, outbox.plus(1), when(shipping, outbox.minus(1), outbox))}))
export type LiveCase = {name: string, r: Parameters<typeof proveLeadsTo>[0], laws: Law[], live: Liveness}
// The rank (and invariants) findLeadsTo finds for a case, as proveLeadsTo calls it.
export const findLive = (c: LiveCase) => {
  const laws = [...c.r.kindLaws().filter(k => !c.laws.some(l => l.name === k.name)), ...c.laws]
  const out = findLeadsTo(c.r.machine, laws, c.live, {params: (rand, bound) => c.r.randomParams(rand, bound), input: (rand, bound, ps) => c.r.randomInput(rand, bound, ps)})
  return out.proven && out.checked && out.rank ? {rank: out.rank, laws: [...laws, ...(out.laws ?? [])]} : undefined
}
export const liveCases = (): [LiveCase, boolean][] => {
  const out: [LiveCase, boolean][] = []
  for (const bug of [undefined, 'stalls on the last item'] as const) {
    const r = batches(bug)
    out.push([{name: `batches${bug ? ` (${bug})` : ''}`, r: r as never, laws: batchLaws(r), live: r.leadsTo('every batch gets done', {from: () => yes, to: ({waiting, items}) => waiting.eq(0).and(items.eq(0)),
      helpful: [{when: ({items}) => items.gt(0), request: () => ({op: 1})}, {when: ({items}) => items.eq(0), request: () => ({op: 0})}]})}, !bug])
  }
  for (const bug of [undefined, 'ships only with two waiting'] as const) {
    const r = pipeline(bug)
    out.push([{name: r.machine.name, r: r as never, laws: [], live: r.leadsTo('every job ships', {from: () => yes, to: ({inbox, outbox}) => inbox.eq(0).and(outbox.eq(0)),
      helpful: [{when: ({outbox}) => outbox.gt(0), request: () => ({op: 1})}, {when: ({outbox}) => outbox.eq(0), request: () => ({op: 0})}]})}, !bug])
  }
  return out
}

const foundText = (f: Verdict['found']) => [...(f?.rank ? [`rank ${f.rank}`] : []), ...(f?.laws ?? []).map(l => l.text), ...(f?.facts ?? [])].join('; ')
const shown = (v: Verdict) => (v.proven && v.checked ? `proven${v.found ? ` (${foundText(v.found)})` : ''}` : `refused${v.goal ? ` at ${v.goal}` : ''}`)
if (import.meta.main) {
  let failed = 0
  const report = (name: string, want: boolean, v: Verdict, ms: number) => {
    const ok = (v.proven && v.checked) === want
    if (!ok) failed++
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${name}: ${shown(v)} (${Math.round(ms)} ms)`)
  }
  for (const [c, want] of claimCases()) {
    const t = performance.now(), out = findCycles(c.facts, c.claims)
    report(c.name, want, {proven: out.proven, checked: out.checked, ...(out.found ? {found: {rank: Object.values(out.found.ranks).join(' '), facts: out.found.companions}} : {}), ...(out.goal ? {goal: out.goal} : {})}, performance.now() - t)
  }
  for (const [l, want] of loopCases()) { const t = performance.now(), out = proveLoop(l, []); report(l.loop.name, want, out, performance.now() - t) }
  for (const [{r, laws}, want] of ruleCases()) { const t = performance.now(), out = proveRule(r, laws); report(r.machine.name, want, out, performance.now() - t) }
  for (const [c, want] of liveCases()) { const t = performance.now(), out = proveLeadsTo(c.r, c.laws, c.live); report(`${c.name}: ${c.live.name}`, want, out, performance.now() - t) }
  if (failed) process.exit(1)
}

// The proofs found, for the Lean export (lean-kernel/package-check.ts, the suite's lean-cycles job): each cyclic proof
// through Cyclic.lean's cyclic_sound, each loop's halting with its rank and laws found through Live.lean, each rule's
// laws with its lemmas (stated as the hypotheses they are there) and the lemmas' own cyclic proof.
export function leanItems(): ({id: string, cyclic: Cyclic} | {id: string, loop: Loop, rank: E[], laws: Law[]} | {id: string, machine: Machine, laws: Law[]} | {id: string, machine: Machine, laws: Law[], liveness: Liveness[]})[] {
  const ids = ['cycmc91', '', 'cycack', '', 'cycgcd', '', 'cycacc', '', 'cycacc2', '', 'cycring', '', 'cycthrough', '', 'cycexchange', '', 'cycsquare', '']
  const loops = ['loopphases', '', 'loopphases3', '', 'loopother', '', 'loopeuclid', '', 'looptriangle', '', 'loopexchange', '', 'loopproduct', '']
  const rules = ['rule91', '', 'ruledouble', '', 'rulefill', '']
  const lives = ['livebatches', '', 'livepipeline', '']
  const fail = (what: string): never => { throw new Error(`${what}: not proven`) }
  return [
    ...claimCases().flatMap(([c], i) => (ids[i] ? [{id: ids[i]!, cyclic: findCycles(c.facts, c.claims).proof ?? fail(c.name)}] : [])),
    ...loopCases().flatMap(([l], i) => {
      if (!loops[i]) return []
      const out = findRank(l.loop, [])
      return out.proven && out.rank ? [{id: loops[i]!, loop: l.loop, rank: out.rank, laws: out.laws ?? []}] : fail(l.loop.name)
    }),
    ...ruleCases().flatMap(([{r, laws}], i) => {
      if (!rules[i]) return []
      const out = cycleLemmas(r.machine, laws)
      return out.proven && out.machine && out.proof ? [{id: rules[i]!, machine: out.machine, laws}, {id: `${rules[i]}lemma`, cyclic: out.proof}] : fail(r.machine.name)
    }),
    // Each liveness with the rank found (and its invariants as laws), exported as a stated one is.
    ...liveCases().flatMap(([c], i) => {
      if (!lives[i]) return []
      const found = findLive(c)
      return found ? [{id: lives[i]!, machine: c.r.machine, laws: found.laws, liveness: [{...c.live, rank: found.rank}]}] : fail(c.name)
    }),
  ]
}
