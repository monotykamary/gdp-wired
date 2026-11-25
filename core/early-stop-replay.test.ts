import {expect, test} from 'bun:test'
import {type Term, all, bool, everyKey, fn, forall, nat, no, oneOf, proveRule, replayRefutation, replayVerifiedRefutation, rule, sizedSort, when, yes} from './dsl.ts'
import {selectorReads, smallOf, smallOfChecked} from './exists.ts'
import {seeded} from './machine.ts'

const rel = bool.from(false)

const majorityRule = (broken: boolean) => rule('quorum demo')
  .params({size: nat}).sorts('Node')
  .inputs({op: oneOf('vote', 'elect'), i: nat, j: nat}).carries('Q')
  .counts({members: ({Q, size}) => ({below: size, body: (_x, k) => Q.has(k)})})
  .assume(({op, i, j, size, Q, members}) => all(
    sizedSort('Node', size).has(i),
    sizedSort('Node', size).has(j),
    op.is('elect').implies(all(
      everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(size)))),
      size.lt(members.at(0).times(2)),
    )),
  ))
  .maps({Leader: rel, Voted: 0})
  .flags(({i, Q, Voted}) => ({allVoted: everyKey(k => Q.has(k).implies(Voted.at(k).eq(i.plus(1))))}))
  .flags(({op, i, allVoted, Voted}) => ({
    votes: op.is('vote').and(broken ? yes : Voted.at(i).eq(0)),
    elects: op.is('elect').and(allVoted),
  }))
  .step(({i, j, votes, elects, Leader, Voted}) => ({
    Voted: Voted.set(i, when(votes, j.plus(1), Voted.at(i))),
    Leader: Leader.set(i, when(elects, yes, Leader.at(i))),
  }))

test('smallOfChecked stops early with replay-verified trace without poisoning smalls cache', () => {
  const r = majorityRule(true), m = r.machine
  const badLaw = r.law('one leader', ({size, Leader}) =>
    forall((a, b) => all(sizedSort('Node', size).has(a), sizedSort('Node', size).has(b), Leader.at(a), Leader.at(b)).implies(a.eq(b))))
  const intactLaw = r.law('voted stays within size', ({size, Voted}) => forall(a => Voted.at(a).atMost(size)))

  const hit = smallOfChecked(m, {laws: [badLaw]})
  expect(hit.violation).toBeDefined()
  expect(hit.checkedAll).toBe(false)
  expect(hit.violation!.trace.length).toBeGreaterThan(0)
  expect(replayRefutation(r, [badLaw], [], hit.violation!.params, hit.violation!.trace, 4, badLaw)).toBe(true)

  // A partial early-stopped run must not be cached into `smalls`: an intact law afterward still sees the full graph.
  const full = smallOfChecked(m, {laws: [intactLaw]})
  expect(full.violation).toBeUndefined()
  expect(full.checkedAll).toBe(true)
  expect(full.samples).toBe(smallOf(m))
  expect(full.samples!.some(s => s.sts.length > hit.violation!.trace.length)).toBe(true)
})

test('proveRule refutes broken counted quorum via replayRefutation and proves intact control', () => {
  const broken = majorityRule(true)
  const brokenLaw = broken.law('one leader', ({size, Leader}) =>
    forall((a, b) => all(sizedSort('Node', size).has(a), sizedSort('Node', size).has(b), Leader.at(a), Leader.at(b)).implies(a.eq(b))))
  const ref = proveRule(broken, [brokenLaw], {search: {ms: 5000}})
  expect(ref.proven).toBe(false)
  expect(ref.run).toBeDefined()
  expect(ref.run!.trace.length).toBeGreaterThan(0)

  const intact = majorityRule(false)
  const intactLaw = intact.law('one leader', ({size, Leader}) =>
    forall((a, b) => all(sizedSort('Node', size).has(a), sizedSort('Node', size).has(b), Leader.at(a), Leader.at(b)).implies(a.eq(b))))
  const ok = proveRule(intact, [intactLaw], {search: {ms: 10000}})
  expect(ok.proven).toBe(true)
  expect(ok.checked).toBe(true)
  expect(ok.run).toBeUndefined()
})

test('selectorReads collapses inactive inputs and 0/1 map no-op writes', () => {
  const r = majorityRule(false)
  const sr = selectorReads(r.machine, [])
  expect(sr).toBeDefined()
  expect(sr!.selector).toBe('op')
  // op=0 ('vote') only writes Voted[i] using j; it does not read Q.
  expect([...sr!.readsFor(0)].sort()).toEqual(['i', 'j', 'op'])
  // op=1 ('elect') reads i and Q via allVoted; it does not read j.
  expect([...sr!.readsFor(1)].sort()).toEqual(['Q', 'i', 'op'])
})

test('Rule.randomInput bounds carried map keys by count and assume param limits', () => {
  const r = majorityRule(false)
  const rand = seeded(17)
  for (let t = 0; t < 40; t++) {
    const req = r.randomInput(rand, 8, {size: 2})
    const q = req.Q as Map<number, number>
    expect(q).toBeInstanceOf(Map)
    for (const key of q.keys()) expect(key).toBeLessThan(2)
  }
})

test('inferLaws early-stop catches radix-key uninterpreted-fn mutant and leaves intact control unrefuted', () => {
  const N = 64
  const pk = (a: Term, b: Term) => a.times(N).plus(b)
  const idn = fn(1, (x: number) => x ^ 5, {facts: f => ({'idn is injective': forall((a, b) => f(a).eq(f(b)).implies(a.eq(b)))})})
  const makeRing = (broken: boolean) => rule('mini ring')
    .params({size: nat}).pre(({size}) => size.atLeast(2).and(size.atMost(N)))
    .inputs({op: oneOf('send', 'recv', 'elect'), n: nat, n1: nat, m: nat})
    .assume(({n, n1, size}) => n.lt(size).and(n1.lt(size)))
    .fns({idn})
    .maps({Pending: rel, Leader: rel})
    .flags(({op, n, n1, m, size, idn, Pending}) => {
      const next = n1.eq(when(n.plus(1).eq(size), 0, n.plus(1)))
      return {
        sends: op.is('send').and(next),
        recvs: op.is('recv').and(next, Pending.at(pk(m, n)), broken ? yes : idn(n).atMost(m)),
        leads: op.is('elect').and(Pending.at(pk(idn(n), n))),
      }
    })
    .step(({n, n1, m, idn, sends, recvs, leads, Pending, Leader}) => ({
      Pending: Pending.each(k => when(sends.and(k.eq(pk(idn(n), n1))).or(recvs.and(k.eq(pk(m, n1)))), yes, Pending.at(k))),
      Leader: Leader.set(n, when(leads, yes, Leader.at(n))),
    }))

  const broken = makeRing(true)
  const brokenLaw = broken.law('one leader', ({size, Leader}) =>
    forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))
  const ref = proveRule(broken, [brokenLaw], {search: {ms: 10000}})
  expect(ref.proven).toBe(false)
  expect(ref.run).toBeDefined()
  expect(ref.run!.trace.length).toBeGreaterThan(0)

  const intact = makeRing(false)
  const intactLaw = intact.law('one leader', ({size, Leader}) =>
    forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))
  const ok = proveRule(intact, [intactLaw], {search: {ms: 1500}})
  expect(ok.run).toBeUndefined()
}, 15_000)

test('inferLaws early-stop catches relational mutant and proves intact control', () => {
  const makeGate = (broken: boolean) => rule('mini token')
    .params({clients: nat, servers: nat}).sorts('Client', 'Server')
    .inputs({op: oneOf('grant', 'release'), c: nat, s: nat})
    .assume(({clients, servers, c, s}) => all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s)))
    .maps({Free: bool.from(true)})
    .relations({Held: ['Client', 'Server']})
    .flags(({op, c, s, Free, Held}) => ({
      grants: op.is('grant').and(broken ? yes : Free.at(s)),
      releases: op.is('release').and(Held.has(c, s)),
    }))
    .step(({c, s, grants, releases, Free, Held}) => ({
      Free: Free.set(s, when(grants, no, when(releases, yes, Free.at(s)))),
      Held: {...Held.add([c, s]), value: when(grants, 1, when(releases, 0, Held.at(c, s))).e},
    }))

  const broken = makeGate(true)
  const brokenLaw = broken.law('one holder per server', ({clients, servers, Held}) =>
    forall((c1, c2, s) => all(
      sizedSort('Client', clients).has(c1), sizedSort('Client', clients).has(c2), sizedSort('Server', servers).has(s),
      Held.has(c1, s), Held.has(c2, s),
    ).implies(c1.eq(c2))))
  const ref = proveRule(broken, [brokenLaw], {search: {ms: 5000}})
  expect(ref.proven).toBe(false)
  expect(ref.run).toBeDefined()

  const intact = makeGate(false)
  const intactLaw = intact.law('one holder per server', ({clients, servers, Held}) =>
    forall((c1, c2, s) => all(
      sizedSort('Client', clients).has(c1), sizedSort('Client', clients).has(c2), sizedSort('Server', servers).has(s),
      Held.has(c1, s), Held.has(c2, s),
    ).implies(c1.eq(c2))))
  // Include a simple intact inductive law so the unit test stays fast while exercising intact relational proving.
  const okLaw = intact.law('free implies unheld', ({clients, servers, Free, Held}) =>
    forall((c, s) => all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s), Free.at(s)).implies(Held.has(c, s).not())))
  const ok = proveRule(intact, [intactLaw, okLaw], {search: {ms: 5000}})
  expect(ok.proven).toBe(true)
  expect(ok.checked).toBe(true)
  expect(ok.run).toBeUndefined()
  // Also run unassisted search briefly on intact to ensure early-stop emits zero false refutations.
  const searched = proveRule(intact, [intactLaw], {search: {ms: 1500}})
  expect(searched.run).toBeUndefined()
}, 15_000)

test('replayVerifiedRefutation rejects candidates whose precondition or facts fail', () => {
  const f = fn(1, (k: number) => k % 2, {facts: g => ({'f is identity below 3': forall(k => k.lt(3).implies(g(k).eq(k)))})})
  const r = rule('fact gated')
    .params({size: nat}).pre(({size}) => size.atLeast(2))
    .inputs({x: nat})
    .fns({f})
    .state({bad: 0})
    .step(({x, f, bad}) => ({bad: when(f(x).eq(0).and(x.atLeast(2)), 1, bad)}))
  const law = r.law('never bad', ({bad}) => bad.eq(0))

  // At size=1, pre fails; at size=3, fact f(2)=2 fails (since f(2)=0). Both must be rejected by replayVerifiedRefutation.
  const candPre = {law, params: {size: 1}, state: {scalars: {bad: 1}, maps: {}}, trace: [{x: 2}]}
  expect(replayVerifiedRefutation(r, [law], [], candPre)).toBeUndefined()
  const candFact = {law, params: {size: 3}, state: {scalars: {bad: 1}, maps: {}}, trace: [{x: 2}]}
  expect(replayVerifiedRefutation(r, [law], [], candFact)).toBeUndefined()
})
