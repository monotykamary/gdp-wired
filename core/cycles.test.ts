// Cycles found (core/cycles.ts): what the search builds the kernel checks again on its own; a tampered proof found is
// refused; the broken variants are refused; the ranks are the small ones the runs give.
import {expect, test} from 'bun:test'
import {refuseCyclic} from '../kernel/cyclic.ts'
import {readFileSync} from 'node:fs'
import {findCycles, findRank, linE, rankOfRelation, rankWithInvariants, showE} from './cycles.ts'
import {check, loopObligations} from '../kernel/kernel.ts'
import {grow} from '../kernel/prove.ts'
import {parseAri} from '../compare/term/ari.ts'
import {build} from '../compare/term/translate.ts'
import {bool, nat, no, oneOf, proveLeadsTo, proveLoop, proveRule, rule, when, yes} from './dsl.ts'
import {accumulator, ackermann, claimCases, countUp, euclid, exchange, exchangeLoop, liveCases, loopCases, mccarthy, phases, ruleCases, toProduct, triangle} from '../examples/cycles.ts'

test('claims over functions: each proven and checked by the kernel again, each broken variant refused', () => {
  for (const [c, want] of claimCases()) {
    const out = findCycles(c.facts, c.claims)
    expect([c.name, out.proven && out.checked]).toEqual([c.name, want])
    if (want) expect(refuseCyclic(out.proof!)).toBeUndefined()
    // The claims are nodes of the proof as given.
    if (want) for (const cl of c.claims) expect(out.proof!.nodes.find(n => n.name === cl.name)).toMatchObject({hyps: cl.hyps ?? [], concl: cl.concl})
  }
}, 60_000)

test('ranks from the runs: 101 − n, (m, n) in order, a companion below its claim', () => {
  const mc = findCycles(mccarthy().facts, mccarthy().claims)
  expect(mc.found?.ranks['f(n) = 91 for n <= 101']).toBe('(101 − n)')
  expect(findCycles(ackermann().facts, ackermann().claims).found?.ranks['ack(m, n) > n']).toBe('(m, n)')
  const acc = findCycles(accumulator().facts, accumulator().claims)
  expect(acc.found?.companions).toEqual(['g(x, g1$0) = g1$0 + 2·x'])
  expect(showE(linE({n: -1}, 101))).toBe('101 − n')
})

test('a proof found, tampered, is refused', () => {
  const p = findCycles(mccarthy().facts, mccarthy().claims).proof!
  expect(refuseCyclic({...p, nodes: p.nodes.map(n => ({...n, rank: n.rank.map(() => ({op: 'var', name: 'n'}))}))})).toBeDefined()
  expect(refuseCyclic({...p, nodes: p.nodes.map(n => ({...n, uses: n.uses.map(u => ({...u, guard: {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}}))}))})).toBeDefined()
})

test('loops with no rank: the rank and the invariants found, the broken ones refused', () => {
  expect(findRank(phases().loop).found?.rank).toBe('(x, y)')
  expect(findRank(euclid().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(a + b)'}})
  for (const [l, want] of loopCases()) expect([l.loop.name, proveLoop(l, []).proven]).toEqual([l.loop.name, want])
}, 60_000)

test('rules reading functions known by their facts: the lemma found in the search, not without it', () => {
  for (const [{r, laws}, want] of ruleCases()) {
    expect([r.machine.name, proveRule(r, laws).proven]).toEqual([r.machine.name, want])
    expect(proveRule(r, laws, {search: {cycles: false}}).proven).toBe(false)
  }
}, 60_000)

test('past linear ranks with coefficients up to 4: the exact LP, products of two variables, ranks in order', () => {
  expect(findCycles(exchange().facts, exchange().claims).found?.ranks['ex(x, y) <= 5']).toBe('(11·x + 2·y)')
  expect(findCycles(countUp().facts, countUp().claims).found?.ranks['up(i, n) >= n·n']).toBe('(n·n − i)')
  expect(findRank(exchangeLoop().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(11·x + 2·y)'}})
  expect(findRank(toProduct().loop)).toMatchObject({proven: true, checked: true, found: {rank: '(M·N − (i + 1))'}})
  // A rank the runs' size bounds (32·x + y where x reaches 33) is refused: the triangle's is (x, y).
  expect(findRank(triangle().loop).found?.rank).toBe('(x, y)')
}, 60_000)

test('liveness with no rank: the rank found, the broken ones refused', () => {
  for (const [c, want] of liveCases()) expect([c.name, proveLeadsTo(c.r, c.laws, c.live).proven]).toEqual([c.name, want])
  expect(proveLeadsTo(liveCases()[2]![0].r, [], liveCases()[2]![0].live).found?.rank).toBe('(2·inbox + outbox)')
}, 60_000)

// The relation's ranks (rankOfRelation, rankWithInvariants): TermComp and SV-COMP tasks from the second frontier corpus,
// as the benchmark translates them; each rank's halting goals proven and checked by the kernel, and each task's broken
// variant (a run that never ends) given none the kernel takes.
test('ranks from the relation: per location, in order, multiphase, with invariants; the broken variants refused', () => {
  const dir = `${import.meta.dir}/../research/frontier2/tasks`
  const loopOf = (f: string) => build(parseAri(readFileSync(`${dir}/${f}`, 'utf8')), f).loop
  const halts = (f: string, invariants = false): boolean => {
    const ms = f.includes('.broken.') ? 2_000 : 10_000, l = loopOf(f), r = invariants ? rankWithInvariants(l, [], performance.now() + ms) : rankOfRelation(l, [], performance.now() + ms)
    if (!('rank' in r)) return false
    return loopObligations(l, 'laws' in r ? r.laws : [], r.rank).every(g => { const o = grow(g); return 'tree' in o && check(g, o.tree) })
  }
  for (const f of ['its/Continue1.jar-obl-8', 'its/p-60.t2_fixed', 'its/AckR.jar-obl-8', 'its/Alternate.jar-obl-10', 'its/toy3.t2', 'its/polyrank1.t2', 'sv/2Nested-1', 'its/AProVEMath.jar-obl-8', 'sv/WhileFalse']) {
    expect([f, halts(`${f}.ari`)]).toEqual([f, true])
    expect([f, halts(`${f}.broken.ari`), halts(`${f}.broken.ari`, true)]).toEqual([f, false, false])
  }
  expect(halts('sv/McCarthy91_Iteration.ari', true)).toBe(true)
  expect(halts('sv/McCarthy91_Iteration.broken.ari', true)).toBe(false)
  // regions with their own invariants: x is 1 or −1 (x ≠ 0, a disjunction), 100 − y where x ≥ 1, 100 − z where not
  expect(halts('sv/Toulouse-BranchesToLoop-2.ari', true)).toBe(true)
  expect(halts('sv/Toulouse-BranchesToLoop-2.broken.ari', true)).toBe(false)
}, 120_000)

// The real-world corpus: with no rank stated, 0 of its 35 liveness laws; with rank 0 stated, 19. The fit needs a
// helpful step that stays pending, and where every helpful step reaches `to` at once there is none. The trivial
// ranks are tried first: 0, then each state variable alone that the runs allow.
test('liveness with no rank: the trivial ranks tried first (0, a variable alone)', () => {
  // a marker set by a refill and cleared by the next admission (LibreChat's): the helpful request clears it at once
  const marker = rule('marker').inputs({op: oneOf('refill', 'admit', 'noop')}).state({pending: bool.from(false), refills: 0})
    .step(({op, pending, refills}) => ({pending: when(op.is('refill'), yes, when(op.is('admit'), no, pending)), refills: when(op.is('refill'), refills.plus(1), refills)}))
  const v = proveLeadsTo(marker, [], marker.leadsTo('a marker is eventually cleared', {from: ({pending}) => pending, to: ({pending}) => pending.not(), helpful: () => ({op: 1})}), {ms: 5000})
  expect(v).toMatchObject({proven: true, checked: true, found: {rank: '(0)'}})
  // a batch of n jobs drained one at a time (a peek takes none): the rank is what is left alone
  const queue = rule('queue').params({n: nat}).inputs({op: oneOf('peek', 'pop')}).state({len: ({n}) => n})
    .step(({op, len}) => ({len: when(op.is('pop'), len.minus(1), len)}))
  const w = proveLeadsTo(queue, [], queue.leadsTo('the queue drains', {from: () => yes, to: ({len}) => len.eq(0), helpful: () => ({op: 1})}), {ms: 5000})
  expect(w).toMatchObject({proven: true, checked: true, found: {rank: '(len)'}})
  // and a helpful step that misses the goal still refused: a marker the admission never clears
  const stuck = rule('stuck marker').inputs({op: oneOf('refill', 'admit')}).state({pending: bool.from(false)})
    .step(({op, pending}) => ({pending: when(op.is('refill'), yes, pending)}))
  expect(proveLeadsTo(stuck, [], stuck.leadsTo('cleared', {from: ({pending}) => pending, to: ({pending}) => pending.not(), helpful: () => ({op: 1})}), {ms: 3000}).proven).toBe(false)
}, 60_000)

// Under strong fairness a helpful request may hand over to a higher region instead of lowering the rank (kernel.ts's
// livenessParts): the search reads the levels off the runs (a region's hand-overs to one whose request ends), so a fetch
// that hands a waiting job to a worker keeps the rank and no rank must fall on it: rank 0, with the levels the kernel's
// search chooses. A stall that may lose the job is refused all the same.
test('strong fairness: the rank search lets a helpful request hand over', () => {
  const job = (bug?: 'lost') => rule('flaky job')
    .inputs({op: oneOf('fetch', 'stall', 'fail', 'lose')})
    .state({st: (bug ? oneOf('wait', 'active', 'failed', 'lost') : oneOf('wait', 'active', 'failed')).from('wait')})
    .flags(({op, st}) => ({fetches: op.is('fetch').and(st.is('wait')), stalls: op.is('stall').and(st.is('active')), fails: op.is('fail').and(st.is('active')),
      loses: bug ? op.is('lose').and(st.is('active')) : op.is('lose').and(st.is('active'), st.is('wait'))}))
    .step(({st, fetches, stalls, fails, loses}) => ({st: when(fetches, 'active', when(stalls, 'wait', when(fails, 'failed', bug ? when(loses, 'lost', st) : st)))}))
  const ends = (j: ReturnType<typeof job>) => j.leadsTo('the job fails for good', {from: ({st}) => st.is('failed').not(), to: ({st}) => st.is('failed'),
    helpful: [{when: ({st}) => st.is('wait'), request: () => ({op: 0})}, {when: ({st}) => st.is('active'), request: () => ({op: 2})}], fairness: 'strong'})
  const j = job(), v = proveLeadsTo(j, j.kindLaws(), ends(j), {ms: 20000})
  expect([v.proven, v.checked, v.found?.rank]).toEqual([true, true, '(0)'])
  const jb = job('lost')
  expect(proveLeadsTo(jb, jb.kindLaws(), ends(jb), {ms: 5000}).proven).toBe(false)
}, 60_000)
