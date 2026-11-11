import {expect, test} from 'bun:test'
import {type Law, all, get, n, same, x} from './machine.ts'
import {admitCountedFamily, countedAttempts, countsDump, supportOrder, certFor} from './counts.ts'
import {prepareCountStrategyMachine, proveCountStrategies, proveCountStrategyPool} from './count-strategies.ts'
import {prepareGuardCountContext} from './count-guard-context.ts'
import {rowCompositionFixture} from './count-row-composition.fixture.ts'
import {env} from './solver.ts'
import {checkMC, countedObligations} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withinDeadline, withDeadline, withWall} from '../kernel/prove.ts'
function mode<T>(value: string, f: () => T): T {
  const before = env.GDP_COUNT_STRATEGIES
  env.GDP_COUNT_STRATEGIES = value
  try {return f()} finally {if (before === undefined) delete env.GDP_COUNT_STRATEGIES; else env.GDP_COUNT_STRATEGIES = before}
}
test('optional strategies share the attempt end and return an original-machine proof', () => {
  const {m, law, family} = rowCompositionFixture(), before = JSON.stringify(m), prior = countsDump.on
  try {
    for (const flag of ['0', '1']) mode(flag, () => counted(fullRate, () => withWall(performance.now() + 8000, () => {
      const events: Record<string, unknown>[] = [], until = clock() + 4000
      countsDump.on = e => {if ('phase' in e && String(e.phase).startsWith('count-strategy')) events.push({...e, activeEnd: withinDeadline(Infinity)})}
      const result = withDeadline(until + 5000, () => countedAttempts(m, [], new Set(), until + 5000).traced(law, family, 0, 4000))
      if (flag === '0') expect(events).toHaveLength(0)
      else {
        expect('proof' in result).toBe(true)
        expect(events.some(e => e.phase === 'count-strategy' && e.stage === 'operation')).toBe(true)
        expect(events.every(e => e.end === until && e.activeEnd === until)).toBe(true)
      }
      if ('proof' in result) for (const p of countedObligations(m, family, {[law.name]: result.proof.instances}, 0)) expect(checkMC(p.goal.hyps, p.decls, result.proof.certs[p.goal.name]!)).toBe(true)
    })))
  } finally {countsDump.on = prior}
  expect(JSON.stringify(m)).toBe(before)
}, 12000)
test('shape-only ordering puts row helpers after count helpers and before safety', () => {
  const {m, law, family} = rowCompositionFixture(), count = family[1]!, marker = family[2]!, safety: Law = {name: 'renamed caller', holds: same(n(0), n(0))}, set = [marker, safety, law, count]
  expect(mode('0', () => supportOrder(set, [safety], new Set(), false, m))).toEqual([count, safety, marker, law])
  expect(mode('1', () => supportOrder(set, [safety], new Set(), false, m))).toEqual([count, law, safety, marker])
  expect(mode('1', () => supportOrder(set, [safety], new Set(), true, m))).toEqual(set)
})
test('join and demand schedule a selected row before count-first fallback', () => {
  const {m, law, family} = rowCompositionFixture(), marker = family[2]!, prior = countsDump.on, countFirst = env.GDP_COUNTS_COUNT_FIRST, stopped = new Error('observed first attempt')
  try {
    env.GDP_COUNTS_COUNT_FIRST = '1'
    mode('1', () => {
      for (const support of [new Set<Law>(), new Set([marker])]) counted(fullRate, () => withWall(performance.now() + 3000, () => {
        const events: Record<string, unknown>[] = []
        countsDump.on = event => {
          if ('law' in event && event.law === law.name && 'phase' in event && (event.phase === 'query' || event.phase === 'count-strategy-result')) {
            events.push(event)
            throw stopped
          }
        }
        expect(() => admitCountedFamily(m, [law], [law, marker], support, clock() + 1000)).toThrow(stopped)
        expect(events).toHaveLength(1)
        expect(events[0]).toMatchObject({phase: 'count-strategy-result', pass: 0})
      }))
    })
  } finally {
    countsDump.on = prior
    if (countFirst === undefined) delete env.GDP_COUNTS_COUNT_FIRST; else env.GDP_COUNTS_COUNT_FIRST = countFirst
  }
})
test('a guard strategy cannot silently admit fresh count definitions', () => {
  const {m, family} = rowCompositionFixture(), law = family[1]!
  m.inputMaps = ['selected']; m.counts!.inputSize = {j: 'row', key: 'member', below: x('size'), body: {op: 'if', c: same(get('selected', x('member')), n(1)), then: n(1), else: n(0)}}
  const context = prepareGuardCountContext(m, law, family)
  expect(context).toBeDefined()
  expect(Object.keys(context!.machine.counts!).length).toBeGreaterThan(Object.keys(m.counts!).length)
  const events: Record<string, unknown>[] = []
  expect(proveCountStrategies(m, family, law, clock() + 1000, (g, ds) => certFor(g, ds), e => events.push(e))).toBeUndefined()
  expect(events).toContainEqual({strategy: 'guard', stage: 'decline', reason: 'unadmitted count definitions'})
})
test('admission installs exact conservative definitions so a generic guard composition can run', () => {
  const {m, family} = rowCompositionFixture(), law = family[1]!, before = JSON.stringify(m)
  m.inputMaps = ['selected']; m.counts!.inputSize = {j: 'row', key: 'member', below: x('size'), body: {op: 'if', c: same(get('selected', x('member')), n(1)), then: n(1), else: n(0)}}
  // Use a pure frame here: shape admission is independent of copy search.
  m.step = {}
  law.holds = {op: 'or', xs: [{op: 'not', x: all({op: '<', a: x('a'), b: x('size')}, {op: '<', a: x('b'), b: x('size')})}, law.holds]}
  const source = JSON.stringify(m), names = family.map(l => l.name)
  counted(fullRate, () => withWall(performance.now() + 6000, () => {
    const until = clock() + 4000, prepared = prepareCountStrategyMachine(m, family, until)
    expect(Object.keys(prepared.counts!).length).toBeGreaterThan(Object.keys(m.counts!).length)
    expect(prepared.step).toBe(m.step); expect(prepared.maps).toBe(m.maps)
    expect(JSON.stringify(m)).toBe(source); expect(family.map(l => l.name)).toEqual(names)
    expect(prepareCountStrategyMachine(prepared, family, until)).toBe(prepared)
    expect(prepareGuardCountContext(prepared, law, family)?.machine).toBe(prepared)
    const events: Record<string, unknown>[] = []
    const proof = proveCountStrategies(prepared, family, law, until, (g, ds) => certFor(g, ds, false, 0), e => events.push(e))
    expect(events.some(e => e.strategy === 'guard' && e.stage === 'operation')).toBe(true)
    expect(events.some(e => e.reason === 'unadmitted count definitions')).toBe(false)
    expect({proof: !!proof, events}).toMatchObject({proof: true})
    if (proof) for (const p of countedObligations(prepared, family, {[law.name]: proof.instances}, family.indexOf(law))) expect(checkMC(p.goal.hyps, p.decls, proof.certs[p.goal.name]!)).toBe(true)
    const name = Object.keys(prepared.counts!).find(name => !m.counts?.[name])!
    const broken = {...prepared, counts: {...prepared.counts, [name]: {...prepared.counts![name]!, below: n(0)}}}
    expect(prepareGuardCountContext(broken, law, family)).toBeUndefined()
  }))
  expect(before).not.toBe(source)
})
test('an empty or expired strategy pool cannot allocate or renew an attempt', () => {
  const {m, family} = rowCompositionFixture(), events: Record<string, unknown>[] = []
  let calls = 0
  const request = () => {calls++; return {reads: [], insts: [], picks: []}}
  const empty = proveCountStrategyPool(m, [], clock() + 1000, request, e => events.push(e))
  const expired = proveCountStrategyPool(m, family, clock() - 1, request, e => events.push(e))
  expect(empty.proofs.size).toBe(0); expect(expired.proofs.size).toBe(0)
  expect(calls).toBe(0); expect(events).toHaveLength(0)
})

test('unsupported laws fall through and a broken row is never accepted', () => {
  const {m, law, family} = rowCompositionFixture(), plain: Law = {name: 'unrelated', holds: same(n(0), n(0))}
  mode('1', () => counted(fullRate, () => withWall(performance.now() + 6000, () => {
    const until = clock() + 1500
    expect('proof' in countedAttempts(m, [], new Set(), until).traced(plain, [plain], 0, 100)).toBe(true)
    m.step.maps!.edge = {each: 'cell', value: {op: 'if', c: same(x('cell'), n(0)), then: n(1), else: n(0)}}
    m.step.maps!.marker = {each: 'r', value: n(1)}
    m.assume = all(m.assume!, same(x('mode'), n(0)))
    expect('proof' in countedAttempts(m, [], new Set(), until).traced(law, family, 0, Math.max(0, until - clock()))).toBe(false)
    expect(proveCountStrategies(m, family, law, clock() - 1, (g, ds) => certFor(g, ds))).toBeUndefined()
  })))
})
