import {expect, test} from 'bun:test'
import {all, bool, forall, nat, no, oneOf, proveRule, rule, sizedSort, when, yes} from './dsl.ts'
import {domainStep, inferLaws} from './infer.ts'
import {pool, poolLaw} from '../examples/infer.ts'

// Point-write relational rule (`m.relations` present, `domainStep` undefined):
// two clients cannot hold the same server's lock.
const pointLock = (broken = false) => rule('point relational lock')
  .params({clients: nat, servers: nat}).sorts('Client', 'Server')
  .inputs({op: oneOf('connect', 'disconnect'), c: nat, s: nat})
  .assume(({clients, servers, c, s}) => all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s)))
  .maps({Free: bool.from(true)})
  .relations({Held: ['Client', 'Server']})
  .flags(({op, c, s, Held, Free}) => ({
    connects: op.is('connect').and(broken ? yes : Free.at(s)),
    disconnects: op.is('disconnect').and(Held.has(c, s)),
  }))
  .step(({c, s, connects, disconnects, Held, Free}) => ({
    Held: {...Held.add([c, s]), value: when(connects, 1, when(disconnects, 0, Held.at(c, s))).e},
    Free: Free.set(s, when(connects, no, when(disconnects, yes, Free.at(s)))),
  }))

// Provable point-write relational rule (`m.relations` present, `domainStep` undefined).
const singleMutex = (broken = false) => rule('point relational mutex')
  .sorts('Node')
  .inputs({op: oneOf('grant', 'release'), a: nat, b: nat})
  .maps({Free: bool.from(true)})
  .relations({Grant: ['Node', 'Node']})
  .flags(({op, a, b, Free, Grant}) => ({
    grants: op.is('grant').and(broken ? yes : Free.at(b)),
    releases: op.is('release').and(Grant.has(a, b)),
  }))
  .step(({a, b, grants, releases, Free, Grant}) => ({
    Free: Free.set(b, when(grants, no, when(releases, yes, Free.at(b)))),
    Grant: {...Grant.add([a, b]), value: when(grants, 1, when(releases, 0, Grant.at(a, b))).e},
  }))

test('relational rules without domainStep skip scalar/cell houdini and unused noJoin setup', () => {
  const r = pointLock()
  expect(domainStep(r.machine)).toBeUndefined()
  expect(Object.keys(r.machine.relations ?? {})).toEqual(['Held'])
  const law = r.law('one holder per server', ({clients, servers, Held}) =>
    forall((c1, c2, s) => all(sizedSort('Client', clients).has(c1), sizedSort('Client', clients).has(c2), sizedSort('Server', servers).has(s), Held.has(c1, s), Held.has(c2, s)).implies(c1.eq(c2))))

  const events: {phase: string, info: Record<string, number | string>}[] = []
  inferLaws(r, [law], [], {
    ms: 10_000,
    wall: Infinity,
    progress: (phase, info) => events.push({phase, info}),
  })

  const houdini = events.find(e => e.phase === 'houdini')
  const joinStarts = events.filter(e => e.phase === 'join start')
  const engineStart = events.find(e => e.phase === 'join meters' && e.info.at === 'engine')
  expect(houdini).toBeDefined()
  expect(houdini!.info.ctis).toBe(0)
  expect(joinStarts).toHaveLength(0)
  expect(engineStart).toBeDefined()
  expect(engineStart!.info.evals).toBe(0)
  expect(engineStart!.info.erows).toBe(0)
}, 30_000)

test('provable and broken point-write relational rules still prove and refute cleanly', () => {
  const ok = singleMutex()
  expect(domainStep(ok.machine)).toBeUndefined()
  const safety = (r: ReturnType<typeof singleMutex>) => r.law('unique grant', ({Grant}) =>
    forall((a, b, c) => all(Grant.has(a, b), Grant.has(c, b)).implies(a.eq(c))))

  const events: {phase: string, info: Record<string, number | string>}[] = []
  const v = inferLaws(ok, [safety(ok)], [], {
    ms: 15_000,
    wall: Infinity,
    progress: (phase, info) => events.push({phase, info}),
  })
  expect(v).toMatchObject({proven: true, checked: true})
  expect(events.filter(e => e.phase === 'join start')).toHaveLength(0)
  const engineStart = events.find(e => e.phase === 'join meters' && e.info.at === 'engine')
  expect(engineStart?.info.evals).toBe(0)
  expect(engineStart?.info.erows).toBe(0)
  expect(proveRule(ok, [safety(ok), ...v.found.map(f => f.law)], {search: false})).toMatchObject({proven: true, checked: true})

  const bad = singleMutex(true)
  const refuted = proveRule(bad, [safety(bad)], {search: {ms: 10_000}})
  expect(refuted.proven).toBe(false)
  expect(refuted.run).toBeDefined()
}, 30_000)

test('non-relational rules keep join and houdini, while join:0 skips only join setup', () => {
  const r = pool(), law = poolLaw(r)
  const normalEvents: {phase: string, info: Record<string, number | string>}[] = []
  const vNormal = inferLaws(r, [law], [], {
    ms: 15_000,
    wall: Infinity,
    progress: (phase, info) => normalEvents.push({phase, info}),
  })
  expect(vNormal).toMatchObject({proven: true, checked: true})
  expect(normalEvents.some(e => e.phase === 'join start')).toBe(true)

  const noJoinEvents: {phase: string, info: Record<string, number | string>}[] = []
  const vNoJoin = inferLaws(r, [law], [], {
    ms: 15_000,
    wall: Infinity,
    join: 0,
    progress: (phase, info) => noJoinEvents.push({phase, info}),
  })
  expect(vNoJoin).toMatchObject({proven: true, checked: true})
  expect(noJoinEvents.filter(e => e.phase === 'join start')).toHaveLength(0)
  expect(noJoinEvents.some(e => e.phase === 'houdini')).toBe(true)
}, 30_000)
