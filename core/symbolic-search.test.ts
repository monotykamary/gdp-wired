// Regression tests for symbolic-size & tuple-view search bugs (Item 2):
// (1) valued-map nil/non-nil literals (`1 <= M[...]`) and symbolic-sort constant-cap suppression.
import {expect, test} from 'bun:test'
import {Term, all, bool, everyKey, exists, forall, nat, oneOf, proveRule, rule, sizedSort, when, yes} from './dsl.ts'
import {tuple} from './machine.ts'
import {inferLaws} from './infer.ts'

test('bug 1: valued map emits nil/non-nil literals and suppresses spurious constant cap on symbolic counted quorum', () => {
  const rel = bool.from(false)
  const r = rule('mini toy consensus forall')
    .params({size: nat, values: nat}).sorts('Node', 'Value')
    .inputs({op: oneOf('cast_vote', 'decide'), i: nat, v: nat}).carries('Q')
    .counts({members: ({Q, size}) => ({below: size, body: (_x: Term, k: Term) => Q.has(k)})})
    .assume(({op, i, v, size, values, Q, members}) => all(
      sizedSort('Node', size).has(i),
      sizedSort('Value', values).has(v),
      op.is('decide').implies(everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(size)))).and(size.lt(members.at(0).times(2)))),
    ))
    .maps({Vote: 0, Voted: rel, Decided: rel})
    .flags(({v, Q, Vote}) => ({allVote: everyKey(k => Q.has(k).implies(Vote.at(k).eq(v.plus(1))))}))
    .flags(({op, i, allVote, Voted}) => ({casts: op.is('cast_vote').and(Voted.at(i).not()), decides: op.is('decide').and(allVote)}))
    .step(({i, v, casts, decides, Vote, Voted, Decided}) => ({
      Vote: Vote.set(i, when(casts, v.plus(1), Vote.at(i))),
      Voted: Voted.set(i, when(casts, yes, Voted.at(i))),
      Decided: Decided.set(v, when(decides, yes, Decided.at(v))),
    }))
  const law = r.law('one value decided', ({values, Decided}) =>
    forall((a, b) => all(sizedSort('Value', values).has(a), sizedSort('Value', values).has(b), Decided.at(a), Decided.at(b)).implies(a.eq(b))))
  const cubes = inferLaws(r, [law], [], {cubes: 2, ms: 5_000}).found.map(f => f.text)
  expect(cubes.some(t => t.includes('1 <= Vote[x]') && t.includes('Voted[x] is 0'))).toBe(true)
  const v = proveRule(r, [law], {search: {ms: 15_000}})
  expect(v.proven).toBe(true)
  expect(v.checked).toBe(true)
  expect((v.found?.laws ?? []).some(l => /Vote at most \d+/.test(l.text))).toBe(false)
}, 30_000)

test('bug 1: tuple-keyed valued map emits 1 <= Table[...] cubes linking ownership', () => {
  const r = rule('mini sharded table')
    .params({nodes: nat, keys: nat, values: nat}).sorts('Node', 'Key', 'Value')
    .inputs({op: oneOf('own', 'put'), n: nat, k: nat, v: nat})
    .assume(({n, k, v, nodes, keys, values}) => all(
      sizedSort('Node', nodes).has(n),
      sizedSort('Key', keys).has(k),
      sizedSort('Value', values).has(v),
    ))
    .maps({Table: 0}).relations({Owner: ['Key', 'Node']})
    .flags(({k, nodes, Owner}) => ({unowned: everyKey(m => sizedSort('Node', nodes).has(m).implies(Owner.has(k, m).not()))}))
    .flags(({op, n, k, unowned, Owner}) => ({owns: op.is('own').and(unowned), puts: op.is('put').and(Owner.has(k, n))}))
    .step(({n, k, v, owns, puts, Table, Owner}) => ({
      Table: Table.set(new Term(tuple([n.e, k.e])), when(puts, v.plus(1), Table.at(new Term(tuple([n.e, k.e]))))),
      Owner: Owner.add([k, n], owns),
    }))
  const law = r.law('one value per key', ({nodes, keys, values, Table}) =>
    forall((a, b, k, v, u) => all(a.lt(nodes), b.lt(nodes), k.lt(keys), v.lt(values), u.lt(values),
      Table.at(new Term(tuple([a.e, k.e]))).eq(v.plus(1)), Table.at(new Term(tuple([b.e, k.e]))).eq(u.plus(1))).implies(a.eq(b).and(v.eq(u)))))
  const cubes = inferLaws(r, [law], [], {cubes: 2, ms: 5_000}).found.map(f => f.text)
  expect(cubes.some(t => t.includes('1 <= Table[') && t.includes('Owner[') && t.includes('is 0'))).toBe(true)
})

test('bug 2: projected free$enum carries sort bounds in law frame and proves symbolic lock server', () => {
  const relTrue = bool.from(true)
  const r = rule('mini lock server')
    .params({clients: nat, servers: nat}).sorts('Client', 'Server')
    .inputs({op: oneOf('connect', 'disconnect'), c: nat, s: nat})
    .assume(({clients, servers, c, s}) => all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s)))
    .maps({Semaphore: relTrue}).relations({Link: ['Client', 'Server']})
    .flags(({op, c, s, Link, Semaphore}) => ({
      connects: op.is('connect').and(Semaphore.at(s)),
      disconnects: op.is('disconnect').and(Link.has(c, s)),
    }))
    .step(({c, s, connects, disconnects, Link, Semaphore}) => ({
      Link: {...Link.add([c, s]), value: when(connects, 1, when(disconnects, 0, Link.at(c, s))).e},
      Semaphore: Semaphore.set(s, when(connects, yes.not(), when(disconnects, yes, Semaphore.at(s)))),
    }))
  const law = r.law('one client per server', ({clients, servers, Link}) =>
    forall((c1, c2, s) => all(sizedSort('Client', clients).has(c1), sizedSort('Client', clients).has(c2), sizedSort('Server', servers).has(s), Link.has(c1, s), Link.has(c2, s)).implies(c1.eq(c2))))
  const v = proveRule(r, [law], {search: {ms: 15_000}})
  expect(v.proven).toBe(true)
  expect(v.checked).toBe(true)
  const projLaw = v.found?.laws?.find(l => l.text.includes('Link[⟨_, x⟩]'))?.law
  expect(projLaw).toBeDefined()
  expect(JSON.stringify(projLaw!.holds)).toContain('"name":"clients"')
}, 30_000)

test('bug 3: demand-driven projected uniqueness proves symbolic simple decentralized lock without 4-key views', () => {
  const rel = bool.from(false)
  const r = rule('mini decentralized lock')
    .params({size: nat}).sorts('Node')
    .inputs({op: oneOf('init', 'send', 'recv'), src: nat, dst: nat})
    .assume(({src, dst, size}) => all(sizedSort('Node', size).has(src), sizedSort('Node', size).has(dst)))
    .state({started: 0})
    .maps({HasLock: rel}).relations({Message: ['Node', 'Node']})
    .flags(({op, src, dst, started, Message, HasLock}) => ({
      inits: op.is('init').and(started.eq(0)),
      sends: op.is('send').and(started.eq(1), HasLock.at(src)),
      recvs: op.is('recv').and(started.eq(1), Message.has(src, dst)),
    }))
    .step(({src, dst, inits, sends, recvs, started, Message, HasLock}) => ({
      started: when(inits, 1, started),
      Message: {...Message.add([src, dst]), value: when(sends, 1, when(recvs, 0, Message.at(src, dst))).e},
      HasLock: HasLock.each(k => when(inits.and(k.eq(src)), yes, when(sends.and(k.eq(src)), yes.not(), when(recvs.and(k.eq(dst)), yes, HasLock.at(k))))),
    }))
  const law = r.law('one node holds the lock', ({size, HasLock}) =>
    forall((a, b) => all(sizedSort('Node', size).has(a), sizedSort('Node', size).has(b), HasLock.at(a), HasLock.at(b)).implies(a.eq(b))))
  const v = proveRule(r, [law], {search: {ms: 15_000}})
  expect(v.proven).toBe(true)
  expect(v.checked).toBe(true)
  const texts = (v.found?.laws ?? []).map(l => l.text)
  expect(texts.some(t => t.includes('Message[⟨x, _⟩]') && t.includes('Message[⟨y, _⟩]'))).toBe(true)
  expect(texts.some(t => t.includes('Message[⟨_, x⟩]') && t.includes('Message[⟨_, y⟩]'))).toBe(true)
}, 30_000)

test('bug 4: tuple each-write setters and coupled binderGhostsOf prove sharded kv no-lost-keys', () => {
  const rel = bool.from(false)
  const makeRule = (broken: boolean) => rule('mini sharded no lost')
    .params({nodes: nat, keys: nat, values: nat}).sorts('Node', 'Key', 'Value')
    .inputs({op: oneOf('own', 'start', 'reshard', 'recv', 'put'), n: nat, k: nat, v: nat, n2: nat})
    .assume(({n, k, v, n2, nodes, keys, values}) => all(
      sizedSort('Node', nodes).has(n), sizedSort('Node', nodes).has(n2),
      sizedSort('Key', keys).has(k), sizedSort('Value', values).has(v),
    ))
    .state({started: 0})
    .maps({Table: 0, Owned: rel}).relations({Owner: ['Key', 'Node'], TransferMsg: ['Node', 'Key', 'Value']})
    .flags(({k, keys, nodes, Owner, Owned}) => ({
      unowned: everyKey(m => sizedSort('Node', nodes).has(m).implies(Owner.has(k, m).not())),
      allOwned: everyKey(m => sizedSort('Key', keys).has(m).implies(Owned.at(m))),
    }))
    .flags(({op, n, k, v, started, unowned, allOwned, Table, Owner, TransferMsg}) => ({
      owns: op.is('own').and(started.eq(0), unowned),
      starts: op.is('start').and(started.eq(0), allOwned),
      reshards: op.is('reshard').and(started.eq(1), Table.at(new Term(tuple([n.e, k.e]))).eq(v.plus(1))),
      receives: op.is('recv').and(started.eq(1), TransferMsg.has(n, k, v)),
      puts: op.is('put').and(started.eq(1), Owner.has(k, n)),
    }))
    .step(({n, k, v, n2, owns, starts, reshards, receives, puts, started, Table, Owner, TransferMsg, Owned}) => ({
      started: when(starts, 1, started),
      Table: Table.set(new Term(tuple([n.e, k.e])), when(reshards, 0, when(receives.or(puts), v.plus(1), Table.at(new Term(tuple([n.e, k.e])))))),
      Owner: {...Owner.add([k, n]), value: when(owns.or(receives), 1, when(reshards, 0, Owner.at(k, n))).e},
      TransferMsg: TransferMsg.each((a, b, c) => reshards.and(a.eq(n2), b.eq(k), c.eq(v))
        .and(broken ? TransferMsg.has(a, b, c) : yes)
        .or(TransferMsg.has(a, b, c).and(reshards.and(a.eq(n2), b.eq(k), c.eq(v)).not(), receives.and(a.eq(n), b.eq(k), c.eq(v)).not()))),
      Owned: Owned.set(k, when(owns, yes, Owned.at(k))),
    }))
  const makeLaw = (r: ReturnType<typeof makeRule>) => r.law('no lost keys', ({nodes, keys, values, started, Owner, TransferMsg}) =>
    forall(k => k.lt(keys).and(started.eq(1)).implies(
      exists(x => x.lt(nodes).and(Owner.has(k, x))).or(
        exists(n => exists(j => exists(v => all(n.lt(nodes), j.lt(keys), v.lt(values), TransferMsg.has(n, j, v)))))))))

  const intact = makeRule(false), vOk = proveRule(intact, [makeLaw(intact)], {search: {ms: 20_000}})
  expect(vOk.proven).toBe(true)
  expect(vOk.checked).toBe(true)
  expect(vOk.run).toBeUndefined()

  const broken = makeRule(true), vBad = proveRule(broken, [makeLaw(broken)], {search: {ms: 10_000}})
  expect(vBad.proven).toBe(false)
  expect(vBad.run).toBeDefined()
}, 40_000)
