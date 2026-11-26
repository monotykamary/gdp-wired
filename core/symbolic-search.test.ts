// Regression tests for symbolic-size & tuple-view search bugs (Item 2):
// (1) valued-map nil/non-nil literals (`1 <= M[...]`) and symbolic-sort constant-cap suppression.
import {expect, test} from 'bun:test'
import {Term, all, bool, everyKey, forall, nat, oneOf, proveRule, rule, sizedSort, when, yes} from './dsl.ts'
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
