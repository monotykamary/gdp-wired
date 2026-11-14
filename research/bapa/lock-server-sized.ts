// SECTION-63 row 3, opt-in migration; canonical IC3Syn registry is unchanged.
// The source uses Client×Server identities, not arithmetic on packed keys.
import {all, bool, forall, nat, no, oneOf, rule, sizedSort, when, yes} from '../../core/dsl.ts'

export function lockServerSized(bug = false) {
  return rule('lock server with sized domains')
    .params({clients: nat, servers: nat})
    .sorts('Client', 'Server')
    .inputs({op: oneOf('connect', 'disconnect'), c: nat, s: nat})
    .assume(({clients, servers, c, s}) => all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s)))
    .maps({Semaphore: bool.from(true)})
    .relations({Link: ['Client', 'Server']})
    .flags(({op, c, s, Link, Semaphore}) => ({
      connects: op.is('connect').and(bug ? yes : Semaphore.at(s)),
      disconnects: op.is('disconnect').and(Link.has(c, s)),
    }))
    .step(({c, s, connects, disconnects, Link, Semaphore}) => ({
      Link: {...Link.add([c, s]), value: when(connects, 1, when(disconnects, 0, Link.at(c, s))).e},
      Semaphore: Semaphore.set(s, when(connects, no, when(disconnects, yes, Semaphore.at(s)))),
    }))
}
export type SizedLockServer = ReturnType<typeof lockServerSized>

// This first family uses a helper GIVEN by the implementer, not found by search.
export function lockServerSizedLaws(r: SizedLockServer) {
  return [
    r.law('one client per server', ({clients, servers, Link}) => forall((c1, c2, s) =>
      all(sizedSort('Client', clients).has(c1), sizedSort('Client', clients).has(c2), sizedSort('Server', servers).has(s), Link.has(c1, s), Link.has(c2, s)).implies(c1.eq(c2)))),
    r.law('a linked server is unavailable', ({clients, servers, Link, Semaphore}) => forall((c, s) =>
      all(sizedSort('Client', clients).has(c), sizedSort('Server', servers).has(s), Link.has(c, s)).implies(Semaphore.at(s).not()))),
  ]
}

// Stronger laws: no domain guards. Out-of-domain cells start empty and are
// never written, and native tuples do not alias. The helper is still GIVEN.
export function lockServerUnrestrictedLaws(r: SizedLockServer) {
  return [
    r.law('one client per server over all naturals', ({Link}) => forall((c1, c2, s) =>
      Link.has(c1, s).and(Link.has(c2, s)).implies(c1.eq(c2)))),
    r.law('every linked server is unavailable', ({Link, Semaphore}) => forall((c, s) =>
      Link.has(c, s).implies(Semaphore.at(s).not()))),
  ]
}
