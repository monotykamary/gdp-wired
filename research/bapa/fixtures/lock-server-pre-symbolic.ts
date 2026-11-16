// Frozen legacy lock-server encoding from 18171bbe3, before the accepted symbolic
// port. This negative-control fixture must retain its literal radix and guards.
import {bool, nat, oneOf, rule, when, yes, no} from '../../../core/dsl.ts'
export const historicalLockServer = () => rule('lock server')
  .inputs({op: oneOf('connect', 'disconnect'), c: nat, s: nat})
  .assume(({c, s}) => c.lt(64).and(s.lt(64)))
  .maps({Link: bool.from(false), Semaphore: bool.from(true)})
  .flags(({op, c, s, Link, Semaphore}) => ({
    connects: op.is('connect').and(Semaphore.at(s)),
    disconnects: op.is('disconnect').and(Link.at(c.times(64).plus(s))),
  }))
  .step(({c, s, connects, disconnects, Link, Semaphore}) => ({
    Link: Link.set(c.times(64).plus(s), when(connects, yes, when(disconnects, no, Link.at(c.times(64).plus(s))))),
    Semaphore: Semaphore.set(s, when(connects, no, when(disconnects, yes, Semaphore.at(s)))),
  }))
