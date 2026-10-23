// OpenZeppelin Contracts v5.7.0, TimelockController (contracts/governance/TimelockController.sol). MIT, (c) OpenZeppelin.
// https://github.com/OpenZeppelin/openzeppelin-contracts/blob/cab19933c33c2ad1d4c7a84864a3601dddfd16f3/contracts/governance/TimelockController.sol
//
// Operations are scheduled with a delay, become ready when it has passed, and are executed once (their timestamp set
// to DONE) or cancelled while pending. A call that fails a check reverts: nothing changes, which the step says as
// "every part keeps its value". An operation is its id (the hash of its calls, its predecessor and its salt): the
// predecessor is part of the id, so it is kept with the id when scheduled. Time is block.timestamp, which never goes
// down: each request carries how far it moved (`dt`).
import {bool, forall, maybe, nat, oneOf, optional, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'OpenZeppelin/openzeppelin-contracts', commit: 'cab19933c33c2ad1d4c7a84864a3601dddfd16f3', licence: 'MIT', author: 'OpenZeppelin', language: 'Solidity'}

const DONE = 1 // :28 DONE_TIMESTAMP
export const timelock = () => rule('TimelockController')
  // :115-136 the constructor: `minDelay`, a proposer (who also gets the canceller role), an executor, or the executor
  // role open to anyone (granted to address(0), :140-153 onlyRoleOrOpenRole); `self`: the timelock's own address
  // (updateDelay, :447-454); `t0`: the block timestamp at deployment (a real chain's is far past DONE_TIMESTAMP = 1);
  // `d`: the operation a liveness law watches (not the code's).
  .params({minDelay0: nat, proposer: nat, executor: nat, open: bool, self: nat, t0: nat, d: nat})
  .pre(({t0}) => t0.atLeast(2))
  // One call: msg.sender, the operation id, its predecessor (bytes32(0): none), the delay asked, and the time passed.
  .inputs({op: oneOf('schedule', 'cancel', 'execute', 'updateDelay', 'wait'), sender: nat, id: nat, pred: maybe(nat), delay: nat, newDelay: nat, dt: nat})
  // block.timestamp is t0 + `now` (the time since deployment); `minDelay` :31 _minDelay, missing until updateDelay
  // sets it (the constructor's minDelay0 until then, :135).
  .state({now: 0, minDelay: maybe(nat).from(null)})
  // :30 _timestamps; `Pred`: the predecessor bound into each id (1 + its id, 0 for none). Ghosts: `Runs` executions of
  // each operation (its calls made), `ReadyAt` the earliest time allowed by minDelay when it was last scheduled.
  .maps({Ts: 0, Pred: 0, Runs: 0, ReadyAt: 0})
  .flags(({op, sender, id, delay, dt, now, t0, minDelay, minDelay0, proposer, executor, open, self, Ts, Pred}) => {
    const t = t0.plus(now).plus(dt)
    const md = minDelay.match({none: () => minDelay0, some: v => v})
    // :205-217 getOperationState: 0 Unset, 1 Done, > now Waiting, else Ready.
    const pending = (k: typeof id) => Ts.at(k).gt(DONE)
    const ready = (k: typeof id) => pending(k).and(Ts.at(k).atMost(t))
    const p = Pred.at(id)
    return {
      // :264-322 schedule: onlyRole(PROPOSER_ROLE); not an operation yet; delay >= minDelay.
      schedules: op.is('schedule').and(sender.eq(proposer), Ts.at(id).eq(0), delay.atLeast(md)),
      // :332-340 cancel: onlyRole(CANCELLER_ROLE) (the proposers, :128-129); pending.
      cancels: op.is('cancel').and(sender.eq(proposer), pending(id)),
      // :356-378 execute: onlyRoleOrOpenRole(EXECUTOR_ROLE); :418-425 _beforeCall: ready, and the predecessor done.
      executes: op.is('execute').and(sender.eq(executor).or(open), ready(id), p.eq(0).or(Ts.at(p.minus(1)).eq(DONE))),
      updates: op.is('updateDelay').and(sender.eq(self)),
    }
  })
  .step(({id, pred, delay, newDelay, dt, now, t0, minDelay, minDelay0, Ts, Pred, Runs, ReadyAt, schedules, cancels, executes, updates}) => {
    // the predecessor this schedule binds into the id
    const bound = pred.match({none: () => 0, some: k => k.plus(1)})
    const t = t0.plus(now).plus(dt)
    const md = minDelay.match({none: () => minDelay0, some: v => v})
    return {
      now: now.plus(dt),
      // :453 _minDelay = newDelay.
      minDelay: optional(updates.or(minDelay.isSome), when(updates, newDelay, md)),
      // :322 _timestamps[id] = block.timestamp + delay; :339 delete; :434 _afterCall: DONE.
      Ts: Ts.set(id, when(schedules, t.plus(delay), when(cancels, 0, when(executes, DONE, Ts.at(id))))),
      Pred: Pred.set(id, when(schedules, bound, Pred.at(id))),
      Runs: Runs.set(id, when(executes, Runs.at(id).plus(1), Runs.at(id))),
      ReadyAt: ReadyAt.set(id, when(schedules, t.plus(md), ReadyAt.at(id))),
    }
  })

const r = timelock()
export const items: RealItem[] = [{
  id: 'approval/openzeppelin/TimelockController',
  domain: 'approval',
  source: {...src, path: 'contracts/governance/TimelockController.sol', lines: '115-454', export: 'TimelockController'},
  summary: 'A proposer schedules an operation with at least the minimum delay; once ready (and its predecessor done) an executor runs it once; a canceller may cancel it while pending.',
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'roles are fixed for a run (one proposer, who is also the canceller; one executor or the open role): AccessControl grants and revocations by the admin are left out'},
    {gap: 'external', blocks: 'part', detail: 'the operation\'s calls (and any reentrancy into the timelock from them) are not run; updateDelay is a request from `self`, which on chain only an executed operation can make'},
  ],
  laws: [
    invariant(r, r.law('every operation executes at most once', ({Runs}) => forall(k => Runs.at(k).atMost(1))),
      'safety', 'docs', 'TimelockController.sol:430-434 _afterCall marks the operation DONE; :418-421 only a ready operation executes'),
    stepLaw(r, r.stepLaw('an operation executes no sooner than the minimum delay after it was scheduled', ({id, ReadyAt, t0}, after) => after.now.plus(t0).atLeast(ReadyAt.at(id)),
      ({executes}) => executes),
    'step', 'docs', 'TimelockController.sol:221-223 "the minimum delay in seconds for an operation to become valid"'),
    stepLaw(r, r.stepLaw("an operation executes only after its predecessor is done", ({id, Pred}, after) => Pred.at(id).eq(0).or(after.Ts.at(Pred.at(id).minus(1)).eq(DONE)),
      ({executes}) => executes),
    'step', 'docs', 'TimelockController.sol:422-424 TimelockUnexecutedPredecessor'),
    stepLaw(r, r.stepLaw('a cancelled or unscheduled operation never executes', ({id, Runs}, after) => after.Runs.at(id).eq(Runs.at(id)),
      ({id, Ts}) => Ts.at(id).eq(0)),
    'step', 'docs', 'TimelockController.sol:326-339 cancel deletes the timestamp; :419 execution needs Ready'),
    stepLaw(r, r.stepLaw('only the executor executes, unless the role is open', ({sender, executor, open}) => sender.eq(executor).or(open),
      ({executes}) => executes),
    'access', 'docs', 'TimelockController.sol:351 "the caller must have the \'executor\' role"; :140-153 onlyRoleOrOpenRole'),
    stepLaw(r, r.stepLaw('only the proposer schedules', ({sender, proposer, id, Ts}, after) => after.Ts.at(id).eq(Ts.at(id)).or(sender.eq(proposer)),
      ({op}) => op.is('schedule')),
    'access', 'docs', 'TimelockController.sol:261 "the caller must have the \'proposer\' role"'),
    leadsTo(r, r.leadsTo('every scheduled operation becomes ready', {
      from: ({Ts, now, t0, d}) => Ts.at(d).gt(t0.plus(now)),
      to: ({Ts, now, t0, d}) => Ts.at(d).atMost(t0.plus(now)),
      helpful: () => ({op: 4, dt: 1}),
    }), 'docs', 'TimelockController.sol:183-187 isOperationReady; an operation is Waiting until its timestamp, then Ready'),
  ],
}]
