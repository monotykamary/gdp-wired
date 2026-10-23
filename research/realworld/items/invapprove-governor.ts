// OpenZeppelin Contracts v5.7.0: Governor with GovernorCountingSimple and GovernorTimelockControl, one proposal and its
// operation on the TimelockController. MIT, (c) OpenZeppelin.
// https://github.com/OpenZeppelin/openzeppelin-contracts/tree/cab19933c33c2ad1d4c7a84864a3601dddfd16f3/contracts/governance
//
// A proposal is created, voted on while Active, Defeated or Succeeded at its deadline, queued on the timelock, and
// executed through it once ready; its proposer may cancel it while Pending. A call that reverts changes nothing, which
// the step says as "every part keeps its value". The Governor's clock (block numbers, ERC-6372) and the timelock's
// (block.timestamp) never go down: each request carries how far each moved. The proposal is one (its id: the hash of
// its calls and description); its timelock operation is the one GovernorTimelockControl schedules for it.
import {type Cond, type Term, bool, forall, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'OpenZeppelin/openzeppelin-contracts', commit: 'cab19933c33c2ad1d4c7a84864a3601dddfd16f3', licence: 'MIT', author: 'OpenZeppelin', language: 'Solidity'}
const gov = 'contracts/governance'

// Governor.sol:141-179 state(), with GovernorTimelockControl.sol:43-60 for a Queued proposal (by its timelock
// operation: pending Queued, done Executed, else Canceled). 'None' is a proposal not yet created (state() reverts).
const STATES = ['None', 'Pending', 'Active', 'Canceled', 'Defeated', 'Succeeded', 'Queued', 'Executed'] as const
type S = typeof STATES[number]
type Proposal = {executed: Cond, canceled: Cond, voteStart: Term, votingPeriod: Term, quorum: Term, forVotes: Term, againstVotes: Term, abstainVotes: Term, eta: Term, Ts: Term}

export const governor = () => rule('OpenZeppelin Governor with a timelock')
  // votingDelay(), votingPeriod() (Governor.sol:805-808, fixed here), quorum(snapshot) (the quorum at the proposal's
  // snapshot: GovernorVotesQuorumFraction checkpoints it), proposalThreshold() (:181), the timelock's minDelay;
  // `others`: the timelock has a proposer and canceller besides the governor (`other`), the setup
  // GovernorTimelockControl.sol:19-22 warns against; `open`: the timelock's executor role is open to anyone; `b0`,
  // `t0`: the block number and timestamp at deployment.
  .params({votingDelay: nat, votingPeriod: nat, quorum: nat, threshold: nat, minDelay: nat, others: bool, other: nat, open: bool, b0: nat, t0: nat})
  .pre(({t0, b0}) => t0.atLeast(2).and(b0.atLeast(1)))
  // One call: which function (`tl*`: a call made straight to the timelock), msg.sender, the voter's support, the
  // weight getVotes returns (an ERC20Votes checkpoint read at the snapshot: an input), and the clocks' moves.
  .inputs({op: oneOf('propose', 'vote', 'queue', 'execute', 'cancel', 'tlSchedule', 'tlExecute', 'tlCancel', 'wait'), sender: nat, support: oneOf('against', 'for', 'abstain'), weight: nat, db: nat, dt: nat})
  // Governor.sol ProposalCore: proposer, voteStart (0: no proposal), executed, canceled, etaSeconds;
  // GovernorCountingSimple.sol ProposalVote's tallies; the timelock's _timestamps for the operation (0 unset, 1 done).
  // `bn`, `ts`: the clocks since deployment. Ghosts: `runs`, how many times the proposal's calls were made.
  .state({bn: 0, ts: 0, proposer: 0, voteStart: 0, executed: bool.from(false), canceled: bool.from(false), eta: 0,
    againstVotes: 0, forVotes: 0, abstainVotes: 0, Ts: 0, runs: 0})
  // GovernorCountingSimple.sol:18-24 hasVoted; `Counted`: ballots counted per account (ghost).
  .maps({HasVoted: bool.from(false), Counted: 0})
  .flags(env => {
    const {op, sender, weight, db, dt, b0, t0, threshold, others, other, open, proposer, voteStart, Ts, HasVoted} = env
    const now = b0.plus(env.bn).plus(db), t = t0.plus(env.ts).plus(dt)
    const st = stateAt(env, now)
    const pending = Ts.gt(1), ready = pending.and(Ts.atMost(t))
    return {
      // The proposal's state when the call runs (at the request's block).
      atPending: st.Pending, atActive: st.Active, atQueued: st.Queued, atCanceled: st.Canceled,
      // Governor.sol:274-297 propose: getVotes(proposer, clock() - 1) >= proposalThreshold() when positive; :316 a
      // proposal that exists reverts.
      proposes: op.is('propose').and(threshold.eq(0).or(weight.atLeast(threshold)), voteStart.eq(0)),
      // :633-650 _castVote: Active; GovernorCountingSimple.sol:72-75 one vote per account.
      votes: op.is('vote').and(st.Active, HasVoted.at(sender).not()),
      // :344-366 queue: Succeeded; GovernorTimelockControl.sol:81-93 schedules on the timelock (TimelockController.sol
      // :314-322: the operation must be unset; the delay is the minimum, so it suffices); eta = block.timestamp + delay.
      queues: op.is('queue').and(st.Succeeded, Ts.eq(0)),
      // :395-428 execute: Queued; GovernorTimelockControl.sol:99-110 executeBatch: TimelockController.sol:418-421 ready.
      executes: op.is('execute').and(st.Queued, ready),
      // :454-467 cancel: _validateCancel (:793-795) Pending and the proposer; :477-497 _cancel: not Canceled, Expired,
      // or Executed; GovernorTimelockControl.sol:121-138 cancels the timelock operation if it was queued (not while Pending).
      cancels: op.is('cancel').and(st.Pending, sender.eq(proposer)),
      // TimelockController.sol:289-312 scheduleBatch by another proposer of the same operation (same calls and salt),
      // :383-408 executeBatch by an executor (the open role, or the other account), :332-340 cancel by another canceller.
      tlSchedules: op.is('tlSchedule').and(others, sender.eq(other), Ts.eq(0)),
      tlExecutes: op.is('tlExecute').and(open.or(others.and(sender.eq(other))), ready),
      tlCancels: op.is('tlCancel').and(others, sender.eq(other), pending),
    }
  })
  .step(({support, weight, db, dt, t0, b0, sender, votingDelay, minDelay, bn, ts, proposer, voteStart, executed, canceled, eta,
    againstVotes, forVotes, abstainVotes, Ts, runs, HasVoted, Counted, proposes, votes, queues, executes, cancels, tlSchedules, tlExecutes, tlCancels}) => {
    const now = b0.plus(bn).plus(db), t = t0.plus(ts).plus(dt)
    return {
      bn: bn.plus(db), ts: ts.plus(dt),
      // :320-327 voteStart = clock() + votingDelay(), the proposer.
      proposer: when(proposes, sender, proposer),
      voteStart: when(proposes, now.plus(votingDelay), voteStart),
      // :410 executed = true (before the calls); :493 canceled = true.
      executed: executed.or(executes),
      canceled: canceled.or(cancels),
      eta: when(queues, t.plus(minDelay), eta),
      // GovernorCountingSimple.sol:77-85 the tallies by support.
      againstVotes: when(votes.and(support.is('against')), againstVotes.plus(weight), againstVotes),
      forVotes: when(votes.and(support.is('for')), forVotes.plus(weight), forVotes),
      abstainVotes: when(votes.and(support.is('abstain')), abstainVotes.plus(weight), abstainVotes),
      // The timelock operation: scheduled at t + minDelay (by the governor's queue or another proposer), done, deleted.
      Ts: when(queues.or(tlSchedules), t.plus(minDelay), when(executes.or(tlExecutes), 1, when(tlCancels, 0, Ts))),
      runs: when(executes.or(tlExecutes), runs.plus(1), runs),
      HasVoted: HasVoted.set(sender, HasVoted.at(sender).or(votes)),
      Counted: Counted.set(sender, when(votes, Counted.at(sender).plus(1), Counted.at(sender))),
    }
  })

// The proposal's state at Governor clock `now`, one condition per state (a Queued proposal's timelock operation is
// read as it stands: GovernorTimelockControl asks isOperationPending / isOperationDone, which do not depend on the time).
function stateAt(e: Proposal, now: Term): Record<S, Cond> {
  const {executed, canceled, voteStart, votingPeriod, quorum, forVotes, againstVotes, abstainVotes, eta, Ts} = e
  const exists = voteStart.gt(0)
  const live = executed.not().and(canceled.not(), exists)
  const pending = live.and(voteStart.atLeast(now))
  const active = live.and(voteStart.lt(now), voteStart.plus(votingPeriod).atLeast(now))
  const closed = live.and(voteStart.plus(votingPeriod).lt(now))
  // GovernorCountingSimple.sol:57-70 quorum on for + abstain; for strictly over against.
  const wins = quorum.atMost(forVotes.plus(abstainVotes)).and(forVotes.gt(againstVotes))
  const queued = closed.and(wins, eta.gt(0))
  return {
    None: exists.not().and(executed.not(), canceled.not()),
    Pending: pending,
    Active: active,
    Canceled: canceled.and(executed.not()).or(queued.and(Ts.gt(1).not(), Ts.eq(1).not())),
    Defeated: closed.and(wins.not()),
    Succeeded: closed.and(wins, eta.eq(0)),
    Queued: queued.and(Ts.gt(1)),
    Executed: executed.or(queued.and(Ts.eq(1))),
  }
}

const r = governor()
const st = (e: Proposal & {b0: Term, bn: Term}) => stateAt(e, e.b0.plus(e.bn))
const cite = (file: string, lines: string, exp: string) => ({...src, path: `${gov}/${file}`, lines, export: exp})
export const items: RealItem[] = [{
  id: 'approval/openzeppelin/Governor',
  domain: 'approval',
  source: cite('Governor.sol', '141-660', 'Governor'),
  also: [cite('extensions/GovernorCountingSimple.sol', '40-96', 'GovernorCountingSimple'), cite('extensions/GovernorTimelockControl.sol', '40-138', 'GovernorTimelockControl'),
    cite('TimelockController.sol', '289-434', 'TimelockController')],
  summary: 'A proposal is Pending until its snapshot, Active until its deadline, then Defeated or Succeeded by quorum and for > against; a Succeeded proposal is queued on the timelock and executed through it once ready; the proposer may cancel while Pending.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'vote weights (ERC20Votes checkpoints at the snapshot) and the quorum at the snapshot are inputs and a param; the proposal\'s calls are not run (reentrancy, relay and onlyGovernance calls are left out)'},
    {gap: 'unbounded-collection', blocks: 'part', detail: 'one proposal: proposals are independent records keyed by id, so laws about one hold for each'},
    {gap: 'other', blocks: 'part', detail: 'votingDelay, votingPeriod, minDelay and the timelock\'s roles are fixed for a run (settings changed only by governance proposals)'},
  ],
  laws: [
    // Stated first for every setup ("a proposal's calls run only after it succeeded and was queued"), these two laws
    // were refuted: another timelock proposer schedules the proposal's operation (same calls and salt) and an executor
    // runs it while the proposal is Pending, or after the proposer canceled it (GovernorTimelockControl's _cancel only
    // cancels an operation it queued itself). A law error: GovernorTimelockControl.sol:19-22 warns that additional
    // proposers or cancelers can "execute operations as the timelock"; the laws hold for the setup it prescribes.
    stepLaw(r, r.stepLaw("with the governor as the timelock's only proposer, a proposal's calls run only after it succeeded and was queued", ({atQueued, others}) => others.not().implies(atQueued), ({executes, tlExecutes}) => executes.or(tlExecutes)),
      'step', 'docs', 'Governor.sol:400-403 execute requires Queued when proposalNeedsQueuing; GovernorTimelockControl.sol:11-12 "adds a delay ... to all successful proposals"'),
    invariant(r, r.law("a proposal's calls run at most once", ({runs}) => runs.atMost(1)),
      'safety', 'docs', 'Governor.sol:409 "mark as executed before calls to avoid reentrancy"'),
    stepLaw(r, r.stepLaw("with the governor as the timelock's only proposer, a canceled proposal's calls never run", ({runs}, after) => after.runs.eq(runs), ({atCanceled, others}) => atCanceled.and(others.not())),
      'step', 'docs', 'Governor.sol:472-475 "A proposal can be cancelled in any state other than Canceled, Expired, or Executed. Once cancelled a proposal can\'t be re-submitted."'),
    invariant(r, r.law('every account is counted at most once', ({Counted}) => forall(k => Counted.at(k).atMost(1))),
      'safety', 'docs', 'GovernorCountingSimple.sol:72-74 GovernorAlreadyCastVote'),
    stepLaw(r, r.stepLaw('only the proposer cancels, and only while pending', ({sender, proposer, atPending, canceled}, after) => after.canceled.and(canceled.not()).implies(sender.eq(proposer).and(atPending))),
      'access', 'docs', 'Governor.sol:790-795 "The default implementation allows the proposal proposer to cancel the proposal during the pending state."'),
    stepLaw(r, r.stepLaw('votes are counted only while the vote is active', ({forVotes, againstVotes, abstainVotes}, after) =>
      after.forVotes.eq(forVotes).and(after.againstVotes.eq(againstVotes), after.abstainVotes.eq(abstainVotes)), ({atActive}) => atActive.not()),
    'step', 'docs', 'Governor.sol:640 `_validateStateBitmap(proposalId, _encodeStateBitmap(ProposalState.Active))`'),
    leadsTo(r, r.leadsTo('a queued proposal is eventually executed or canceled', {
      from: e => st(e).Queued,
      to: e => st(e).Executed.or(st(e).Canceled),
      helpful: () => ({op: 3, dt: 1}),
    }), 'docs', 'TimelockController.sol:183-187 a scheduled operation becomes ready; Governor.sol:395 execute is open to anyone'),
  ],
}]
