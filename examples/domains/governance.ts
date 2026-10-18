// Elections and governance: one vote per voter, quorum before a decision, a proposal's lifecycle, delegated vote
// weight, the secrecy of a ballot, which ballots count, and runoff rounds.
import {type Term, bool, forall, loop, maybe, nat, no, oneOf, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// One vote per voter: a ballot is counted only if the voter hasn't voted (Voted), and the tally keeps ayes + nays = cast.
// Counted holds how many of a voter's ballots were counted, which the law caps at one.
const ballots = (bug?: 'counts a repeat ballot') => rule('one vote per voter')
  .inputs({voter: nat, choice: oneOf('yes', 'no')})
  .state({ayes: 0, nays: 0, cast: 0})
  .maps({Voted: 0, Counted: 0})
  .flags(({voter, Voted}) => ({fresh: Voted.at(voter).eq(0)}))
  .step(({voter, choice, fresh, ayes, nays, cast, Voted, Counted}) => {
    const counts = bug === 'counts a repeat ballot' ? yes : fresh
    return {
      Voted: Voted.set(voter, 1),
      Counted: Counted.bump(voter, counts),
      ayes: when(counts.and(choice.is('yes')), ayes.plus(1), ayes),
      nays: when(counts.and(choice.is('no')), nays.plus(1), nays),
      cast: when(counts, cast.plus(1), cast),
    }
  })
const ballotLaws = (r: ReturnType<typeof ballots>) => [
  r.law('every voter: at most one ballot counted', ({Counted}) => forall(v => Counted.at(v).atMost(1))),
  r.law('ayes + nays = ballots cast', ({ayes, nays, cast}) => ayes.plus(nays).eq(cast)),
  r.law('a counted ballot means the voter voted', ({Counted, Voted}) => forall(v => Counted.at(v).atMost(Voted.at(v)))),
]

// Quorum: votes are taken until the proposal is closed, and it can be closed only once `quorum` votes are in. A
// decided proposal passed if more than half approved.
const quorum = (bug?: 'closes without quorum' | 'votes after the close') => rule('quorum before a decision')
  .params({quorum: nat})
  .inputs({op: oneOf('vote', 'close'), approve: bool})
  .state({votes: 0, approvals: 0, decided: 0, passed: 0})
  .flags(({op, votes, decided, quorum}) => ({
    votes_: op.is('vote').and(bug === 'votes after the close' ? yes : decided.eq(0)),
    closes: op.is('close').and(decided.eq(0), bug === 'closes without quorum' ? yes : votes.atLeast(quorum)),
  }))
  .step(({approve, votes, approvals, decided, passed, votes_, closes}) => ({
    votes: when(votes_, votes.plus(1), votes),
    approvals: when(votes_.and(approve), approvals.plus(1), approvals),
    decided: when(closes, 1, decided),
    passed: when(closes, when(approvals.times(2).gt(votes), 1, 0), passed),
  }))
const quorumLaws = (r: ReturnType<typeof quorum>) => [
  r.law('a decision has its quorum', ({decided, votes, quorum}) => decided.eq(0).or(votes.atLeast(quorum))),
  r.law('approvals <= votes', ({approvals, votes}) => approvals.atMost(votes)),
  r.law('only a decided proposal has passed', ({passed, decided}) => passed.atMost(decided)),
  r.law('decided is 0 or 1', ({decided}) => decided.atMost(1)),
]
const quorumSteps = (r: ReturnType<typeof quorum>) => [
  r.stepLaw('a decided proposal\'s votes never move', ({decided, votes}, after) => decided.eq(1).implies(after.votes.eq(votes))),
]

// A proposal's lifecycle: draft (0) -> open (1) -> passed (2) -> executed (3), or rejected (4) while open.
const lifecycle = (bug?: 'executes while open' | 'reopens a rejected proposal') => rule('proposal lifecycle')
  .inputs({op: oneOf('open', 'pass', 'reject', 'execute')})
  .state({stage: 0, executions: 0})
  .flags(({op, stage}) => ({
    opens: op.is('open').and(stage.eq(0).or(bug === 'reopens a rejected proposal' ? stage.eq(4) : no)),
    passes: op.is('pass').and(stage.eq(1)),
    rejects: op.is('reject').and(stage.eq(1)),
    executes: op.is('execute').and(bug === 'executes while open' ? stage.eq(1).or(stage.eq(2)) : stage.eq(2)),
  }))
  .step(({stage, executions, opens, passes, rejects, executes}) => ({
    stage: when(opens, 1, when(passes, 2, when(rejects, 4, when(executes, 3, stage)))),
    executions: when(executes, executions.plus(1), executions),
  }))
const lifecycleLaws = (r: ReturnType<typeof lifecycle>) => [
  r.law('stage <= 4', ({stage}) => stage.atMost(4)),
  r.law('executed at most once', ({executions}) => executions.atMost(1)),
  r.law('an execution means the stage is executed', ({executions, stage}) => executions.eq(0).or(stage.eq(3))),
]
const lifecycleSteps = (r: ReturnType<typeof lifecycle>) => [
  r.stepLaw('an executed proposal stays executed', ({stage}, after) => stage.eq(3).implies(after.stage.eq(3))),
  r.stepLaw('only a passed proposal is executed', ({stage}, after) => after.stage.eq(3).implies(stage.eq(2).or(stage.eq(3)))),
  r.stepLaw('a rejected proposal stays rejected', ({stage}, after) => stage.eq(4).implies(after.stage.eq(4))),
  r.stepsLaw('two steps from a draft never execute', 2, ({stage}, after) => stage.eq(0).implies(after.stage.ne(3))),
]

// Delegated weight: a voter delegates to another, adding one to the delegate's weight while it is under `cap`;
// undelegating takes it back from the delegate recorded at the time.
const delegation = (bug?: 'cap off by one') => rule('delegated vote weight')
  .params({cap: nat})
  .inputs({op: oneOf('delegate', 'undelegate'), from: nat, to: nat})
  .maps({Weight: 0, Given: 0, To: 0})
  .flags(({op, from, to, cap, Weight, Given}) => ({
    gives: op.is('delegate').and(Given.at(from).eq(0), bug === 'cap off by one' ? Weight.at(to).atMost(cap) : Weight.at(to).lt(cap)),
    takes: op.is('undelegate').and(Given.at(from).eq(1)),
  }))
  .step(({op, from, to, gives, takes, Weight, Given, To}) => {
    // the delegate touched: the new one on a delegation, the recorded one on an undelegation (a key reads no flag)
    const k = when(op.is('delegate'), to, To.at(from))
    return {
    Weight: Weight.set(k, when(gives, Weight.at(k).plus(1), when(takes, Weight.at(k).minus(1), Weight.at(k)))),
    Given: Given.set(from, when(gives, 1, when(takes, 0, Given.at(from)))),
    To: To.set(from, when(gives, to, To.at(from))),
    }
  })
const delegationLaws = (r: ReturnType<typeof delegation>) => [
  r.law('every delegate: weight <= cap', ({Weight, cap}) => forall(d => Weight.at(d).atMost(cap))),
  r.law('every voter delegates at most once', ({Given}) => forall(v => Given.at(v).atMost(1))),
]

// Publishing a district's tally: it is published when turnout reaches the threshold (so few voters can't be singled
// out), and the decision must not depend on how any one ballot went.
const publication = rule('publishing a district tally')
  .params({threshold: nat})
  .inputs({district: nat, turnout: nat, choice: upTo(1)})
const published = ({turnout, threshold, choice}: {turnout: Term, threshold: Term, choice: Term}, leaks = false) =>
  leaks ? turnout.atLeast(threshold).or(choice.eq(1).and(turnout.plus(1).atLeast(threshold))) : turnout.atLeast(threshold)
const publicationDecisions = [
  publication.relate('a ballot\'s choice never changes whether its district is published', (a, b) => [a.district.eq(b.district), a.turnout.eq(b.turnout)],
    (a, b) => published(a).iff(published(b))),
  publication.decide('a district below the threshold is never published', ({turnout, threshold}) => turnout.lt(threshold), env => published(env).not()),
]
const publicationBroken = [
  {name: 'publishes on a yes', why: 'a district one voter short of the threshold is published when the ballot read was a yes',
    decision: publication.relate('a ballot\'s choice never changes whether its district is published', (a, b) => [a.district.eq(b.district), a.turnout.eq(b.turnout)],
      (a, b) => published(a, true).iff(published(b, true)))},
]

// Which ballots count: in person always; by mail only with a postmark by election day and a matching signature; a
// missing postmark or signature check means the ballot is set aside, never counted.
const validity = rule('which ballots count')
  .params({electionDay: upTo(400)})
  .inputs({method: oneOf('in person', 'mail'), postmark: maybe(upTo(400)), signature: maybe(bool)})
type Env = Parameters<Parameters<typeof validity.decide>[2]>[0]
const counts = ({method, postmark, signature, electionDay}: Env, lateOk = false) => method.match({
  'in person': () => yes,
  mail: () => postmark.match({none: () => no, some: p => (lateOk ? p.atMost(electionDay.plus(3)) : p.atMost(electionDay))})
    .and(signature.match({none: () => no, some: s => s})),
})
const validityDecisions = [
  validity.decide('a mail ballot without a postmark is never counted', ({method, postmark}) => [method.is('mail'), postmark.isNone], env => counts(env).not()),
  validity.decide('a mail ballot postmarked after election day is never counted', ({method, postmark, electionDay}) => [method.is('mail'), postmark.match({none: () => no, some: p => p.gt(electionDay)})], env => counts(env).not()),
  validity.decide('an in-person ballot always counts', ({method}) => method.is('in person'), env => counts(env)),
]
const validityBroken = [
  {name: 'counts late mail', why: 'a grace period lets mail postmarked three days after election day count',
    decision: validity.decide('a mail ballot postmarked after election day is never counted', ({method, postmark, electionDay}) => [method.is('mail'), postmark.match({none: () => no, some: p => p.gt(electionDay)})], env => counts(env, true).not())},
]

// Runoff rounds: each round eliminates at least one candidate (and never the last), until one remains.
const runoff = (bug?: 'a round may eliminate no one') => {
  const base = loop('runoff rounds')
    .params({candidates: nat})
    .inputs({eliminated: nat})
    .state({left: ({candidates}) => candidates, rounds: 0})
    .while(({left}) => left.gt(1))
    .body(({left, rounds, eliminated}) => ({left: left.minus(eliminated), rounds: rounds.plus(1)}))
    .pre(({candidates}) => candidates.atLeast(1))
    .rank(({left}) => left)
  return bug === 'a round may eliminate no one' ? base.assume(({eliminated, left}) => eliminated.lt(left)) : base.assume(({eliminated, left}) => eliminated.atLeast(1).and(eliminated.lt(left)))
}
const runoffLaws = (l: ReturnType<typeof runoff>) => [
  l.law('at least one candidate remains', ({left}) => left.atLeast(1)),
  l.law('left <= candidates', ({left, candidates}) => left.atMost(candidates)),
]

const ballotsRepeat = ballots('counts a repeat ballot')
const quorumEarly = quorum('closes without quorum'), quorumLate = quorum('votes after the close')
const lifecycleOpen = lifecycle('executes while open'), lifecycleReopen = lifecycle('reopens a rejected proposal')
const delegationOff = delegation('cap off by one')
const runoffStall = runoff('a round may eliminate no one')

export const domain: Domain = {
  domain: 'governance',
  about: 'one vote per voter, quorum, proposal lifecycle, delegation caps, tally publication, ballot validity, runoff rounds',
  cases: [
    machineCase('one vote per voter', 'each voter\'s ballot is counted once, and the tally adds up', ballots(), ballotLaws(ballots()), [
      {name: 'counts a repeat ballot', why: 'the tally counts every ballot received, and the voted mark only blocks nothing', rule: ballotsRepeat, laws: ballotLaws(ballotsRepeat)},
    ]),
    machineCase('quorum before a decision', 'a proposal is decided only with its quorum, and its votes freeze once decided', quorum(), quorumLaws(quorum()), [
      {name: 'closes without quorum', why: 'the close forgets to check the vote count', rule: quorumEarly, laws: quorumLaws(quorumEarly), steps: quorumSteps(quorumEarly)},
      {name: 'votes after the close', why: 'a vote is taken after the decision, changing a closed count', rule: quorumLate, laws: quorumLaws(quorumLate), steps: quorumSteps(quorumLate)},
    ], {steps: quorumSteps(quorum())}),
    machineCase('proposal lifecycle', 'draft, open, passed, executed or rejected: executed and rejected are final', lifecycle(), lifecycleLaws(lifecycle()), [
      {name: 'executes while open', why: 'execution is allowed before the vote passes', rule: lifecycleOpen, laws: lifecycleLaws(lifecycleOpen), steps: lifecycleSteps(lifecycleOpen)},
      {name: 'reopens a rejected proposal', why: 'a rejected proposal can be opened again', rule: lifecycleReopen, laws: lifecycleLaws(lifecycleReopen), steps: lifecycleSteps(lifecycleReopen)},
    ], {steps: lifecycleSteps(lifecycle())}),
    machineCase('delegated vote weight', 'no delegate holds more than `cap` delegated votes, and each voter delegates once', delegation(), delegationLaws(delegation()), [
      {name: 'cap off by one', why: 'a delegation is taken at weight = cap', rule: delegationOff, laws: delegationLaws(delegationOff)},
    ]),
    decisionCase('publishing a district tally', 'publication depends on turnout, never on a single ballot', publicationDecisions, publicationBroken),
    decisionCase('which ballots count', 'mail ballots need a postmark by election day and a signature check; missing facts never count', validityDecisions, validityBroken),
    loopCase('runoff rounds', 'every round eliminates someone and never the last candidate, so the runoff ends', runoff(), runoffLaws(runoff()), [
      {name: 'a round may eliminate no one', why: 'a round with no elimination repeats forever', loop: runoffStall, laws: runoffLaws(runoffStall)},
    ]),
  ],
}
