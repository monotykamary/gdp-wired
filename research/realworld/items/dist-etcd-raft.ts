// etcd-io/raft (go.etcd.io/raft/v3) at c51f010, three parts of one node: the log's append and commit (log.go raftLog:
// maybeAppend, findConflict, append, commitTo, maybeCommit, appliedTo, matchTerm, term), the term and vote handling of
// Step with the election ticks and role changes (raft.go), and the candidate's tally (tracker.go RecordVote, TallyVotes;
// quorum/majority.go VoteResult). Apache-2.0, (c) The etcd Authors.
// https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/log.go
//
// Mapping:
// - The log is MemoryStorage's with no snapshot: the dummy entry at index 0 (term 0), firstIndex 1, so term(i) is the
//   entry's term for i <= lastIndex and ErrUnavailable past it (log.go:387-413). `Term[i]` is entry i's term, `last`
//   lastIndex(); a truncation clears the cells it drops. unstable/stable is one log here (stableTo is left out).
// - A panic (logger.Panicf) stops the node: `dead` is set and no later request changes anything.
// - A MsgApp carries at most one entry (scope): its prev (index, term), the entry's term and the leader's commit.
// - Messages are sent in as requests, one Step each; the network delivers any of them in any order (a message's
//   fields are the request's). isUpToDate (log.go:442-445) is an input: it reads the log, which this part leaves out.
import {bool, forall, min, nat, oneOf, rule, upTo, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'etcd-io/raft', commit: 'c51f010c851edd0dada5af41bafbf68e54617767', licence: 'Apache-2.0', author: 'The etcd Authors', language: 'Go'}
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})

// ------------------------------------------------------------------------------------------------- the log
export const raftLog = () => rule('etcd raft raftLog')
  // `app`: maybeAppend(a, committed) for a MsgApp (raft.go handleAppendEntries); `append`: the leader's own append at
  // lastIndex + 1 (raft.go appendEntry); `commit`: maybeCommit(at) with the quorum's index (raft.go maybeCommit);
  // `apply`: appliedTo(i) for a MsgStorageApplyResp.
  .inputs({op: oneOf('app', 'append', 'commit', 'apply'), prev: nat, prevTerm: nat, n: upTo(1), eterm: nat, lcommit: nat, at: nat, atTerm: nat})
  .state({last: 0, committed: 0, applied: 0, dead: bool.from(false)})
  .maps({Term: 0})
  .flags(({op, prev, prevTerm, n, eterm, lcommit, at, atTerm, last, committed, applied, dead, Term}) => {
    // matchTerm (log.go:447-453): term(i) == t, false where term errs (i > lastIndex).
    const match = (i: typeof prev, t: typeof prev) => i.atMost(last).and(Term.at(i).eq(t))
    const live = dead.not()
    // maybeAppend (log.go:109-131): no match at prev: (0, false), nothing changes.
    const ok = live.and(op.is('app'), match(prev, prevTerm))
    // findConflict (log.go:154-180): the one entry, at prev + 1, not matching.
    const conflict = ok.and(n.eq(1), match(prev.plus(1), eterm).not())
    // :120-121 a conflict at or below committed panics; append's own check (:137-139, after < committed) never fires
    // past it (after = ci - 1 >= committed).
    const clash = conflict.and(prev.plus(1).atMost(committed))
    const trunc = conflict.and(clash.not())
    const last1 = when(trunc, prev.plus(1), last)
    // :130 commitTo(min(committed, lastnewi)); commitTo (:322-330) panics past lastIndex.
    const toc = min(lcommit, prev.plus(n))
    const appCommits = ok.and(clash.not(), committed.lt(toc))
    const appPanics = appCommits.and(last1.lt(toc))
    // maybeCommit (:455-464): term not 0, past committed, matching.
    const commits = live.and(op.is('commit'), atTerm.gt(0), at.gt(committed), match(at, atTerm))
    // appliedTo (:332-345): panics outside [applied, committed].
    const applyBad = live.and(op.is('apply'), committed.lt(at).or(at.lt(applied)))
    const applies = live.and(op.is('apply'), applyBad.not())
    return {ok, trunc, clash, appCommits, appPanics, commits, applies, applyBad, appends: live.and(op.is('append'))}
  })
  .step(({prev, eterm, n, lcommit, at, last, committed, applied, dead, Term, ok, trunc, clash, appCommits, appPanics, commits, applies, applyBad, appends}) => {
    const panics = clash.or(appPanics, applyBad)
    const toc = min(lcommit, prev.plus(n))
    return {
      dead: dead.or(panics),
      last: when(panics, last, when(trunc, prev.plus(1), when(appends, last.plus(1), last))),
      Term: Term.each(k => when(panics, Term.at(k),
        when(trunc.and(k.eq(prev.plus(1))).or(appends.and(k.eq(last.plus(1)))), eterm, when(trunc.and(k.gt(prev.plus(1))), 0, Term.at(k))))),
      committed: when(panics, committed, when(ok.and(appCommits), toc, when(commits, at, committed))),
      applied: when(applies, at, applied),
    }
  })

// ------------------------------------------------------------------------------------------------- term and vote
const MT = oneOf('hup', 'vote', 'prevote', 'app', 'won', 'lost', 'other')
const voteBase = () => rule('etcd raft Step: terms and votes')
  // `id`: r.id (not 0, None); `checkQuorum`, `preVote`: Config; `et`: electionTimeout; `promotable`: the node is a
  // voter in its config (raft.go:1938-1941).
  .params({id: nat, checkQuorum: bool, preVote: bool, et: nat, promotable: bool})
  .pre(({id, et}) => id.atLeast(1).and(et.atLeast(1)))
  // A request: a tick (tickElection, tickHeartbeat), or a message of type `mt` with term `mterm` from `from`.
  // `won`/`lost`: the candidate's MsgVoteResp / MsgPreVoteResp that decides the tally (stepCandidate :1663-1683,
  // through poll; the tally itself is the next rule). `app` stands for MsgApp, MsgHeartbeat and MsgSnap from a leader.
  // `force`: the campaignTransfer context. `upToDate`: isUpToDate of the candidate's last entry. `rto`: the random
  // timeout resetRandomizedElectionTimeout draws (in [et, 2·et)). `active`: QuorumActive at a CheckQuorum.
  .inputs({op: oneOf('tick', 'msg'), mt: MT, mterm: nat, from: nat, force: bool, upToDate: bool, rto: nat, active: bool})
  .assume(({rto, et, from}) => rto.atLeast(et).and(rto.lt(et.times(2)), from.gt(0)))
  .state({term: 0, vote: 0, lead: 0, st: oneOf('follower', 'precandidate', 'candidate', 'leader').from('follower'), elapsed: 0, timeout: ({et}) => et})
// Step's term handling and the vote decision, shared by the flags and the step.
type VEnv = Parameters<Parameters<ReturnType<typeof voteBase>['flags']>[0]>[0]
function decide({op, mt, mterm, from, force, upToDate, active, checkQuorum, et, promotable, term, vote, lead, st, elapsed, timeout}: VEnv) {
  const msg = op.is('msg'), local = mt.is('hup').or(mt.is('won'), mt.is('lost'))
  const req = mt.is('vote').or(mt.is('prevote'))
  // Step :1100-1112 the lease: a vote request with a higher term within the election timeout of hearing a leader.
  const inLease = checkQuorum.and(lead.gt(0), elapsed.lt(et))
  const ignored = msg.and(local.not(), mterm.gt(term), req, force.not(), inLease)
  // :1114-1131 a higher term: become a follower at it, except a PreVote (a granted PreVoteResp is `won`, local here).
  const higher = msg.and(local.not(), mterm.gt(term), ignored.not(), mt.is('prevote').not())
  // :1133-1186 a lower term: dropped (the replies change nothing here).
  const lower = msg.and(local.not(), mterm.lt(term))
  const handled = msg.and(ignored.not(), lower.not())
  const term1 = when(higher, mterm, term), vote1 = when(higher, 0, vote)
  const lead1 = when(higher, when(mt.is('app'), from, 0), lead)
  const st1 = when(higher, 'follower', st)
  // :1211-1262 MsgVote / MsgPreVote: canVote, then isUpToDate.
  const canVote = vote1.eq(from).or(vote1.eq(0).and(lead1.eq(0))).or(mt.is('prevote').and(mterm.gt(term1)))
  const grants = handled.and(req, canVote, upToDate)
  // tickElection (:850-860): past the random timeout a promotable follower or candidate campaigns (MsgHup).
  const ticksOut = op.is('tick').and(st.is('leader').not(), promotable, elapsed.plus(1).atLeast(timeout))
  // tickHeartbeat (:862-890): the leader's CheckQuorum every electionTimeout; without a quorum active, step down.
  const checks = op.is('tick').and(st.is('leader'), elapsed.plus(1).atLeast(et))
  // hup (:973-995): not a leader, promotable (pending conf changes left out).
  const hups = ticksOut.or(handled.and(mt.is('hup'))).and(st.is('leader').not(), promotable)
  return {higher, handled, term1, vote1, lead1, st1, grants, ticksOut, checks, hups, stepsDown: checks.and(checkQuorum, active.not()), inLease, ignored}
}
export const raftVote = () => voteBase()
  .flags(env => {
    const d = decide(env)
    return {higher: d.higher, handled: d.handled, grants: d.grants, ticksOut: d.ticksOut, checks: d.checks, hups: d.hups, stepsDown: d.stepsDown, inLease: d.inLease, ignored: d.ignored}
  })
  .step(env => {
    const {op, mt, mterm, from, rto, id, preVote, lead, st, elapsed, timeout} = env
    const {higher, handled, term1, vote1, lead1, st1, grants, ticksOut, checks, hups, stepsDown} = decide(env)
    // campaign (:1025-1073): pre-vote first where enabled (becomePreCandidate: term and vote kept, lead None), else
    // becomeCandidate (reset(term + 1): vote None, then Vote = id). A precandidate that wins campaigns for real.
    const pre = hups.and(preVote)
    const real = hups.and(preVote.not()).or(handled.and(mt.is('won'), st1.is('precandidate')))
    const leads = handled.and(mt.is('won'), st1.is('candidate'))
    // stepCandidate: a lost tally, or a MsgApp at the term: becomeFollower(term, from or None).
    const follows = handled.and(mt.is('lost'), st1.is('precandidate').or(st1.is('candidate')))
      .or(handled.and(mt.is('app'), mterm.eq(term1), st1.is('precandidate').or(st1.is('candidate'))))
    const appFromLeader = handled.and(mt.is('app'), mterm.eq(term1), st1.is('follower'))
    const resets = higher.or(real, leads, follows, stepsDown) // reset(): elapsed 0, a new random timeout
    const termN = when(real, term1.plus(1), term1)
    return {
      term: termN,
      vote: when(real, id, when(grants.and(mt.is('vote')), from, vote1)),
      lead: when(real.or(pre).or(stepsDown), 0, when(leads, id, when(follows.or(appFromLeader), when(mt.is('app'), from, 0), lead1))),
      st: when(real, 'candidate', when(pre, 'precandidate', when(leads, 'leader', when(follows.or(stepsDown), 'follower', st1)))),
      // :1253 a real vote resets the election timer; a heartbeat or append from the leader too (stepFollower).
      elapsed: when(resets.or(grants.and(mt.is('vote')), appFromLeader, ticksOut, checks), 0, when(op.is('tick'), elapsed.plus(1), elapsed)),
      timeout: when(resets, rto, timeout),
    }
  })

// ------------------------------------------------------------------------------------------------- the tally
export const raftTally = () => rule('etcd raft candidate tally')
  // `n`: the voters, ids 1..n (a MajorityConfig, tracker.go Voters).
  .params({n: nat})
  // RecordVote(id, v) (tracker.go:265-271) for a vote response from voter `id`, or ResetVotes (a new campaign).
  .inputs({op: oneOf('record', 'reset'), id: nat, granted: bool})
  .assume(({id, n}) => id.atLeast(1).and(id.atMost(n)))
  .state({yes: 0, no: 0})
  // Votes: none (missing), a grant or a rejection.
  .maps({V: oneOf('none', 'yes', 'no').from('none')})
  .flags(({op, id, V}) => ({records: op.is('record').and(V.at(id).is('none'))}))
  .step(({op, id, granted, yes, no, V, records}) => ({
    V: V.each(k => when(op.is('reset'), 'none', when(records.and(k.eq(id), granted), 'yes', when(records.and(k.eq(id)), 'no', V.at(k))))),
    // TallyVotes (:273-289) counts them; kept as two counts the step moves as RecordVote fills a cell.
    yes: when(op.is('reset'), 0, when(records.and(granted), yes.plus(1), yes)),
    no: when(op.is('reset'), 0, when(records.and(granted.not()), no.plus(1), no)),
  }))

const L = raftLog(), V = raftVote(), T = raftTally()
export const items: RealItem[] = [{
  id: 'distributed/etcd-raft/raftLog',
  domain: 'distributed',
  source: cite('log.go', '109-180,322-345,447-464', 'raftLog.maybeAppend, append, findConflict, commitTo, appliedTo, matchTerm, maybeCommit'),
  also: [cite('log.go', '24-56,387-413', 'raftLog (fields and invariants), term'), cite('raft.go', '1938-1941', 'appendEntry (the leader appends at lastIndex + 1)')],
  summary: 'A Raft node\'s log: a MsgApp is accepted only where the log matches the leader\'s at the previous index, conflicting uncommitted entries are truncated, the commit index follows the leader\'s and the quorum\'s, never down and never past the log, and the applied index trails it.',
  expressible: 'partial',
  gaps: [
    {gap: 'scope', blocks: 'part', detail: 'one entry per MsgApp; no snapshot or compaction (firstIndex 1); the unstable/stable split, entry sizes and the applying index left out'},
    {gap: 'batch', blocks: 'part', detail: 'a MsgApp\'s entries are appended as one (truncateAndAppend); taken one entry at a time'},
  ],
  laws: [
    invariant(L, L.law('the commit index never passes the last index', ({committed, last}) => committed.atMost(last)), 'safety', 'docs', 'log.go:326 commitTo panics "tocommit(%d) is out of range [lastIndex(%d)]. Was the raft log corrupted, truncated, or lost?"'),
    invariant(L, L.law('the applied index never passes the commit index', ({applied, committed}) => applied.atMost(committed)), 'safety', 'docs', 'log.go:47 "Invariant: applied <= committed"'),
    stepLaw(L, L.stepLaw('the commit index never decreases', ({committed}, after) => committed.atMost(after.committed)), 'step', 'docs', 'log.go:323 commitTo "never decrease commit"'),
    stepLaw(L, L.stepLaw('a committed entry is never overwritten', ({committed, Term}, after) => forall(k => k.atMost(committed).implies(after.Term.at(k).eq(Term.at(k))))),
      'safety', 'docs', 'log.go:120-121 maybeAppend panics "entry %d conflict with committed entry"'),
    stepLaw(L, L.stepLaw('an accepted append leaves the log matching the leader\'s at prev and the new entry', ({prev, prevTerm, n, eterm}, after) =>
      after.Term.at(prev).eq(prevTerm).and(prev.atMost(after.last), n.eq(1).implies(after.Term.at(prev.plus(1)).eq(eterm).and(prev.plus(1).atMost(after.last)))),
    ({ok, clash, appPanics}) => ok.and(clash.not(), appPanics.not())),
    'step', 'docs', 'raft.go handleAppendEntries; the Raft paper\'s consistency check: entries are appended only after the entry at prevLogIndex matches prevLogTerm'),
    stepLaw(L, L.stepLaw('an append that does not match at prev changes nothing', ({last, committed}, after) => after.last.eq(last).and(after.committed.eq(committed)), ({op, dead, ok}) => op.is('app').and(dead.not(), ok.not())),
      'step', 'docs', 'log.go:107-108 "maybeAppend returns (0, false) if the entries cannot be appended"'),
  ],
}, {
  id: 'distributed/etcd-raft/vote',
  domain: 'distributed',
  source: cite('raft.go', '1089-1271', 'raft.Step (term handling, MsgVote, MsgPreVote)'),
  also: [cite('raft.go', '781-1073', 'reset, tickElection, tickHeartbeat, becomeFollower, becomeCandidate, becomePreCandidate, hup, campaign'), cite('raft.go', '1601-1700', 'stepCandidate, stepFollower (MsgApp, MsgHeartbeat)')],
  summary: 'A Raft node\'s term and vote: a higher term makes it a follower with no vote, it votes at most once per term (only for an up-to-date candidate when it knows no leader), a pre-vote changes neither, and with CheckQuorum a node that heard from its leader within the election timeout ignores vote requests (the leader lease).',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'ticks and messages are requests in any order; the tally deciding an election is one request (`won`/`lost`, the next item)'},
    {gap: 'external', blocks: 'part', detail: 'isUpToDate and QuorumActive read the log and the progress tracker: inputs'},
    {gap: 'scope', blocks: 'part', detail: 'leader transfer (MsgTimeoutNow, MsgTransferLeader), learners, pending conf changes, ReadIndex and the messages sent are left out'},
  ],
  laws: [
    stepLaw(V, V.stepLaw('the term never decreases', ({term}, after) => term.atMost(after.term)), 'step', 'docs', 'raft.go:1114-1131: a higher term moves the node to it; lower terms are ignored (the Raft paper: currentTerm increases monotonically)'),
    stepLaw(V, V.stepLaw('a vote cast in a term never changes within it', ({term, vote}, after) => after.term.eq(term).and(vote.gt(0)).implies(after.vote.eq(vote))),
      'safety', 'docs', 'raft.go:1212 "We can vote if this is a repeat of a vote we\'ve already cast..."; the Raft paper: each server votes for at most one candidate in a given term'),
    stepLaw(V, V.stepLaw('a vote for another node is cast only for a candidate at the node\'s term', ({from, mterm}, after) => after.vote.eq(from).implies(after.term.eq(mterm)),
      ({op, mt, vote, id, from}) => op.is('msg').and(mt.is('vote'), from.eq(id).not(), vote.eq(from).not())), 'step', 'docs', 'raft.go:1250-1255 "When responding to Msg{Pre,}Vote messages we include the term from the message"; :1252 Only record real votes'),
    stepLaw(V, V.stepLaw('a pre-vote changes neither the term nor the vote', ({term, vote}, after) => after.term.eq(term).and(after.vote.eq(vote)),
      ({op, mt, mterm, term}) => op.is('msg').and(mt.is('prevote'), mterm.atLeast(term))), 'step', 'docs', 'raft.go:1115 "Never change our term in response to a PreVote"; :1252 "Only record real votes"'),
    stepLaw(V, V.stepLaw('within the leader lease a vote request changes nothing', ({term, vote, lead}, after) => after.term.eq(term).and(after.vote.eq(vote), after.lead.eq(lead)),
      ({ignored}) => ignored), 'safety', 'docs', 'raft.go:1104-1106 "If a server receives a RequestVote request within the minimum election timeout of hearing from a current leader, it does not update its term or grant its vote"'),
    invariant(V, V.law('a candidate or leader has voted for itself', ({st, vote, id}) => st.is('candidate').or(st.is('leader')).implies(vote.eq(id))), 'safety', 'docs', 'raft.go:910 becomeCandidate "r.Vote = r.id"; the Raft paper: a candidate votes for itself'),
  ],
}, {
  id: 'distributed/etcd-raft/tally',
  domain: 'distributed',
  source: cite('quorum/majority.go', '180-197', 'MajorityConfig.VoteResult'),
  also: [cite('tracker/tracker.go', '258-289', 'ProgressTracker.ResetVotes, RecordVote, TallyVotes')],
  summary: 'A candidate\'s tally: each voter\'s first response counts, and the election is won at a majority of grants (n/2 + 1), lost once the grants and the missing votes can\'t reach it.',
  expressible: 'partial',
  gaps: [
    {gap: 'unbounded-collection', blocks: 'part', detail: 'TallyVotes and VoteResult count the map\'s cells in a loop; the rule keeps the two counts as the step moves them'},
    {gap: 'scope', blocks: 'part', detail: 'joint configurations (JointConfig.VoteResult) and learners left out; voters are ids 1..n'},
  ],
  laws: [
    invariant(T, T.law('the grants and rejections never outnumber the voters', ({yes, no, n}) => yes.plus(no).atMost(n)), 'safety', 'inferred', 'tracker.go:265-271 RecordVote records a voter\'s first response only'),
    invariant(T, T.law('an election won and lost at once is impossible', ({yes, no, n}) => yes.times(2).gt(n).and(n.minus(no).times(2).atMost(n)).not()), 'safety', 'docs', 'majority.go:180-197 VoteResult: VoteWon at q grants, VoteLost when grants plus missing are below q'),
    stepLaw(T, T.stepLaw('a recorded vote is never changed by a later response', ({V, id}, after) => forall(k => V.at(k).is('none').not().implies(after.V.at(k).eq(V.at(k)))), ({op}) => op.is('record')),
      'step', 'docs', 'tracker.go:266-270 "_, ok := p.Votes[id]; if !ok { p.Votes[id] = v }"'),
    stepLaw(T, T.stepLaw('a won election stays won as responses arrive', ({n}, after) => after.yes.times(2).gt(n), ({op, yes, n}) => op.is('record').and(yes.times(2).gt(n))),
      'step', 'inferred', 'majority.go:189-191 votedCnt >= q is VoteWon; a recorded vote never changes'),
  ],
}]
