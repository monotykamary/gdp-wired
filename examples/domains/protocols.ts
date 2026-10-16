// Networking and distributed protocols: sliding windows, leases, election terms, idempotency keys, versioned writes,
// failure detectors, gossip, quorums, retransmission pacing. Each rule takes the bug its broken variant carries.
import {type Bool, type Choice, type Maybe, type Term, bool, forall, loop, maybe, min, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A sliding-window sender: it sends the next sequence number while fewer than `window` are unacknowledged; a cumulative
// ack moves the base forward to `upto` if it acknowledges something new that was actually sent. `lastBase` is the base
// before the last step, so "acks only move forward" is a law.
const sender = (bug?: 'takes future acks' | 'takes stale acks') => rule('sliding window sender')
  .params({window: nat})
  .inputs({op: oneOf('send', 'ack'), upto: nat})
  .state({next: 0, base: 0, lastBase: 0})
  .flags(({op, upto, next, base, window}) => ({
    sent: op.is('send').and(next.lt(base.plus(window))),
    acked: op.is('ack').and(bug === 'takes future acks' ? yes : upto.atMost(next), bug === 'takes stale acks' ? yes : upto.gt(base)),
  }))
  .step(({upto, next, base, sent, acked}) => ({
    next: when(sent, next.plus(1), next),
    base: when(acked, upto, base),
    lastBase: base,
  }))
const senderLaws = [
  sender().law('acked <= sent (base <= next)', ({base, next}) => base.atMost(next)),
  sender().law('unacked <= window', ({next, base, window}) => next.atMost(base.plus(window))),
  sender().law('the base only moves forward', ({lastBase, base}) => lastBase.atMost(base)),
]

// A lease: a client acquires it if it already owns it (a renewal) or the current lease has expired; it then holds it
// until now + duration. A release expires the owner's lease at once. `Expiry` is each client's lease end, `until` the
// latest end handed out. The safety law: every client other than the owner holds an expired lease, so at most one
// client holds a live one.
const lease = (bug?: 'takes over a tick early' | 'release keeps the token') => rule('lease')
  .params({duration: nat})
  .inputs({op: oneOf('acquire', 'release', 'tick'), who: nat})
  .state({owner: 0, until: 0, now: 0})
  .maps({Expiry: 0})
  .flags(({op, who, owner, until, now}) => ({
    granted: op.is('acquire').and(who.eq(owner).or(until.atMost(bug === 'takes over a tick early' ? now.plus(1) : now))),
    dropped: op.is('release').and(who.eq(owner)),
  }))
  .step(({op, who, duration, owner, until, now, Expiry, granted, dropped}) => ({
    owner: when(granted, who, owner),
    until: when(granted, now.plus(duration), when(dropped, now, until)),
    now: when(op.is('tick'), now.plus(1), now),
    Expiry: Expiry.set(who, when(granted, now.plus(duration), when(dropped.and(bug !== 'release keeps the token' ? yes : no), now, Expiry.at(who)))),
  }))
const leaseLaws = [
  lease().law('only the owner holds a live lease', ({Expiry, owner, now}) => forall(c => c.eq(owner).or(Expiry.at(c).atMost(now)))),
  lease().law('every lease ends by until', ({Expiry, until}) => forall(c => Expiry.at(c).atMost(until))),
  lease().law('until <= now + duration', ({until, now, duration}) => until.atMost(now.plus(duration))),
]

// Leader election: a timeout starts a new term; a vote request carries a term t, which the cluster adopts if newer. A
// voter grants a vote in a term newer than its last, or in its last term if it hasn't voted in it yet. `Last` is each
// voter's last term, `Count` its votes in that term.
const election = (bug?: 'votes twice in a term' | 'adopts any term') => rule('leader election')
  .inputs({op: oneOf('timeout', 'vote'), voter: nat, t: nat})
  .state({term: 0, lastTerm: 0})
  .maps({Last: 0, Count: 0})
  .flags(({op, voter, t, Last, Count}) => ({
    granted: op.is('vote').and(bug === 'votes twice in a term' ? t.atLeast(Last.at(voter)) : t.gt(Last.at(voter)).or(t.eq(Last.at(voter)).and(Count.at(voter).eq(0)))),
  }))
  .step(({op, voter, t, term, Last, Count, granted}) => ({
    lastTerm: term,
    term: when(op.is('timeout'), term.plus(1), bug === 'adopts any term' ? t : when(term.lt(t), t, term)),
    Last: Last.set(voter, when(granted, t, Last.at(voter))),
    Count: Count.set(voter, when(granted, when(t.eq(Last.at(voter)), Count.at(voter).plus(1), 1), Count.at(voter))),
  }))
const electionLaws = [
  election().law('the term only increases', ({lastTerm, term}) => lastTerm.atMost(term)),
  election().law('every voter: at most one vote in its term', ({Count}) => forall(v => Count.at(v).atMost(1))),
  election().law('no voter is ahead of the cluster\'s term', ({Last, term}) => forall(v => Last.at(v).atMost(term))),
]

// Idempotency keys: a request id is locked when first seen (0 unseen, 1 in progress, 2 done), its effect is applied
// once on commit, and an abort (the worker died) unlocks it for a retry. A repeat of a done id replays the stored
// response and changes nothing.
const idempotency = (bug?: 'restarts a done key' | 'commits unchecked') => rule('idempotency keys')
  .inputs({op: oneOf('begin', 'commit', 'abort'), id: nat})
  .maps({Status: 0, Applied: 0})
  .flags(({op, id, Status}) => ({
    locked: op.is('begin').and(bug === 'restarts a done key' ? Status.at(id).ne(1) : Status.at(id).eq(0)),
    committed: op.is('commit').and(bug === 'commits unchecked' ? Status.at(id).atLeast(1) : Status.at(id).eq(1)),
    aborted: op.is('abort').and(Status.at(id).eq(1)),
  }))
  .step(({id, Status, Applied, locked, committed, aborted}) => ({
    Status: Status.set(id, when(locked, 1, when(committed, 2, when(aborted, 0, Status.at(id))))),
    Applied: Applied.bump(id, committed),
  }))
const idempotencyLaws = [
  idempotency().law('every id: applied at most once', ({Applied}) => forall(k => Applied.at(k).atMost(1))),
  idempotency().law('every id: applied exactly when done', ({Applied, Status}) => forall(k => Applied.at(k).eq(1).iff(Status.at(k).eq(2)))),
]

// Versioned writes (compare-and-swap): a write names the version it read and is applied only if that is still the
// key's version, which then moves up by one; a stale write is refused. `rev` is the store's revision.
const cas = (bug?: 'lost update') => rule('compare-and-swap')
  .inputs({key: nat, seen: nat, value: nat})
  .state({rev: 0})
  .maps({Version: 0, Writes: 0, Value: 0})
  .flags(({key, seen, Version}) => ({wrote: bug === 'lost update' ? seen.atMost(Version.at(key)) : seen.eq(Version.at(key))}))
  .step(({key, seen, value, rev, Version, Writes, Value, wrote}) => ({
    rev: when(wrote, rev.plus(1), rev),
    Version: Version.set(key, when(wrote, seen.plus(1), Version.at(key))),
    Writes: Writes.bump(key, wrote),
    Value: Value.set(key, when(wrote, value, Value.at(key))),
  }))
const casLaws = [
  cas().law('every key: its version counts its applied writes', ({Version, Writes}) => forall(k => Version.at(k).eq(Writes.at(k)))),
  cas().law('every key: version <= the store\'s revision', ({Version, rev}) => forall(k => Version.at(k).atMost(rev))),
]

// A heartbeat failure detector: a node is declared dead if it announced it left, or if it missed at least 3 checks and
// its last heartbeat (if any) is at least 3 patience periods old; a leader's patience is the timeout, a follower's
// twice it, a learner's four times.
const detector = rule('heartbeat failure detector')
  .params({timeout: nat})
  .inputs({now: nat, lastBeat: maybe(nat), missed: upTo(10), left: bool, role: oneOf('leader', 'follower', 'learner')})
type Seen = {timeout: Term, now: Term, lastBeat: Maybe<Term>, missed: Term, left: Bool, role: Choice<'leader' | 'follower' | 'learner'>}
const patience = ({role, timeout}: Seen) => role.match({leader: () => timeout, follower: () => timeout.times(2), learner: () => timeout.times(4)})
const dead = (env: Seen, bug?: 'forgets silent nodes' | 'one period is enough') => env.left.or(env.missed.atLeast(3).and(env.lastBeat.match({
  none: () => (bug === 'forgets silent nodes' ? no : yes),
  some: b => b.plus(bug === 'one period is enough' ? patience(env) : patience(env).times(3)).atMost(env.now),
})))
const recent = (periods: number) => ({lastBeat, now, timeout}: Seen) => lastBeat.match({none: () => no, some: b => now.lt(b.plus(timeout.times(periods)))})
const detectorDecisions = [
  detector.decide('a heartbeat within the timeout keeps a node alive', env => [env.left.not(), recent(1)(env)], env => dead(env).not()),
  detector.decide('a heartbeat within two timeouts keeps a node alive', env => [env.left.not(), recent(2)(env)], env => dead(env).not()),
  detector.decide('a node never heard from is dead after 3 missed checks', ({lastBeat, missed}) => [lastBeat.isNone, missed.atLeast(3)], env => dead(env)),
]
const silentForgotten = detector.decide('a node never heard from is dead after 3 missed checks (silent nodes forgotten)', ({lastBeat, missed}) => [lastBeat.isNone, missed.atLeast(3)], env => dead(env, 'forgets silent nodes'))
const eagerDeath = detector.decide('a heartbeat within two timeouts keeps a node alive (one period is enough)', env => [env.left.not(), recent(2)(env)], env => dead(env, 'one period is enough').not())

// A gossip round: each turn informs up to `reached` of the uninformed peers; a turn that informs no one spends one unit
// of patience, one that informs someone restores it, and the round ends when everyone knows or patience runs out. The
// tuple rank (uninformed, patience left) drops on every turn.
const gossip = (bug?: 'never gives up' | 'resets patience every turn') => loop(bug ? `gossip round, ${bug}` : 'gossip round')
  .params({peers: nat, patience: nat})
  .inputs({reached: nat})
  .state({uninformed: ({peers}) => peers, informed: 0, idle: ({patience}) => patience})
  .while(({uninformed, idle}) => uninformed.gt(0).and(bug === 'never gives up' ? yes : idle.gt(0)))
  .body(({reached, patience, uninformed, informed, idle}) => {
    const got = min(uninformed, reached)
    return {
      uninformed: uninformed.minus(got),
      informed: informed.plus(got),
      idle: when(got.gt(0).or(bug === 'resets patience every turn' ? yes : no), patience, idle.minus(1)),
    }
  })
  .rank(({uninformed, idle}) => [uninformed, idle])
const gossipLaws = (l: ReturnType<typeof gossip>) => [
  l.law('informed + uninformed = peers', ({informed, uninformed, peers}) => informed.plus(uninformed).eq(peers)),
  l.law('patience left <= patience', ({idle, patience}) => idle.atMost(patience)),
]

// Quorums over n nodes, majorities as constant multiples (2·votes > n): ayes and nays come from distinct nodes.
const quorum = rule('quorum').params({n: nat, f: nat}).inputs({ayes: nat, nays: nat, alive: nat, read: nat, write: nat, overlap: nat})
const quorumDecisions = [
  quorum.decide('commit and abort never both reach a majority', ({ayes, nays, n}) => ayes.plus(nays).atMost(n), ({ayes, nays, n}) => ayes.times(2).gt(n).and(nays.times(2).gt(n)).not()),
  quorum.decide('a majority survives f crashes when n >= 2f + 1', ({alive, f, n}) => [alive.plus(f).atLeast(n), f.times(2).plus(1).atMost(n)], ({alive, n}) => alive.times(2).gt(n)),
  quorum.decide('read and write quorums with r + w > n share a node', ({read, write, overlap, n}) => [read.plus(write).gt(n), read.plus(write).atMost(n.plus(overlap))], ({overlap}) => overlap.atLeast(1)),
]
const responderMajority = quorum.decide('a majority of the responders is a majority', ({ayes, nays, n}) => [ayes.times(2).gt(ayes.plus(nays)), ayes.plus(nays).atMost(n)], ({ayes, n}) => ayes.times(2).gt(n))
const halfIsQuorum = quorum.decide('commit and abort never both reach half', ({ayes, nays, n}) => ayes.plus(nays).atMost(n), ({ayes, nays, n}) => ayes.times(2).atLeast(n).and(nays.times(2).atLeast(n)).not())

// Retransmission pacing: new data always goes out, but retransmitted bytes within one rtt before a send (`resent`, read
// from the log) plus the send itself must stay within the budget. `recent` sums the retransmitted bytes in the rtt
// ending at now; requests come in time order and records older than an rtt are dropped.
const pacing = (bug?: 'window a tick short') => rule('retransmission pacing')
  .params({rtt: nat, budget: nat, now: nat})
  .inputs({retx: bool, bytes: nat, t: nat})
  .log('retx', 'bytes', 't')
  .sums({recent: (r, {now, rtt}) => when(r.retx.and(r.t.atMost(now), now.lt(r.t.plus(rtt))), r.bytes, 0)})
  .queries({resent: (r, {t, rtt}) => when(r.retx.and((bug === 'window a tick short' ? t.plus(1) : t).lt(r.t.plus(rtt))), r.bytes, 0)})
  .flags(({retx, resent, bytes, budget}) => ({paced: retx.not().or(resent.plus(bytes).atMost(budget))}))
  .keep(({paced}) => paced)
  .relations(({t, now, recent, resent}) => [relation(recent.atMost(resent), t.atMost(now))])
  .prune('t', ({rtt}) => rtt)
const pacingLaw = pacing().law('retransmitted bytes in the rtt ending at now <= budget', ({recent, budget}) => recent.atMost(budget))

export const domain: Domain = {
  domain: 'protocols',
  about: 'sliding windows, leases, election terms, idempotency keys, compare-and-swap, failure detectors, gossip, quorums, pacing',
  cases: [
    machineCase('sliding window sender', 'unacknowledged stays within the window, acks never pass what was sent and only move forward', sender(), senderLaws, [
      {name: 'takes future acks', why: 'an ack for a sequence number never sent is taken', rule: sender('takes future acks'), laws: senderLaws},
      {name: 'takes stale acks', why: 'a reordered old ack moves the base back', rule: sender('takes stale acks'), laws: senderLaws},
    ]),
    machineCase('lease', 'at most one client holds a live lease, and no lease outlives its duration', lease(), leaseLaws, [
      {name: 'takes over a tick early', why: 'a clock-skew allowance in the wrong direction grants the lease while the owner\'s is still live', rule: lease('takes over a tick early'), laws: leaseLaws},
      {name: 'release keeps the token', why: 'a release resets the lease but leaves the holder\'s own expiry live', rule: lease('release keeps the token'), laws: leaseLaws},
    ]),
    machineCase('leader election', 'terms only increase, and every voter votes at most once in its term', election(), electionLaws, [
      {name: 'votes twice in a term', why: 'a voter grants any request of its current term, forgetting it already voted', rule: election('votes twice in a term'), laws: electionLaws},
      {name: 'adopts any term', why: 'the cluster takes the term of any request, even an older one', rule: election('adopts any term'), laws: electionLaws},
    ]),
    machineCase('idempotency keys', 'every request id\'s effect is applied at most once, exactly when it is done', idempotency(), idempotencyLaws, [
      {name: 'restarts a done key', why: 'a retry after completion locks the key again and applies the effect twice', rule: idempotency('restarts a done key'), laws: idempotencyLaws},
      {name: 'commits unchecked', why: 'a commit doesn\'t check the key is still in progress', rule: idempotency('commits unchecked'), laws: idempotencyLaws},
    ]),
    machineCase('compare-and-swap', 'stale writes are refused: every key\'s version counts its writes and stays within the revision', cas(), casLaws, [
      {name: 'lost update', why: 'a write based on an older version is taken and sets the version back', rule: cas('lost update'), laws: casLaws},
    ]),
    decisionCase('heartbeat failure detector', 'a recent heartbeat keeps a node alive whatever its role, a silent node is declared dead', detectorDecisions, [
      {name: 'silent nodes forgotten', why: 'a node that never sent a heartbeat is never declared dead', decision: silentForgotten},
      {name: 'one period is enough', why: 'one patience period instead of three declares a leader dead within two timeouts', decision: eagerDeath},
    ]),
    loopCase('gossip round', 'a round ends (the rank: uninformed, then patience left), and every peer is counted once', gossip(), gossipLaws(gossip()), [
      {name: 'never gives up', why: 'with no one reachable the round runs forever once patience is spent', loop: gossip('never gives up'), laws: gossipLaws(gossip('never gives up'))},
      {name: 'resets patience every turn', why: 'a fruitless turn restores patience, so nothing drops', loop: gossip('resets patience every turn'), laws: gossipLaws(gossip('resets patience every turn'))},
    ]),
    decisionCase('quorums', 'majorities never conflict, survive f crashes, and read/write quorums intersect', quorumDecisions, [
      {name: 'a majority of the responders', why: 'a majority of those who answered need not be a majority of the cluster', decision: responderMajority},
      {name: 'half is a quorum', why: 'with an even n, half the yes votes and half the no votes both pass', decision: halfIsQuorum},
    ]),
    machineCase('retransmission pacing', 'retransmitted bytes in any rtt ending at now stay within the budget, read from a pruned log', pacing(), [pacingLaw], [
      {name: 'window a tick short', why: 'the check reads one tick less than an rtt, missing a retransmission the window still counts', rule: pacing('window a tick short'), laws: [pacingLaw]},
    ]),
  ],
}
