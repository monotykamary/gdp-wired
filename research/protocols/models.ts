// Distributed protocols from the DistAI / DuoAI benchmark suites (their Ivy sources, github.com/VeriGu/DuoAI
// protocols/<name>/<name>.ivy), each written as a gdp-wired rule by hand, with its safety property as a law, a broken
// variant (one mutated action that breaks safety), and the inductive invariant a person would write (to tell what the
// kernel proves from what the search finds). README.md says how each relation maps.
//
// The encoding, the same for every protocol:
//   - a sort is the naturals; a relation over one sort is a map of 0/1 cells; a function into a sort is a map of values
//   - a relation over two sorts is one map at the key a·N + b (b < N), over three a·N² + b·N + c: N = 64, so each sort
//     but the first holds at most 64 elements (the encoding Casbin's link table uses in research/realworld/)
//   - an action is a request (`op`, its parameters as inputs); its `require`s are a flag, and a request whose flag is
//     false changes nothing (a stutter, which no safety property sees)
//   - `after init` with a free individual (a start node) is an `init` request taken once, before any other action
//   - a quorum is a set the request carries; Ivy's axiom that every two quorums meet is assumed of the request's quorum
//     and the stored one (`voting_quorum`) at a node the request names (`w`, the axiom's witness)
//   - a total order (le) on a sort is ≤ on the naturals, its successor + 1; a ring of `size` nodes is the positions
//     0..size − 1, next(n) = n + 1 mod size
import {type Law} from '../../core/machine.ts'
import {type Term, bool, everyKey, exists, fn, forall, nat, oneOf, no, rule, when, yes} from '../../core/dsl.ts'

export const N = 64
// a relation's cells: 0 or 1 (a kind, so the kernel and the search know it)
const rel = bool.from(false), relTrue = bool.from(true)
const pk = (a: Term, b: Term) => a.times(N).plus(b)
const pk3 = (a: Term, b: Term, c: Term) => a.times(N * N).plus(b.times(N)).plus(c)
type Bug = string | undefined
export type Protocol = {
  id: string, source: string, safety: string,
  make: (bug?: Bug) => any, bug: string,
  laws: (r: any) => Law[], // the safety property
  human: (r: any) => Law[], // the invariant a person writes, beside the safety property
}

// lock_server_sync: clients connect to servers, each server a semaphore.
const lockServerSync = (bug?: Bug) => rule('lock server sync')
  .inputs({op: oneOf('connect', 'disconnect'), x: nat, y: nat})
  .assume(({x, y}) => x.lt(N).and(y.lt(N)))
  .maps({Link: rel, Semaphore: relTrue})
  .flags(({op, x, y, Link, Semaphore}) => ({
    connects: op.is('connect').and(bug ? yes : Semaphore.at(y)),
    disconnects: op.is('disconnect').and(Link.at(pk(x, y))),
  }))
  .step(({x, y, connects, disconnects, Link, Semaphore}) => ({
    Link: Link.set(pk(x, y), when(connects, yes, when(disconnects, no, Link.at(pk(x, y))))),
    Semaphore: Semaphore.set(y, when(connects, no, when(disconnects, yes, Semaphore.at(y)))),
  }))

// lock_server_async: the same lock handed out by messages.
const lockServerAsync = (bug?: Bug) => rule('lock server async')
  .inputs({op: oneOf('send_lock', 'recv_lock', 'recv_grant', 'unlock', 'recv_unlock'), n: nat, l: nat})
  .assume(({n, l}) => n.lt(N).and(l.lt(N)))
  .maps({LockMsg: rel, GrantMsg: rel, UnlockMsg: rel, HoldsLock: rel, ServerHoldsLock: relTrue})
  .flags(({op, n, l, LockMsg, GrantMsg, UnlockMsg, HoldsLock, ServerHoldsLock}) => ({
    sendLock: op.is('send_lock'),
    recvLock: op.is('recv_lock').and(LockMsg.at(pk(n, l)), bug ? yes : ServerHoldsLock.at(l)),
    recvGrant: op.is('recv_grant').and(GrantMsg.at(pk(n, l))),
    unlocks: op.is('unlock').and(HoldsLock.at(pk(n, l))),
    recvUnlock: op.is('recv_unlock').and(UnlockMsg.at(pk(n, l))),
  }))
  .step(({n, l, sendLock, recvLock, recvGrant, unlocks, recvUnlock, LockMsg, GrantMsg, UnlockMsg, HoldsLock, ServerHoldsLock}) => ({
    LockMsg: LockMsg.set(pk(n, l), when(sendLock, yes, when(recvLock, no, LockMsg.at(pk(n, l))))),
    GrantMsg: GrantMsg.set(pk(n, l), when(recvLock, yes, when(recvGrant, no, GrantMsg.at(pk(n, l))))),
    HoldsLock: HoldsLock.set(pk(n, l), when(recvGrant, yes, when(unlocks, no, HoldsLock.at(pk(n, l))))),
    UnlockMsg: UnlockMsg.set(pk(n, l), when(unlocks, yes, when(recvUnlock, no, UnlockMsg.at(pk(n, l))))),
    ServerHoldsLock: ServerHoldsLock.set(l, when(recvLock, no, when(recvUnlock, yes, ServerHoldsLock.at(l)))),
  }))

// decentralized_lock: the lock passed by messages between nodes, no server.
const decentralizedLock = (bug?: Bug) => rule('decentralized lock')
  .params({start: nat}).pre(({start}) => start.lt(N))
  .inputs({op: oneOf('init', 'send', 'recv'), src: nat, dst: nat})
  .assume(({src, dst}) => src.lt(N).and(dst.lt(N)))
  .state({started: 0})
  .maps({Message: rel, HasLock: rel})
  .flags(({op, src, dst, started, Message, HasLock}) => ({
    inits: op.is('init').and(started.eq(0)),
    sends: op.is('send').and(started.eq(1), HasLock.at(src)),
    recvs: op.is('recv').and(started.eq(1), Message.at(pk(src, dst))),
  }))
  .step(({start, src, dst, inits, sends, recvs, started, Message, HasLock}) => ({
    started: when(inits, 1, started),
    Message: Message.set(pk(src, dst), when(sends, yes, when(recvs, no, Message.at(pk(src, dst))))),
    HasLock: HasLock.each(k => when(inits.and(k.eq(start)), yes, when(sends.and(k.eq(src)), bug ? HasLock.at(k) : no, when(recvs.and(k.eq(dst)), yes, HasLock.at(k))))),
  }))

// distributed_lock: the lock passed with epochs; a node takes it only at an epoch above its own.
const distributedLock = (bug?: Bug) => rule('distributed lock')
  .params({first: nat, e1: nat}).pre(({first, e1}) => first.lt(N).and(e1.atLeast(1)))
  .inputs({op: oneOf('init', 'grant', 'accept'), n1: nat, n2: nat, e: nat})
  .assume(({n1, n2}) => n1.lt(N).and(n2.lt(N)))
  .state({started: 0})
  .maps({Ep: 0, Held: rel, Transfer: rel, Locked: rel})
  .flags(({op, n1, e, started, Ep, Held, Transfer}) => ({
    inits: op.is('init').and(started.eq(0)),
    grants: op.is('grant').and(started.eq(1), bug ? yes : Held.at(n1), e.gt(Ep.at(n1))),
    // accept(n, e) is accept(n1, e): require transfer(e, n); if e > ep(n) it takes the lock
    accepts: op.is('accept').and(started.eq(1), Transfer.at(pk(e, n1)), e.gt(Ep.at(n1))),
  }))
  .step(({first, e1, n1, n2, e, inits, grants, accepts, started, Ep, Held, Transfer, Locked}) => ({
    started: when(inits, 1, started),
    Ep: Ep.each(k => when(inits.and(k.eq(first)), e1, when(accepts.and(k.eq(n1)), e, Ep.at(k)))),
    Held: Held.each(k => when(inits.and(k.eq(first)), yes, when(grants.and(k.eq(n1)), no, when(accepts.and(k.eq(n1)), yes, Held.at(k))))),
    Transfer: Transfer.set(pk(e, n2), when(grants, yes, Transfer.at(pk(e, n2)))),
    Locked: Locked.set(pk(e, n1), when(accepts, yes, Locked.at(pk(e, n1)))),
  }))

// two_phase_commit: `size` participants (Ivy's go1 and go2 read every node, so the nodes are 0..size − 1).
const twoPhaseCommit = (bug?: Bug) => rule('two-phase commit')
  .params({size: nat}).pre(({size}) => size.atMost(N))
  .inputs({op: oneOf('vote1', 'vote2', 'fail', 'go1', 'go2', 'commit', 'abort'), n: nat, w: nat})
  .assume(({n, w, size}) => n.lt(size).and(w.lt(size)))
  .state({abortFlag: 0})
  .maps({VoteYes: rel, VoteNo: rel, Alive: relTrue, GoCommit: rel, GoAbort: rel, DecideCommit: rel, DecideAbort: rel})
  .flags(({size, GoCommit, GoAbort, VoteYes}) => ({
    noGo: everyKey(k => k.lt(size).implies(GoCommit.at(k).not().and(GoAbort.at(k).not()))),
    allYes: everyKey(k => k.lt(size).implies(VoteYes.at(k))),
  }))
  .flags(({op, n, w, noGo, allYes, VoteYes, VoteNo, Alive, GoCommit, GoAbort, DecideCommit, DecideAbort}) => ({
    v1: op.is('vote1').and(Alive.at(n), VoteNo.at(n).not(), DecideCommit.at(n).not(), DecideAbort.at(n).not()),
    v2: op.is('vote2').and(Alive.at(n), VoteYes.at(n).not(), DecideCommit.at(n).not(), DecideAbort.at(n).not()),
    fails: op.is('fail').and(Alive.at(n)),
    g1: op.is('go1').and(noGo, bug ? yes : allYes),
    // require exists N. vote_no(N) | ~alive(N): the request names that node (w)
    g2: op.is('go2').and(noGo, VoteNo.at(w).or(Alive.at(w).not())),
    commits: op.is('commit').and(Alive.at(n), GoCommit.at(n)),
    aborts: op.is('abort').and(Alive.at(n), GoAbort.at(n)),
  }))
  .step(({n, v1, v2, fails, g1, g2, commits, aborts, abortFlag, VoteYes, VoteNo, Alive, GoCommit, GoAbort, DecideCommit, DecideAbort}) => ({
    abortFlag: when(v2.or(fails), 1, abortFlag),
    VoteYes: VoteYes.set(n, when(v1, yes, VoteYes.at(n))),
    VoteNo: VoteNo.set(n, when(v2, yes, VoteNo.at(n))),
    Alive: Alive.set(n, when(fails, no, Alive.at(n))),
    GoCommit: GoCommit.each(k => when(g1, yes, GoCommit.at(k))),
    GoAbort: GoAbort.each(k => when(g2, yes, GoAbort.at(k))),
    DecideCommit: DecideCommit.set(n, when(commits, yes, DecideCommit.at(n))),
    DecideAbort: DecideAbort.set(n, when(v2.or(aborts), yes, DecideAbort.at(n))),
  }))

// ticket_lock: pc1/pc2/pc3 as Pc 0/1/2; m(t, K) := K = next_ticket is a function, Ticket[t].
const ticketLock = (bug?: Bug) => rule('ticket lock')
  .inputs({op: oneOf('step12', 'step23', 'step31'), t: nat, k: nat})
  .state({service: 0, next: 0})
  .maps({Pc: 0, Ticket: 0})
  .flags(({op, t, k, service, Pc, Ticket}) => ({
    s12: op.is('step12').and(Pc.at(t).eq(0)),
    s23: op.is('step23').and(Pc.at(t).eq(1), bug ? yes : Ticket.at(t).eq(k), k.atMost(service)),
    s31: op.is('step31').and(Pc.at(t).eq(2)),
  }))
  .step(({t, s12, s23, s31, service, next, Pc, Ticket}) => ({
    Ticket: Ticket.set(t, when(s12, next, Ticket.at(t))),
    next: when(s12, next.plus(1), next),
    Pc: Pc.set(t, when(s12, 1, when(s23, 2, when(s31, 0, Pc.at(t))))),
    service: when(s31, service.plus(1), service),
  }))

// toy_consensus_forall: nodes vote once; a value is decided by a quorum all voting for it. vote(N, V) is Vote[V·N + N]
// (the quorum's flag reads it at every node, and a quantified flag reads a key only plainly, plus a term).
const toyConsensus = (bug?: Bug) => rule('toy consensus forall')
  .inputs({op: oneOf('init', 'cast_vote', 'decide'), n: nat, v: nat, w: nat})
  .carries('Q')
  .state({started: 0})
  .maps({Voted: rel, Vote: rel, Decided: rel, VotingQuorum: 0})
  .assume(({op, n, v, w, Q, VotingQuorum}) => n.lt(N).and(v.lt(N), everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(N)))),
    op.is('init').or(op.is('decide')).implies(Q.has(w)), op.is('decide').implies(VotingQuorum.has(w))))
  .flags(({v, Q, Vote}) => ({allVoted: everyKey(k => Q.has(k).implies(Vote.at(pk(v, k))))}))
  .flags(({op, n, started, allVoted, Voted}) => ({
    inits: op.is('init').and(started.eq(0)),
    casts: op.is('cast_vote').and(started.eq(1), bug ? yes : Voted.at(n).not()),
    decides: op.is('decide').and(started.eq(1), allVoted),
  }))
  .step(({n, v, inits, casts, decides, started, Q, Voted, Vote, Decided, VotingQuorum}) => ({
    started: when(inits, 1, started),
    Vote: Vote.set(pk(v, n), when(casts, yes, Vote.at(pk(v, n)))),
    Voted: Voted.set(n, when(casts, yes, Voted.at(n))),
    Decided: Decided.set(v, when(decides, yes, Decided.at(v))),
    VotingQuorum: VotingQuorum.each(k => when(inits.or(decides), Q.at(k), VotingQuorum.at(k))),
  }))

// consensus_wo_decide: leader election by a quorum of votes over messages.
const consensusWoDecide = (bug?: Bug) => rule('consensus wo decide')
  .inputs({op: oneOf('init', 'send_request_vote', 'send_vote', 'recv_vote', 'choose_voting_quorum', 'become_leader'), src: nat, dst: nat, nondet: bool, w: nat})
  .carries('Q')
  .state({started: 0})
  .maps({VoteRequestMsg: rel, Voted: rel, VoteMsg: rel, Votes: rel, Leader: rel, VotingQuorum: 0})
  .assume(({op, src, dst, w, Q, VotingQuorum}) => src.lt(N).and(dst.lt(N), everyKey(k => Q.at(k).atMost(1).and(Q.has(k).implies(k.lt(N)))),
    op.is('init').or(op.is('choose_voting_quorum')).implies(Q.has(w)), op.is('choose_voting_quorum').implies(VotingQuorum.has(w))))
  .flags(({src, Q, Votes, VotingQuorum}) => ({
    quorumVotes: everyKey(k => Q.has(k).implies(Votes.at(pk(src, k)))),
    votingQuorumVotes: everyKey(k => VotingQuorum.has(k).implies(Votes.at(pk(src, k)))),
  }))
  .flags(({op, src, dst, started, quorumVotes, votingQuorumVotes, Voted, VoteRequestMsg, VoteMsg}) => ({
    inits: op.is('init').and(started.eq(0)),
    requests: op.is('send_request_vote').and(started.eq(1)),
    votes: op.is('send_vote').and(started.eq(1), bug ? yes : Voted.at(src).not(), VoteRequestMsg.at(pk(dst, src))),
    // recv_vote(n, sender) is recv_vote(dst, src)
    receives: op.is('recv_vote').and(started.eq(1), VoteMsg.at(pk(src, dst))),
    // choose_voting_quorum(q, sn) is (Q, src); its second require (some quorum votes for sn) follows from the first
    chooses: op.is('choose_voting_quorum').and(started.eq(1), quorumVotes),
    leads: op.is('become_leader').and(started.eq(1), votingQuorumVotes),
  }))
  .step(({src, dst, nondet, inits, requests, votes, receives, chooses, leads, started, Q, VoteRequestMsg, Voted, VoteMsg, Votes, Leader, VotingQuorum}) => ({
    started: when(inits, 1, started),
    VoteRequestMsg: VoteRequestMsg.set(pk(src, dst), when(requests, yes, when(votes, nondet, VoteRequestMsg.at(pk(src, dst))))),
    VoteMsg: VoteMsg.set(pk(src, dst), when(votes, yes, VoteMsg.at(pk(src, dst)))),
    Voted: Voted.set(src, when(votes, yes, Voted.at(src))),
    Votes: Votes.set(pk(dst, src), when(receives, yes, Votes.at(pk(dst, src)))),
    Leader: Leader.set(src, when(leads, yes, Leader.at(src))),
    VotingQuorum: VotingQuorum.each(k => when(inits.or(chooses), Q.at(k), VotingQuorum.at(k))),
  }))

// ring_leader_election: `size` nodes in a ring, each passing on the largest id it has seen; idn is any injective
// function (the kernel knows it only by that fact; runs compute it as n XOR 5).
const idn = fn(1, (x: number) => x ^ 5, {facts: f => ({'idn is injective': forall((a, b) => f(a).eq(f(b)).implies(a.eq(b)))})})
const ringLeader = (bug?: Bug) => rule('ring leader election')
  .params({size: nat}).pre(({size}) => size.atLeast(2).and(size.atMost(N)))
  .inputs({op: oneOf('send', 'receive', 'become_leader'), n: nat, n1: nat, m: nat})
  .assume(({n, n1, size}) => n.lt(size).and(n1.lt(size)))
  .fns({idn})
  .maps({Leader: rel, Pending: rel})
  .flags(({op, n, n1, m, size, idn, Pending}) => {
    const next = n1.eq(when(n.plus(1).eq(size), 0, n.plus(1)))
    return {
      sends: op.is('send').and(next),
      receives: op.is('receive').and(next, Pending.at(pk(m, n)), bug ? yes : idn(n).atMost(m)),
      leads: op.is('become_leader').and(Pending.at(pk(idn(n), n))),
    }
  })
  .step(({n, n1, m, idn, sends, receives, leads, Leader, Pending}) => ({
    Pending: Pending.each(k => when(sends.and(k.eq(pk(idn(n), n1))).or(receives.and(k.eq(pk(m, n1)))), yes, Pending.at(k))),
    Leader: Leader.set(n, when(leads, yes, Leader.at(n))),
  }))

// sharded_key_value_store: keys move between shards by messages. Ivy's init assumes each key has at most one owner:
// `own` requests before `start` set that relation.
const shardedKv = (bug?: Bug) => rule('sharded key-value store')
  .inputs({op: oneOf('own', 'start', 'reshard', 'recv_transfer_msg', 'put'), n: nat, k: nat, v: nat, n2: nat})
  .assume(({n, k, v, n2}) => n.lt(N).and(k.lt(N), v.lt(N), n2.lt(N)))
  .state({started: 0})
  .maps({Table: rel, Owner: rel, TransferMsg: rel})
  .flags(({k, Owner}) => ({unowned: everyKey(m => m.lt(N).implies(Owner.at(pk(k, m)).not()))}))
  .flags(({op, n, k, v, started, unowned, Table, Owner, TransferMsg}) => ({
    owns: op.is('own').and(started.eq(0), unowned),
    starts: op.is('start').and(started.eq(0)),
    // reshard(k, v, n_old, n_new) is (k, v, n, n2)
    reshards: op.is('reshard').and(started.eq(1), Table.at(pk3(n, k, v))),
    receives: op.is('recv_transfer_msg').and(started.eq(1), TransferMsg.at(pk3(n, k, v))),
    puts: op.is('put').and(started.eq(1), bug ? yes : Owner.at(pk(k, n))),
  }))
  .step(({n, k, v, n2, owns, starts, reshards, receives, puts, started, Table, Owner, TransferMsg}) => ({
    started: when(starts, 1, started),
    // put: table(n, k, V) := V = v, the cells n·N² + k·N + V for every V < N
    Table: Table.each(z => when(reshards.and(z.eq(pk3(n, k, v))), no, when(receives.and(z.eq(pk3(n, k, v))), yes,
      when(puts.and(z.atLeast(pk3(n, k, v).minus(v)), z.lt(pk3(n, k, v).minus(v).plus(N))), when(z.eq(pk3(n, k, v)), yes, no), Table.at(z))))),
    Owner: Owner.set(pk(k, n), when(owns.or(receives), yes, when(reshards, no, Owner.at(pk(k, n))))),
    TransferMsg: TransferMsg.each(z => when(reshards.and(z.eq(pk3(n2, k, v))), yes, when(receives.and(z.eq(pk3(n, k, v))), no, TransferMsg.at(z)))),
  }))

// Diagnostics, not the protocols: the two lock servers cut to one server (one lock), every relation a map keyed by the
// client (node) alone and the semaphore a scalar. Ivy's actions touch one server (lock) each and the safety property
// is per server, so each cut is the protocol at one server; gdp-wired does not prove that reduction.
const lockServerOne = (bug?: Bug) => rule('lock server sync, one server')
  .inputs({op: oneOf('connect', 'disconnect'), x: nat})
  .state({semaphore: 1})
  .maps({Link: rel})
  .flags(({op, x, semaphore, Link}) => ({connects: op.is('connect').and(bug ? yes : semaphore.eq(1)), disconnects: op.is('disconnect').and(Link.at(x))}))
  .step(({x, connects, disconnects, semaphore, Link}) => ({
    Link: Link.set(x, when(connects, yes, when(disconnects, no, Link.at(x)))),
    semaphore: when(connects, 0, when(disconnects, 1, semaphore)),
  }))
const lockAsyncOne = (bug?: Bug) => rule('lock server async, one lock')
  .inputs({op: oneOf('send_lock', 'recv_lock', 'recv_grant', 'unlock', 'recv_unlock'), n: nat})
  .state({serverHoldsLock: 1})
  .maps({LockMsg: rel, GrantMsg: rel, UnlockMsg: rel, HoldsLock: rel})
  .flags(({op, n, serverHoldsLock, LockMsg, GrantMsg, UnlockMsg, HoldsLock}) => ({
    sendLock: op.is('send_lock'),
    recvLock: op.is('recv_lock').and(LockMsg.at(n), bug ? yes : serverHoldsLock.eq(1)),
    recvGrant: op.is('recv_grant').and(GrantMsg.at(n)),
    unlocks: op.is('unlock').and(HoldsLock.at(n)),
    recvUnlock: op.is('recv_unlock').and(UnlockMsg.at(n)),
  }))
  .step(({n, sendLock, recvLock, recvGrant, unlocks, recvUnlock, serverHoldsLock, LockMsg, GrantMsg, UnlockMsg, HoldsLock}) => ({
    LockMsg: LockMsg.set(n, when(sendLock, yes, when(recvLock, no, LockMsg.at(n)))),
    GrantMsg: GrantMsg.set(n, when(recvLock, yes, when(recvGrant, no, GrantMsg.at(n)))),
    HoldsLock: HoldsLock.set(n, when(recvGrant, yes, when(unlocks, no, HoldsLock.at(n)))),
    UnlockMsg: UnlockMsg.set(n, when(unlocks, yes, when(recvUnlock, no, UnlockMsg.at(n)))),
    serverHoldsLock: when(recvLock, 0, when(recvUnlock, 1, serverHoldsLock)),
  }))
export const cuts: Protocol[] = [
  {id: 'lock_server_sync@one', source: 'lock_server_sync at one server', safety: 'link(C1, s) & link(C2, s) -> C1 = C2', make: lockServerOne, bug: 'connect without the semaphore',
    laws: r => [r.law('one client', ({Link}: any) => forall((a, b) => Link.at(a).and(Link.at(b)).implies(a.eq(b))))],
    human: r => [r.law('a link means taken', ({Link, semaphore}: any) => forall(a => Link.at(a).implies(semaphore.eq(0))))]},
  {id: 'lock_server_async@one', source: 'lock_server_async at one lock', safety: 'holds_lock(N1, l) & holds_lock(N2, l) -> N1 = N2', make: lockAsyncOne, bug: 'recv_lock without server_holds_lock',
    laws: r => [r.law('one holder', ({HoldsLock}: any) => forall((a, b) => HoldsLock.at(a).and(HoldsLock.at(b)).implies(a.eq(b))))],
    human: r => {
      const tok = (env: any, a: Term) => env.GrantMsg.at(a).or(env.HoldsLock.at(a), env.UnlockMsg.at(a))
      return [
        r.law('one token among the nodes', (env: any) => forall((a, b) => a.eq(b).not().and(tok(env, a)).implies(tok(env, b).not()))),
        r.law('a token out means the server has none', (env: any) => forall(a => tok(env, a).implies(env.serverHoldsLock.eq(0)))),
        r.law('one token per node', ({GrantMsg, HoldsLock, UnlockMsg}: any) => forall(a => GrantMsg.at(a).and(HoldsLock.at(a)).not().and(GrantMsg.at(a).and(UnlockMsg.at(a)).not(), HoldsLock.at(a).and(UnlockMsg.at(a)).not()))),
      ]
    }},
]

const lt = (...ts: Term[]) => ts.map(t => t.lt(N)).reduce((a, b) => a.and(b))
export const protocols: Protocol[] = [
  {id: 'lock_server_sync', source: 'DuoAI protocols/lock_server_sync (DistAI: lock server)', safety: 'link(C1, S) & link(C2, S) -> C1 = C2',
    make: lockServerSync, bug: 'connect without the semaphore',
    laws: r => [r.law('one client per server', ({Link}: any) => forall((c1, c2, s) => lt(c1, c2, s).and(Link.at(pk(c1, s)), Link.at(pk(c2, s))).implies(c1.eq(c2))))],
    human: r => [r.law('a linked server is taken', ({Link, Semaphore}: any) => forall((c, s) => lt(c, s).and(Link.at(pk(c, s))).implies(Semaphore.at(s).not())))]},
  {id: 'lock_server_async', source: 'DuoAI protocols/lock_server_async (DistAI: asynchronous lock server)', safety: 'holds_lock(N1, L) & holds_lock(N2, L) -> N1 = N2',
    make: lockServerAsync, bug: 'recv_lock without server_holds_lock',
    laws: r => [r.law('one holder per lock', ({HoldsLock}: any) => forall((a, b, l) => lt(a, b, l).and(HoldsLock.at(pk(a, l)), HoldsLock.at(pk(b, l))).implies(a.eq(b))))],
    human: r => {
      const tok = (M: any, a: Term, l: Term) => M.at(pk(a, l))
      return [
        r.law('the server or one grant, hold or unlock per lock', ({GrantMsg, HoldsLock, UnlockMsg}: any) => forall((a, b, l) => lt(a, b, l).and(a.eq(b).not()).implies(
          tok(GrantMsg, a, l).or(tok(HoldsLock, a, l), tok(UnlockMsg, a, l)).implies(tok(GrantMsg, b, l).or(tok(HoldsLock, b, l), tok(UnlockMsg, b, l)).not())))),
        r.law('a token out means the server has none', ({GrantMsg, HoldsLock, UnlockMsg, ServerHoldsLock}: any) => forall((a, l) => lt(a, l).and(tok(GrantMsg, a, l).or(tok(HoldsLock, a, l), tok(UnlockMsg, a, l))).implies(ServerHoldsLock.at(l).not()))),
        r.law('one token per node and lock', ({GrantMsg, HoldsLock, UnlockMsg}: any) => forall((a, l) => lt(a, l).implies(GrantMsg.at(pk(a, l)).and(HoldsLock.at(pk(a, l))).not().and(GrantMsg.at(pk(a, l)).and(UnlockMsg.at(pk(a, l))).not(), HoldsLock.at(pk(a, l)).and(UnlockMsg.at(pk(a, l))).not())))),
      ]
    }},
  {id: 'decentralized_lock', source: 'DuoAI protocols/decentralized_lock (DistAI: decentralized lock; cfg-enum simple-de-lock.ivy)', safety: 'X ~= Y -> ~(has_lock(X) & has_lock(Y))',
    make: decentralizedLock, bug: 'send keeps the lock',
    laws: r => [r.law('one node holds the lock', ({HasLock}: any) => forall((a, b) => lt(a, b).and(a.eq(b).not(), HasLock.at(a)).implies(HasLock.at(b).not())))],
    human: r => [
      r.law('a message in flight means nobody holds the lock', ({Message, HasLock}: any) => forall((s, d, x) => lt(s, d, x).and(Message.at(pk(s, d))).implies(HasLock.at(x).not()))),
      r.law('one message in flight', ({Message}: any) => forall((s, d, s2, d2) => lt(s, d, s2, d2).and(Message.at(pk(s, d)), Message.at(pk(s2, d2))).implies(s.eq(s2).and(d.eq(d2))))),
      r.law('no holder before init', ({started, HasLock}: any) => forall(x => lt(x).and(started.eq(0)).implies(HasLock.at(x).not()))),
      r.law('no message before init', ({started, Message}: any) => forall((s, d) => lt(s, d).and(started.eq(0)).implies(Message.at(pk(s, d)).not()))),
    ]},
  {id: 'distributed_lock', source: 'DuoAI protocols/distributed_lock (DistAI: distributed lock; Ivy\'s distributed lock)', safety: 'locked(E, N1) & locked(E, N2) -> N1 = N2',
    make: distributedLock, bug: 'grant without holding the lock',
    laws: r => [r.law('one node locked per epoch', ({Locked}: any) => forall((e, a, b) => lt(a, b).and(Locked.at(pk(e, a)), Locked.at(pk(e, b))).implies(a.eq(b))))],
    // Ivy's: a transfer above every epoch is the lock in flight; the lock is held or in flight once (DistAI's set has 6)
    human: r => [
      r.law('a locked epoch is its node\'s epoch or below', ({Ep, Locked}: any) => forall((e, a) => lt(a).and(Locked.at(pk(e, a))).implies(e.atMost(Ep.at(a))))),
      r.law('a holder\'s epoch is above every node\'s other', ({Ep, Held}: any) => forall((a, b) => lt(a, b).and(a.eq(b).not(), Held.at(a)).implies(Ep.at(b).lt(Ep.at(a))))),
      r.law('two holders are one', ({Held}: any) => forall((a, b) => lt(a, b).and(Held.at(a), Held.at(b)).implies(a.eq(b)))),
      r.law('a live transfer is above every epoch', ({Ep, Transfer}: any) => forall((e, a, b) => lt(a, b).and(Transfer.at(pk(e, a)), e.gt(Ep.at(a))).implies(Ep.at(b).lt(e)))),
      r.law('a live transfer means nobody holds', ({Ep, Held, Transfer}: any) => forall((e, a, b) => lt(a, b).and(Transfer.at(pk(e, a)), e.gt(Ep.at(a))).implies(Held.at(b).not()))),
      r.law('two live transfers are one', ({Ep, Transfer}: any) => forall((e, a, f, b) => lt(a, b).and(Transfer.at(pk(e, a)), e.gt(Ep.at(a)), Transfer.at(pk(f, b)), f.gt(Ep.at(b))).implies(e.eq(f).and(a.eq(b))))),
      r.law('a locked epoch at a node\'s epoch is its own', ({Ep, Locked}: any) => forall((e, a, b) => lt(a, b).and(a.eq(b).not(), Locked.at(pk(e, a))).implies(Locked.at(pk(e, b)).not().or(e.eq(Ep.at(b)).not())))),
      r.law('nothing before init', ({started, Held, Ep}: any) => forall(a => lt(a).and(started.eq(0)).implies(Held.at(a).not().and(Ep.at(a).eq(0))))),
      // (without it the set is not inductive: a transfer held before `init` breaks "a live transfer is above every
      // epoch" once `init` sets Ep[first] — no run reaches such a state, research/protocols/COST.md)
      r.law('no transfer or lock before init', ({started, Transfer, Locked}: any) => forall((e, a) => lt(a).and(started.eq(0)).implies(Transfer.at(pk(e, a)).not().and(Locked.at(pk(e, a)).not())))),
    ]},
  {id: 'two_phase_commit', source: 'DuoAI protocols/two_phase_commit (DistAI: two-phase commit; I4)', safety: '(decide_commit(N0) -> ~decide_abort(N1)) & (decide_commit(N0) -> vote_yes(N1)) & (decide_abort(N0) -> abort_flag)',
    make: twoPhaseCommit, bug: 'go1 without every yes vote',
    laws: r => [r.law('commit and abort agree', ({size, abortFlag, VoteYes, DecideCommit, DecideAbort}: any) => forall((a, b) => a.lt(size).and(b.lt(size)).implies(
      DecideCommit.at(a).implies(DecideAbort.at(b).not().and(VoteYes.at(b))).and(DecideAbort.at(a).implies(abortFlag.eq(1))))))],
    human: r => [
      r.law('go_commit only after every yes', ({size, VoteYes, GoCommit}: any) => forall((a, b) => a.lt(size).and(b.lt(size), GoCommit.at(a)).implies(VoteYes.at(b)))),
      r.law('go_commit and go_abort exclude', ({size, GoCommit, GoAbort}: any) => forall((a, b) => a.lt(size).and(b.lt(size), GoCommit.at(a)).implies(GoAbort.at(b).not()))),
      r.law('a commit had go_commit', ({size, GoCommit, DecideCommit}: any) => forall(a => a.lt(size).and(DecideCommit.at(a)).implies(GoCommit.at(a)))),
      r.law('an abort had go_abort or a no vote', ({size, GoAbort, VoteNo, DecideAbort}: any) => forall(a => a.lt(size).and(DecideAbort.at(a)).implies(GoAbort.at(a).or(VoteNo.at(a))))),
      r.law('a failed node means the flag', ({size, Alive, abortFlag}: any) => forall(a => a.lt(size).and(Alive.at(a).not()).implies(abortFlag.eq(1)))),
      r.law('go_abort means the flag', ({size, GoAbort, abortFlag}: any) => forall(a => a.lt(size).and(GoAbort.at(a)).implies(abortFlag.eq(1)))),
      r.law('a no vote means the flag and no yes', ({size, VoteNo, VoteYes, abortFlag}: any) => forall(a => a.lt(size).and(VoteNo.at(a)).implies(abortFlag.eq(1).and(VoteYes.at(a).not())))),
      r.law('go_commit means no no vote', ({size, GoCommit, VoteNo}: any) => forall((a, b) => a.lt(size).and(b.lt(size), GoCommit.at(a)).implies(VoteNo.at(b).not()))),
      r.law('go flags agree', ({size, GoCommit, GoAbort}: any) => forall((a, b) => a.lt(size).and(b.lt(size)).implies(GoCommit.at(a).iff(GoCommit.at(b)).and(GoAbort.at(a).iff(GoAbort.at(b)))))),
    ]},
  {id: 'ticket_lock', source: 'DuoAI protocols/ticket_lock (mypyvy ticket.pyv)', safety: 'pc3(T1) & pc3(T2) -> T1 = T2',
    make: ticketLock, bug: 'step23 without m(t, k)',
    laws: r => [r.law('one thread in the critical section', ({Pc}: any) => forall((a, b) => Pc.at(a).eq(2).and(Pc.at(b).eq(2)).implies(a.eq(b))))],
    human: r => [
      r.law('pc is 0, 1 or 2', ({Pc}: any) => forall(a => Pc.at(a).atMost(2))),
      r.law('a waiting ticket is below next', ({Pc, Ticket, next}: any) => forall(a => Pc.at(a).atLeast(1).implies(Ticket.at(a).lt(next)))),
      r.law('service is at most next', ({service, next}: any) => service.atMost(next)),
      r.law('in the section, the ticket is the service', ({Pc, Ticket, service}: any) => forall(a => Pc.at(a).eq(2).implies(Ticket.at(a).eq(service)))),
      r.law('a waiting ticket is at least the service', ({Pc, Ticket, service}: any) => forall(a => Pc.at(a).atLeast(1).implies(Ticket.at(a).atLeast(service)))),
      r.law('waiting tickets are distinct', ({Pc, Ticket}: any) => forall((a, b) => a.eq(b).not().and(Pc.at(a).atLeast(1), Pc.at(b).atLeast(1)).implies(Ticket.at(a).eq(Ticket.at(b)).not()))),
    ]},
  {id: 'toy_consensus_forall', source: 'DuoAI protocols/toy_consensus_forall (DistAI: simple consensus family)', safety: 'decided(V1) & decided(V2) -> V1 = V2',
    make: toyConsensus, bug: 'cast_vote without voted',
    laws: r => [r.law('one value decided', ({Decided}: any) => forall((a, b) => lt(a, b).and(Decided.at(a), Decided.at(b)).implies(a.eq(b))))],
    human: r => [
      r.law('a vote means voted', ({Vote, Voted}: any) => forall((n, v) => lt(n, v).and(Vote.at(pk(v, n))).implies(Voted.at(n)))),
      r.law('one vote per node', ({Vote}: any) => forall((n, v, u) => lt(n, v, u).and(Vote.at(pk(v, n)), Vote.at(pk(u, n))).implies(v.eq(u)))),
      r.law('the voting quorum voted for every decided value', ({Vote, Decided, VotingQuorum}: any) => forall((n, v) => lt(n, v).and(Decided.at(v), VotingQuorum.has(n)).implies(Vote.at(pk(v, n))))),
      r.law('nothing before init', ({started, Decided}: any) => forall(v => started.eq(0).implies(Decided.at(v).not()))),
    ]},
  {id: 'consensus_wo_decide', source: 'DuoAI protocols/consensus_wo_decide (DistAI: consensus family)', safety: 'leader(N1) & leader(N2) -> N1 = N2',
    make: consensusWoDecide, bug: 'send_vote without voted',
    laws: r => [r.law('one leader', ({Leader}: any) => forall((a, b) => lt(a, b).and(Leader.at(a), Leader.at(b)).implies(a.eq(b))))],
    human: r => [
      r.law('a vote message means voted', ({VoteMsg, Voted}: any) => forall((s, d) => lt(s, d).and(VoteMsg.at(pk(s, d))).implies(Voted.at(s)))),
      r.law('one vote message per voter', ({VoteMsg}: any) => forall((s, d, e) => lt(s, d, e).and(VoteMsg.at(pk(s, d)), VoteMsg.at(pk(s, e))).implies(d.eq(e)))),
      r.law('a counted vote was sent', ({Votes, VoteMsg}: any) => forall((n, s) => lt(n, s).and(Votes.at(pk(n, s))).implies(VoteMsg.at(pk(s, n))))),
      r.law('a leader has the voting quorum\'s votes', ({Leader, Votes, VotingQuorum}: any) => forall((n, s) => lt(n, s).and(Leader.at(n), VotingQuorum.has(s)).implies(Votes.at(pk(n, s))))),
      r.law('nothing before init', ({started, Leader}: any) => forall(n => started.eq(0).implies(Leader.at(n).not()))),
      // (Ivy's quorums meet, so the voting quorum is never empty; without it an empty one lets anyone lead: COST.md)
      r.law('after init the voting quorum has a member', ({started, VotingQuorum}: any) => started.eq(1).implies(exists((x: Term) => x.lt(N).and(VotingQuorum.has(x)),
        {start: 0, step: (before: Term, env: any) => when(env.inits.or(env.chooses), env.w, before)}))),
    ]},
  {id: 'ring_leader_election', source: 'DuoAI protocols/ring_leader_election (DistAI: leader election; Ivy\'s leader_election_ring)', safety: 'leader(X) & leader(Y) -> X = Y',
    make: ringLeader, bug: 'receive forwards every id',
    laws: r => [r.law('one leader', ({size, Leader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))],
    // the leader has the largest id; an id pending at a node passed every node between its owner and it
    human: r => {
      const btw = (x: Term, y: Term, z: Term) => x.lt(y).and(y.lt(z)).or(y.lt(z).and(z.lt(x)), z.lt(x).and(x.lt(y)))
      return [
        r.law('a leader\'s id is the largest', ({size, idn, Leader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a)).implies(idn(b).atMost(idn(a))))),
        r.law('a node\'s own id pending at it is the largest', ({size, idn, Pending}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Pending.at(pk(idn(a), a))).implies(idn(b).atMost(idn(a))))),
        r.law('an id pending past a node is above that node\'s', ({size, idn, Pending}: any) => forall((a, b, c) => a.lt(size).and(b.lt(size), c.lt(size), btw(a, b, c), Pending.at(pk(idn(a), c))).implies(idn(b).lt(idn(a))))),
      ]
    }},
  {id: 'sharded_key_value_store', source: 'DuoAI protocols/sharded_key_value_store (DistAI: hashed sharding family)', safety: 'table(N1, K, V1) & table(N2, K, V2) -> N1 = N2 & V1 = V2',
    make: shardedKv, bug: 'put without ownership',
    laws: r => [r.law('one value per key', ({Table}: any) => forall((a, b, k, v, u) => lt(a, b, k, v, u).and(Table.at(pk3(a, k, v)), Table.at(pk3(b, k, u))).implies(a.eq(b).and(v.eq(u)))))],
    human: r => [
      r.law('one owner per key', ({Owner}: any) => forall((a, b, k) => lt(a, b, k).and(Owner.at(pk(k, a)), Owner.at(pk(k, b))).implies(a.eq(b)))),
      r.law('a table entry is its owner\'s', ({Owner, Table}: any) => forall((a, k, v) => lt(a, k, v).and(Table.at(pk3(a, k, v))).implies(Owner.at(pk(k, a))))),
      r.law('a key in transfer has no owner', ({Owner, TransferMsg}: any) => forall((a, b, k, v) => lt(a, b, k, v).and(TransferMsg.at(pk3(a, k, v))).implies(Owner.at(pk(k, b)).not()))),
      r.law('one transfer per key', ({TransferMsg}: any) => forall((a, b, k, v, u) => lt(a, b, k, v, u).and(TransferMsg.at(pk3(a, k, v)), TransferMsg.at(pk3(b, k, u))).implies(a.eq(b).and(v.eq(u))))),
      r.law('one value per owner and key', ({Table}: any) => forall((a, k, v, u) => lt(a, k, v, u).and(Table.at(pk3(a, k, v)), Table.at(pk3(a, k, u))).implies(v.eq(u)))),
      r.law('nothing in the table before start', ({started, Table, TransferMsg}: any) => forall((a, k, v) => lt(a, k, v).and(started.eq(0)).implies(Table.at(pk3(a, k, v)).not().and(TransferMsg.at(pk3(a, k, v)).not())))),
    ]},
]
