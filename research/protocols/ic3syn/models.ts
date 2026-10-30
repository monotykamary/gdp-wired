// The IC3Syn suite (Cao et al., arXiv 2605.24619): its 29 protocols, each a TLA+ spec of Endive's benchmarks (pyv-paxos-epr
// mypyvy's paxos_epr.pyv, which the TLA+ cites; README.md says where each is from), written as a gdp-wired rule by hand in
// the encoding of ../models.ts (its README): a sort is the naturals below N = 64 (or 0 .. size − 1, a param, where the spec
// reads the whole sort), a relation a map of 0/1 cells at a·N + b, a function into a sort a map of naturals (v + 1, with
// 0 for Nil), an enumeration a map of few values; each action a request (`op` and its parameters), its guard a flag, a
// request whose flag is false a stutter. An `Init` that picks from a set (`owner \in [Node -> SUBSET Key]`, a start node,
// a match relation) is a setup phase of requests before `start`; states before it project to no TLA+ state.
// Quorums: a TLA+ `CONSTANT Quorum` is common.ts's quorum sort (member, meet and their fact, Ivy's axiom); a majority
// (`Cardinality(Q) * 2 > Cardinality(Node)`) is common.ts's `majority`, exact, with a cut `<id>@q` that takes the quorum
// sort instead (sound: majorities of a set meet, so every run of the spec is a run of the cut).
// Each port has its correspondence beside it (`file`, and what differs), a broken variant (`bug`), `bad` (the safety
// property broken, read on the check's instance) and `check` (the instance and its TLC cfg; check.ts, tlc.py).
import {type Term, everyKey, exists, forall, nat, no, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {N, type Protocol, type Read, few, lt, majority, majorityWitness, meet, member, pk, pk3, quorumFacts, range, rel, relTrue, subsets} from './common.ts'

type Bug = string | undefined
const tlc = (module: string, constants: string, inv: string, more = '') => ({module, cfg: `INIT Init\nNEXT Next\n${constants}\nINVARIANT ${inv}\n${more}`})
const nodes = (n: number, p = 'n') => range(n).map(i => `${p}${i + 1}`)
const consts = (sets: Record<string, string[]>, plain: Record<string, string> = {}) =>
  `CONSTANTS\n${Object.entries(sets).map(([k, vs]) => `  ${k} = {${vs.join(', ')}}\n${vs.map(v => `  ${v} = ${v}\n`).join('')}`).join('')}${Object.entries(plain).map(([k, v]) => `  ${k} = ${v}\n`).join('')}`
const cells = (r: Read, map: string, keys: number[]) => keys.map(k => r.cell(map, k))
const pairs = (a: number[], b: number[]) => a.flatMap(x => b.map(y => x * N + y))
const triples = (a: number[], b: number[], c: number[]) => a.flatMap(x => b.flatMap(y => c.map(z => x * N * N + y * N + z)))
// A majority's request: Q from a bitmask over 0 .. size − 1, with its witness (none for other requests).
const withMajority = (size: number) => (i: Record<string, any>) => {
  const q = range(size).filter(k => i.qm >> k & 1), {qm, ...rest} = i
  return [{...rest, ...majorityWitness(q, size)}]
}
const twoDistinct = (r: Read, map: string, keys: number[]) => keys.filter(k => r.cell(map, k)).length > 1

// --- tla-consensus: Consensus.tla. chosen ⊆ Value; Next: chosen = {} ∧ chosen' = {v}. Inv: Cardinality(chosen) <= 1,
// which over a set is ∀ a, b ∈ chosen: a = b.
const consensus = (bug?: Bug) => rule('consensus')
  .inputs({v: nat}).assume(({v}) => v.lt(N))
  .maps({Chosen: rel})
  .flags(({Chosen}) => ({none: everyKey(k => Chosen.at(k).not())}))
  .flags(({none}) => ({chooses: bug ? yes : none}))
  .step(({v, chooses, Chosen}) => ({Chosen: Chosen.set(v, when(chooses, yes, Chosen.at(v)))}))

// --- tla-tcommit: TCommit.tla. rmState: working 0, prepared 1, committed 2, aborted 3; RM is 0 .. size − 1 (canCommit and
// notCommitted read every RM). Decide's two branches are two requests.
const tcommit = (bug?: Bug) => rule('tcommit')
  .params({size: nat}).pre(({size}) => size.atMost(N))
  .inputs({op: oneOf('prepare', 'commit', 'abort'), rm: nat}).assume(({rm, size}) => rm.lt(size))
  .maps({St: few(3)})
  .flags(({size, St}) => ({
    canCommit: everyKey(k => k.lt(size).implies(St.at(k).eq(1).or(St.at(k).eq(2)))),
    notCommitted: everyKey(k => k.lt(size).implies(St.at(k).eq(2).not())),
  }))
  .flags(({op, rm, canCommit, notCommitted, St}) => ({
    prepares: op.is('prepare').and(St.at(rm).eq(0)),
    commits: op.is('commit').and(St.at(rm).eq(1), bug ? yes : canCommit),
    aborts: op.is('abort').and(St.at(rm).atMost(1), notCommitted),
  }))
  .step(({rm, prepares, commits, aborts, St}) => ({St: St.set(rm, when(prepares, 1, when(commits, 2, when(aborts, 3, St.at(rm)))))}))

// --- i4-lock-server: lockserver.tla. semaphore[s] (TRUE at first); s \in clientlocks[c] is Link[c·N + s].
const lockServer = (bug?: Bug) => rule('lock server')
  .inputs({op: oneOf('connect', 'disconnect'), c: nat, s: nat}).assume(({c, s}) => lt(c, s))
  .maps({Link: rel, Semaphore: relTrue})
  .flags(({op, c, s, Link, Semaphore}) => ({
    connects: op.is('connect').and(bug ? yes : Semaphore.at(s)),
    disconnects: op.is('disconnect').and(Link.at(pk(c, s))),
  }))
  .step(({c, s, connects, disconnects, Link, Semaphore}) => ({
    Link: Link.set(pk(c, s), when(connects, yes, when(disconnects, no, Link.at(pk(c, s))))),
    Semaphore: Semaphore.set(s, when(connects, no, when(disconnects, yes, Semaphore.at(s)))),
  }))

// A rule over nodes 0 .. size − 1 whose action `act` reads a majority: a request (op: the protocol's two actions, i, and
// `more`) carrying Q with its witness (Out, c), or, with `axiom`, naming a quorum q of the quorum sort.
const quorumOrMajority = (r: any, axiom: boolean, act: string, more: Record<string, unknown>, ok: (env: any) => any = () => yes): any => {
  const ops = act === 'become_leader' ? oneOf('vote', 'become_leader') : oneOf('cast_vote', 'decide')
  const base = r.params({size: nat}).pre(({size}: any) => size.atMost(N))
  return axiom
    ? base.inputs({op: ops, i: nat, ...more, q: nat}).fns({member, meet}).facts(quorumFacts)
      .assume((env: any) => env.i.lt(env.size).and(ok(env), ...('j' in more ? [env.j.lt(env.size)] : [])))
    : base.inputs({op: ops, i: nat, ...more, c: nat}).carries('Q', 'Out')
      .assume((env: any) => env.i.lt(env.size).and(ok(env), ...('j' in more ? [env.j.lt(env.size)] : []), env.op.is(act).implies(majority(env.Q, env.Out, env.c, env.size))))
}
const inQuorum = (axiom: boolean, k: Term, q: Term, Q: any, member: any) => (axiom ? member(k, q).eq(1) : Q.has(k))

// --- ex-quorum-leader-election: quorum_leader_election.tla. voted[i] is Voted[i] (j + 1; 0 is Nil). Node is 0 .. size − 1.
// BecomeLeader(i, Q) for a majority Q (or, the @q cut, a quorum q).
const quorumLeader = (axiom: boolean) => (bug?: Bug) => quorumOrMajority(rule('quorum leader election'), axiom, 'become_leader', {j: nat})
  .maps({IsLeader: rel, Voted: 0})
  .flags(({i, q, Q, Voted, member}: any) => ({allVoted: everyKey(k => inQuorum(axiom, k, q, Q, member).implies(Voted.at(k).eq(i.plus(1))))}))
  .flags(({op, i, allVoted, Voted}: any) => ({votes: op.is('vote').and(bug ? yes : Voted.at(i).eq(0)), leads: op.is('become_leader').and(allVoted)}))
  .step(({i, j, votes, leads, IsLeader, Voted}: any) => ({
    Voted: Voted.set(i, when(votes, j.plus(1), Voted.at(i))),
    IsLeader: IsLeader.set(i, when(leads, yes, IsLeader.at(i))),
  }))

// --- pyv-toy-consensus-forall: toy_consensus_forall.tla. vote[i] is Vote[i] (v + 1; 0 is Nil). Node is 0 .. size − 1.
const toyForall = (axiom: boolean) => (bug?: Bug) => quorumOrMajority(rule('toy consensus forall'), axiom, 'decide', {v: nat}, ({v}: any) => v.lt(N))
  .maps({Vote: 0, Voted: rel, Decided: rel})
  .flags(({v, q, Q, Vote, member}: any) => ({allVote: everyKey(k => inQuorum(axiom, k, q, Q, member).implies(Vote.at(k).eq(v.plus(1))))}))
  .flags(({op, i, allVote, Voted}: any) => ({casts: op.is('cast_vote').and(bug ? yes : Voted.at(i).not()), decides: op.is('decide').and(allVote)}))
  .step(({i, v, casts, decides, Vote, Voted, Decided}: any) => ({
    Vote: Vote.set(i, when(casts, v.plus(1), Vote.at(i))),
    Voted: Voted.set(i, when(casts, yes, Voted.at(i))),
    Decided: Decided.set(v, when(decides, yes, Decided.at(v))),
  }))

// --- tla-simple: Simple.tla. Processes 0 .. n − 1, pc a 0, b 1, Done 2; (self − 1) % N is self − 1, or n − 1 at 0.
// PCorrect, (∀i: pc[i] = Done) ⇒ ∃i: y[i] = 1, is written as its prenex form ∃i: pc[i] ≠ Done ∨ y[i] = 1.
const simple = (regular: boolean) => (bug?: Bug) => rule(regular ? 'simple regular' : 'simple')
  .params({n: nat}).pre(({n}) => n.atLeast(1).and(n.atMost(N)))
  .inputs({op: oneOf('a1', 'a2', 'b'), self: nat, v: nat}).assume(({self, n, v}) => self.lt(n).and(v.atMost(1)))
  // simple: x[i] 0 or 1. simple regular: x[i] {0} 0, {0, 1} 1, {1} 2; pc a1 0, a2 1, b 2, Done 3
  .maps({X: few(2), Y: few(1), Pc: few(3)})
  .flags(({op, self, n, v, X, Pc}) => {
    const prev = when(self.eq(0), n.minus(1), self.minus(1)), xp = X.at(prev)
    return regular ? {
      a1s: op.is('a1').and(Pc.at(self).eq(0)), a2s: op.is('a2').and(Pc.at(self).eq(1)),
      bs: op.is('b').and(Pc.at(self).eq(2), v.eq(0).and(xp.atMost(1)).or(v.eq(1).and(xp.atLeast(1)))),
    } : {a1s: op.is('a1').and(Pc.at(self).eq(0)), a2s: no, bs: op.is('b').and(Pc.at(self).eq(1), v.eq(xp))}
  })
  .step(({self, a1s, a2s, bs, v, X, Y, Pc}) => ({
    X: X.set(self, regular ? when(a1s, 1, when(a2s, bug ? 1 : 2, X.at(self))) : when(a1s, bug ? X.at(self) : 1, X.at(self))),
    Y: Y.set(self, when(bs, v, Y.at(self))),
    Pc: Pc.set(self, when(a1s, 1, when(a2s, 2, when(bs, regular ? 3 : 2, Pc.at(self))))),
  }))

// --- ex-lockserv-automaton: lockserv_automaton.tla. held is a scalar.
const lockservAutomaton = (bug?: Bug) => rule('lockserv automaton')
  .inputs({op: oneOf('lock', 'unlock', 'recv_lock', 'recv_grant', 'recv_unlock'), n: nat}).assume(({n}) => n.lt(N))
  .state({held: 0})
  .maps({LockMsg: rel, UnlockMsg: rel, GrantMsg: rel, HoldsLock: rel})
  .flags(({op, n, held, LockMsg, UnlockMsg, GrantMsg, HoldsLock}) => ({
    locks: op.is('lock'),
    unlocks: op.is('unlock').and(HoldsLock.at(n)),
    recvLock: op.is('recv_lock').and(LockMsg.at(n), bug ? yes : held.eq(0)),
    recvGrant: op.is('recv_grant').and(GrantMsg.at(n)),
    recvUnlock: op.is('recv_unlock').and(UnlockMsg.at(n)),
  }))
  .step(({n, locks, unlocks, recvLock, recvGrant, recvUnlock, held, LockMsg, UnlockMsg, GrantMsg, HoldsLock}) => ({
    LockMsg: LockMsg.set(n, when(locks, yes, when(recvLock, no, LockMsg.at(n)))),
    UnlockMsg: UnlockMsg.set(n, when(unlocks, yes, when(recvUnlock, no, UnlockMsg.at(n)))),
    GrantMsg: GrantMsg.set(n, when(recvLock, yes, when(recvGrant, no, GrantMsg.at(n)))),
    HoldsLock: HoldsLock.set(n, when(unlocks, no, when(recvGrant, yes, HoldsLock.at(n)))),
    held: when(recvLock, 1, when(recvUnlock, 0, held)),
  }))

// --- pyv-sharded-kv and pyv-sharded-kv-no-lost-keys: sharded_kv.tla, sharded_kv_no_lost_keys.tla. table[n][k] is
// Table[n·N + k] (v + 1; 0 is Nil), k \in owner[n] is Owner[k·N + n], <<n, k, v>> \in transfer_msg TransferMsg[n·N² + k·N + v].
// Init's owner, any relation with one owner a key (and, no lost keys, an owner for each of the keys 0 .. keys − 1), is
// set by `own` requests before `start` (Owned, read by `start` alone, says which keys have one).
const shardedKv = (noLost: boolean) => (bug?: Bug) => ((noLost ? rule('sharded kv no lost keys').params({keys: nat}).pre(({keys}) => keys.atMost(N)) : rule('sharded kv')) as any)
  .inputs({op: oneOf('own', 'start', 'reshard', 'recv_transfer_msg', 'put'), n: nat, k: nat, v: nat, n2: nat})
  .assume(({n, k, v, n2, keys}: any) => lt(n, v, n2).and(k.lt(noLost ? keys : N)))
  .state({started: 0})
  .maps({Table: 0, Owner: rel, TransferMsg: rel, ...(noLost ? {Owned: rel} : {})})
  .flags(({k, keys, Owner, Owned}: any) => ({
    unowned: everyKey(m => m.lt(N).implies(Owner.at(pk(k, m)).not())),
    allOwned: noLost ? everyKey(m => m.lt(keys).implies(Owned.at(m))) : yes,
  }))
  .flags(({op, n, k, v, started, unowned, allOwned, Table, Owner, TransferMsg}: any) => ({
    owns: op.is('own').and(started.eq(0), unowned),
    starts: op.is('start').and(started.eq(0), allOwned),
    // Reshard(k, v, n_old, n_new) is (n, k, v, n2)
    reshards: op.is('reshard').and(started.eq(1), Table.at(pk(n, k)).eq(v.plus(1))),
    receives: op.is('recv_transfer_msg').and(started.eq(1), TransferMsg.at(pk3(n, k, v))),
    puts: op.is('put').and(started.eq(1), bug ? yes : Owner.at(pk(k, n))),
  }))
  .step(({n, k, v, n2, owns, starts, reshards, receives, puts, started, Table, Owner, TransferMsg, Owned}: any) => ({
    started: when(starts, 1, started),
    Table: Table.set(pk(n, k), when(reshards, 0, when(receives.or(puts), v.plus(1), Table.at(pk(n, k))))),
    Owner: Owner.set(pk(k, n), when(owns.or(receives), yes, when(reshards, no, Owner.at(pk(k, n))))),
    TransferMsg: TransferMsg.each(z => when(reshards.and(z.eq(pk3(n2, k, v))), yes, when(receives.and(z.eq(pk3(n, k, v))), no, TransferMsg.at(z)))),
    ...(noLost ? {Owned: Owned.set(k, when(owns, yes, Owned.at(k)))} : {}),
  }))

// --- pyv-lockserv: lockserv.tla. One server: server_holds_lock is a scalar (1 at first).
const lockserv = (bug?: Bug) => rule('lockserv')
  .inputs({op: oneOf('send_lock', 'recv_lock', 'recv_grant', 'unlock', 'recv_unlock'), n: nat}).assume(({n}) => n.lt(N))
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

// --- tla-twophase: TwoPhase.tla. rmState as tcommit's; tmState init 0, committed 1, aborted 2; msgs: Prepared(rm) is
// PreparedMsg[rm], Commit and Abort two scalars. RM is 0 .. size − 1 (tmPrepared = RM reads every RM).
const twoPhase = (bug?: Bug) => rule('two phase')
  .params({size: nat}).pre(({size}) => size.atMost(N))
  .inputs({op: oneOf('tm_rcv_prepared', 'tm_commit', 'tm_abort', 'rm_prepare', 'rm_choose_to_abort', 'rm_rcv_commit_msg', 'rm_rcv_abort_msg'), rm: nat})
  .assume(({rm, size}) => rm.lt(size))
  .state({tm: 0, commitMsg: 0, abortMsg: 0})
  .maps({Rm: few(3), TmPrepared: rel, PreparedMsg: rel})
  .flags(({size, TmPrepared}) => ({allPrepared: everyKey(k => k.lt(size).implies(TmPrepared.at(k)))}))
  .flags(({op, rm, tm, commitMsg, abortMsg, allPrepared, Rm, PreparedMsg}) => ({
    rcvPrepared: op.is('tm_rcv_prepared').and(tm.eq(0), PreparedMsg.at(rm)),
    tmCommits: op.is('tm_commit').and(tm.eq(0), bug ? yes : allPrepared),
    tmAborts: op.is('tm_abort').and(tm.eq(0)),
    prepares: op.is('rm_prepare').and(Rm.at(rm).eq(0)),
    choosesAbort: op.is('rm_choose_to_abort').and(Rm.at(rm).eq(0)),
    rcvCommit: op.is('rm_rcv_commit_msg').and(commitMsg.eq(1), Rm.at(rm).eq(2).not()),
    rcvAbort: op.is('rm_rcv_abort_msg').and(abortMsg.eq(1), Rm.at(rm).eq(3).not()),
  }))
  .step(({rm, rcvPrepared, tmCommits, tmAborts, prepares, choosesAbort, rcvCommit, rcvAbort, tm, commitMsg, abortMsg, Rm, TmPrepared, PreparedMsg}) => ({
    tm: when(tmCommits, 1, when(tmAborts, 2, tm)),
    commitMsg: when(tmCommits, 1, commitMsg),
    abortMsg: when(tmAborts, 1, abortMsg),
    Rm: Rm.set(rm, when(prepares, 1, when(choosesAbort.or(rcvAbort), 3, when(rcvCommit, 2, Rm.at(rm))))),
    TmPrepared: TmPrepared.set(rm, when(rcvPrepared, yes, TmPrepared.at(rm))),
    PreparedMsg: PreparedMsg.set(rm, when(prepares, yes, PreparedMsg.at(rm))),
  }))

// --- ex-simple-decentralized-lock: simple_decentralized_lock.tla. Init's `\E start \in Node: has_lock = {start}` is an
// `init` request naming start (src).
const simpleDecentralizedLock = (bug?: Bug) => rule('simple decentralized lock')
  .inputs({op: oneOf('init', 'send', 'recv'), src: nat, dst: nat}).assume(({src, dst}) => lt(src, dst))
  .state({started: 0})
  .maps({Message: rel, HasLock: rel})
  .flags(({op, src, dst, started, Message, HasLock}) => ({
    inits: op.is('init').and(started.eq(0)),
    sends: op.is('send').and(started.eq(1), HasLock.at(src)),
    recvs: op.is('recv').and(started.eq(1), Message.at(pk(src, dst))),
  }))
  .step(({src, dst, inits, sends, recvs, started, Message, HasLock}) => ({
    started: when(inits, 1, started),
    Message: Message.set(pk(src, dst), when(sends, yes, when(recvs, no, Message.at(pk(src, dst))))),
    HasLock: HasLock.each(k => when(inits.and(k.eq(src)), yes, when(sends.and(k.eq(src)), bug ? HasLock.at(k) : no, when(recvs.and(k.eq(dst)), yes, HasLock.at(k))))),
  }))

// --- i4-two-phase-commit: two_phase_commit.tla (I4's). Node is 0 .. size − 1 (Go1 and Go2 read every node); Go2's
// `\E n: vote_no(n) \/ ~alive(n)` names that node (w).
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
    g2: op.is('go2').and(noGo, VoteNo.at(w).or(Alive.at(w).not())),
    commits: op.is('commit').and(Alive.at(n), GoCommit.at(n)),
    aborts: op.is('abort').and(Alive.at(n), GoAbort.at(n)),
  }))
  .step(({n, size, v1, v2, fails, g1, g2, commits, aborts, abortFlag, VoteYes, VoteNo, Alive, GoCommit, GoAbort, DecideCommit, DecideAbort}) => ({
    abortFlag: when(v2.or(fails), 1, abortFlag),
    VoteYes: VoteYes.set(n, when(v1, yes, VoteYes.at(n))),
    VoteNo: VoteNo.set(n, when(v2, yes, VoteNo.at(n))),
    Alive: Alive.set(n, when(fails, no, Alive.at(n))),
    // go_commit' = Node: every node 0 .. size − 1
    GoCommit: GoCommit.each(k => when(g1.and(k.lt(size)), yes, GoCommit.at(k))),
    GoAbort: GoAbort.each(k => when(g2.and(k.lt(size)), yes, GoAbort.at(k))),
    DecideCommit: DecideCommit.set(n, when(commits, yes, DecideCommit.at(n))),
    DecideAbort: DecideAbort.set(n, when(v2.or(aborts), yes, DecideAbort.at(n))),
  }))

// --- pyv-consensus-wo-decide and pyv-consensus-forall: consensus_wo_decide.tla, consensus_forall.tla. Quorums is the
// quorum sort (the TLA+ states no intersection; its configs' quorums are the three majorities of three nodes, which
// meet). voting_quorum is a quorum, vq; Init's `voting_quorum \in Quorums` an `init` request naming it (q). BecomeLeader's
// `voting_quorum # {}` holds of every quorum (meet(q, q) is in q). <<i, j>> \in votes is Votes[i·N + j].
const consensusWo = (decide: boolean) => (bug?: Bug) => (rule(decide ? 'consensus forall' : 'consensus wo decide') as any)
  .inputs(decide ? {op: oneOf('init', 'send_request_vote', 'send_vote', 'recv_vote', 'choose_voting_quorum', 'become_leader', 'decide'), i: nat, j: nat, q: nat, v: nat}
    : {op: oneOf('init', 'send_request_vote', 'send_vote', 'recv_vote', 'choose_voting_quorum', 'become_leader'), i: nat, j: nat, q: nat})
  .assume(({i, j, v}: any) => lt(i, j, ...(decide ? [v] : [])))
  .fns({member, meet}).facts(quorumFacts)
  .state({started: 0, vq: 0})
  .maps({VoteRequestMsg: rel, Voted: rel, VoteMsg: rel, Votes: rel, Leader: rel, ...(decide ? {Decided: rel} : {})})
  .flags(({i, q, vq, Votes, Decided, member}: any) => ({
    quorumVotes: everyKey(k => member(k, q).eq(1).implies(Votes.at(pk(i, k)))),
    votingQuorumVotes: everyKey(k => member(k, vq).eq(1).implies(Votes.at(pk(i, k)))),
    ...(decide ? {undecided: everyKey(x => Decided.at(pk(i, x)).not())} : {}),
  }))
  .flags(({op, i, j, started, quorumVotes, votingQuorumVotes, undecided, Voted, VoteRequestMsg, VoteMsg, Leader}: any) => ({
    inits: op.is('init').and(started.eq(0)),
    requests: op.is('send_request_vote').and(started.eq(1)),
    // SendVote(src, dst) is (i, j)
    votes: op.is('send_vote').and(started.eq(1), bug ? yes : Voted.at(i).not(), VoteRequestMsg.at(pk(j, i))),
    // RecvVote(i, sender) is (i, j)
    receives: op.is('recv_vote').and(started.eq(1), VoteMsg.at(pk(j, i))),
    chooses: op.is('choose_voting_quorum').and(started.eq(1), quorumVotes),
    leads: op.is('become_leader').and(started.eq(1), votingQuorumVotes),
    ...(decide ? {decides: op.is('decide').and(started.eq(1), Leader.at(i), undecided)} : {}),
  }))
  .step(({i, j, q, v, inits, requests, votes, receives, chooses, leads, decides, started, vq, VoteRequestMsg, Voted, VoteMsg, Votes, Leader, Decided}: any) => ({
    started: when(inits, 1, started),
    vq: when(inits.or(chooses), q, vq),
    VoteRequestMsg: VoteRequestMsg.set(pk(i, j), when(requests, yes, VoteRequestMsg.at(pk(i, j)))),
    VoteMsg: VoteMsg.set(pk(i, j), when(votes, yes, VoteMsg.at(pk(i, j)))),
    Voted: Voted.set(i, when(votes, yes, Voted.at(i))),
    Votes: Votes.set(pk(i, j), when(receives, yes, Votes.at(pk(i, j)))),
    Leader: Leader.set(i, when(leads, yes, Leader.at(i))),
    ...(decide ? {Decided: Decided.set(pk(i, v), when(decides, yes, Decided.at(pk(i, v))))} : {}),
  }))

// --- ex-naive-consensus: naive_consensus.tla. Quorum is the quorum sort; <<n, v>> \in vote is Vote[v·N + n], and
// CastVote's `\A x: <<n, x>> \notin vote` is read through Voted[n] (every write keeps Voted[n] = ∃x vote(n, x): a node's
// votes are only added). <<Q, v>> \in decide is Decide[Q·N + v].
const naiveConsensus = (bug?: Bug) => rule('naive consensus')
  .inputs({op: oneOf('cast_vote', 'collect_votes', 'learn_value'), n: nat, v: nat, q: nat}).assume(({n, v, q}) => lt(n, v, q))
  .fns({member, meet}).facts(quorumFacts)
  .maps({Vote: rel, Voted: rel, Decide: rel, Decision: rel})
  .flags(({v, q, Vote, member}) => ({allVote: everyKey(k => member(k, q).eq(1).implies(Vote.at(pk(v, k))))}))
  .flags(({op, n, v, q, allVote, Voted, Decide}) => ({
    casts: op.is('cast_vote').and(bug ? yes : Voted.at(n).not()),
    collects: op.is('collect_votes').and(allVote),
    learns: op.is('learn_value').and(Decide.at(pk(q, v))),
  }))
  .step(({n, v, q, casts, collects, learns, Vote, Voted, Decide, Decision}) => ({
    Vote: Vote.set(pk(v, n), when(casts, yes, Vote.at(pk(v, n)))),
    Voted: Voted.set(n, when(casts, yes, Voted.at(n))),
    Decide: Decide.set(pk(q, v), when(collects, yes, Decide.at(pk(q, v)))),
    Decision: Decision.set(v, when(learns, yes, Decision.at(v))),
  }))

// --- pyv-client-server-ae and pyv-client-server-db-ae: client_server_ae.tla, client_server_db_ae.tla. match, any
// relation at Init, is set by `match` requests before `start`. <<n, r>> \in request_sent is RequestSent[n·N + r],
// <<r, p>> \in match Match[r·N + p], <<i, n>> \in t T[i·N + n] (NoneWithId(i) reads every n).
const clientServer = (db: boolean) => (bug?: Bug) => (rule(db ? 'client server db ae' : 'client server ae') as any)
  .inputs(db ? {op: oneOf('match', 'start', 'new_request', 'receive_response', 'server_process_request', 'db_process_request', 'server_process_db_response'), n: nat, r: nat, p: nat, i: nat}
    : {op: oneOf('match', 'start', 'new_request', 'respond', 'receive_response'), n: nat, r: nat, p: nat})
  .assume(({n, r, p, i}: any) => lt(n, r, p, ...(db ? [i] : [])))
  .state({started: 0})
  .maps({Match: rel, RequestSent: rel, ResponseSent: rel, ResponseReceived: rel, ...(db ? {DbRequestSent: rel, DbResponseSent: rel, T: rel} : {})})
  .flags(({i, T}: any) => (db ? {noneWithId: everyKey(m => T.at(pk(i, m)).not())} : {}))
  .flags(({op, n, r, p, i, started, noneWithId, Match, RequestSent, ResponseSent, DbRequestSent, DbResponseSent, T}: any) => ({
    matches: op.is('match').and(started.eq(0)),
    starts: op.is('start').and(started.eq(0)),
    requests: op.is('new_request').and(started.eq(1)),
    receives: op.is('receive_response').and(started.eq(1), ResponseSent.at(pk(n, p))),
    ...(db ? {
      serverRequests: op.is('server_process_request').and(started.eq(1), RequestSent.at(pk(n, r)), noneWithId),
      dbResponds: op.is('db_process_request').and(started.eq(1), DbRequestSent.at(pk(i, r)), bug ? yes : Match.at(pk(r, p))),
      serverResponds: op.is('server_process_db_response').and(started.eq(1), DbResponseSent.at(pk(i, p)), T.at(pk(i, n))),
    } : {responds: op.is('respond').and(started.eq(1), RequestSent.at(pk(n, r)), bug ? yes : Match.at(pk(r, p)))}),
  }))
  .step(({n, r, p, i, matches, starts, requests, responds, receives, serverRequests, dbResponds, serverResponds, started, Match, RequestSent, ResponseSent, ResponseReceived, DbRequestSent, DbResponseSent, T}: any) => ({
    started: when(starts, 1, started),
    Match: Match.set(pk(r, p), when(matches, yes, Match.at(pk(r, p)))),
    RequestSent: RequestSent.set(pk(n, r), when(requests, yes, RequestSent.at(pk(n, r)))),
    ResponseSent: ResponseSent.set(pk(n, p), when(db ? serverResponds : responds, yes, ResponseSent.at(pk(n, p)))),
    ResponseReceived: ResponseReceived.set(pk(n, p), when(receives, yes, ResponseReceived.at(pk(n, p)))),
    ...(db ? {
      T: T.set(pk(i, n), when(serverRequests, yes, T.at(pk(i, n)))),
      DbRequestSent: DbRequestSent.set(pk(i, r), when(serverRequests, yes, DbRequestSent.at(pk(i, r)))),
      DbResponseSent: DbResponseSent.set(pk(i, p), when(dbResponds, yes, DbResponseSent.at(pk(i, p)))),
    } : {}),
  }))

// --- ex-simple-election: simple_election.tla. Quorum (of acceptors) is the quorum sort; <<a, p>> \in promise is
// Promise[p·N + a], and DidNotPromise(a) is read through Promised[a] (kept = ∃p promise(a, p), as naive consensus's Voted).
const simpleElection = (bug?: Bug) => rule('simple election')
  .inputs({op: oneOf('send_1a', 'send_1b', 'decide'), a: nat, p: nat, q: nat}).assume(({a, p, q}) => lt(a, p, q))
  .fns({member, meet}).facts(quorumFacts)
  .maps({Start: rel, Promise: rel, Promised: rel, Leader: rel})
  .flags(({p, q, Promise, member}) => ({chosenAt: everyKey(k => member(k, q).eq(1).implies(Promise.at(pk(p, k))))}))
  .flags(({op, a, p, chosenAt, Start, Promised}) => ({
    sends1a: op.is('send_1a'),
    sends1b: op.is('send_1b').and(Start.at(p), bug ? yes : Promised.at(a).not()),
    decides: op.is('decide').and(chosenAt),
  }))
  .step(({a, p, sends1a, sends1b, decides, Start, Promise, Promised, Leader}) => ({
    Start: Start.set(p, when(sends1a, yes, Start.at(p))),
    Promise: Promise.set(pk(p, a), when(sends1b, yes, Promise.at(pk(p, a)))),
    Promised: Promised.set(a, when(sends1b, yes, Promised.at(a))),
    Leader: Leader.set(p, when(decides, yes, Leader.at(p))),
  }))

// --- pyv-toy-consensus-epr: toy_consensus_epr.tla. Quorum is the quorum sort; <<n, v>> \in vote is Vote[v·N + n].
const toyEpr = (bug?: Bug) => rule('toy consensus epr')
  .inputs({op: oneOf('cast_vote', 'decide'), n: nat, v: nat, q: nat}).assume(({n, v, q}) => lt(n, v, q))
  .fns({member, meet}).facts(quorumFacts)
  .maps({Voted: rel, Vote: rel, Decided: rel})
  .flags(({v, q, Vote, member}) => ({chosenAt: everyKey(k => member(k, q).eq(1).implies(Vote.at(pk(v, k))))}))
  .flags(({op, n, chosenAt, Voted}) => ({casts: op.is('cast_vote').and(bug ? yes : Voted.at(n).not()), decides: op.is('decide').and(chosenAt)}))
  .step(({n, v, casts, decides, Voted, Vote, Decided}) => ({
    Vote: Vote.set(pk(v, n), when(casts, yes, Vote.at(pk(v, n)))),
    Voted: Voted.set(n, when(casts, yes, Voted.at(n))),
    Decided: Decided.set(v, when(decides, yes, Decided.at(v))),
  }))

// --- ex-toy-consensus: toy_consensus.tla. vote[i] is Vote[i] (v + 1; 0 is Nil); Node is 0 .. size − 1; Decide(v, Q) for a
// majority Q (the @q cut: a quorum q).
const toyConsensus = (axiom: boolean) => (bug?: Bug) => quorumOrMajority(rule('toy consensus'), axiom, 'decide', {v: nat}, ({v}: any) => v.lt(N))
  .maps({Vote: 0, Decision: rel})
  .flags(({v, q, Q, Vote, member}: any) => ({chosenAt: everyKey(k => inQuorum(axiom, k, q, Q, member).implies(Vote.at(k).eq(v.plus(1))))}))
  .flags(({op, i, chosenAt, Vote}: any) => ({casts: op.is('cast_vote').and(bug ? yes : Vote.at(i).eq(0)), decides: op.is('decide').and(chosenAt)}))
  .step(({i, v, casts, decides, Vote, Decision}: any) => ({
    Vote: Vote.set(i, when(casts, v.plus(1), Vote.at(i))),
    Decision: Decision.set(v, when(decides, yes, Decision.at(v))),
  }))

// --- pyv-firewall: firewall.tla. internal, any function at Init, is set by `internal` requests before `start`;
// d \in sent[s] is Sent[s·N + d].
const firewall = (bug?: Bug) => rule('firewall')
  .inputs({op: oneOf('internal', 'start', 'send_from_internal', 'send_to_internal'), s: nat, d: nat}).assume(({s, d}) => lt(s, d))
  .state({started: 0})
  .maps({Internal: rel, Sent: rel, AllowedIn: rel})
  .flags(({op, s, d, started, Internal, AllowedIn}) => ({
    marks: op.is('internal').and(started.eq(0)),
    starts: op.is('start').and(started.eq(0)),
    fromInternal: op.is('send_from_internal').and(started.eq(1), Internal.at(s), Internal.at(d).not()),
    toInternal: op.is('send_to_internal').and(started.eq(1), Internal.at(s).not(), Internal.at(d), bug ? yes : AllowedIn.at(s)),
  }))
  .step(({s, d, marks, starts, fromInternal, toInternal, started, Internal, Sent, AllowedIn}) => ({
    started: when(starts, 1, started),
    Internal: Internal.set(s, when(marks, yes, Internal.at(s))),
    Sent: Sent.set(pk(s, d), when(fromInternal.or(toInternal), yes, Sent.at(pk(s, d)))),
    AllowedIn: AllowedIn.set(d, when(fromInternal, yes, AllowedIn.at(d))),
  }))

// --- ex-majorityset-leader-election: majorityset_leader_election.tla. n2 \in vote[n1] is Vote[n1·N + n2], v \in voters[n]
// Voters[n·N + v], leader a set; Node is 0 .. size − 1. ReceiveVote(voter, n, vs) and BecomeLeader(n, vs) name vs =
// voters[n], so neither carries it; BecomeLeader's vs \in Majority is majority() of the row voters[n] (the @q cut: the
// row holds a quorum q).
const majoritySet = (axiom: boolean) => (bug?: Bug) => {
  const ops = {op: oneOf('voting', 'receive_vote', 'become_leader'), n: nat, m: nat}
  const base: any = rule('majorityset leader election').params({size: nat}).pre(({size}) => size.atMost(N))
  const r: any = axiom ? base.inputs({...ops, q: nat}).fns({member, meet}).facts(quorumFacts) : base.inputs({...ops, c: nat}).carries('Out')
  return r.maps({Vote: rel, Voters: rel, Leader: rel})
  .assume(({op, n, m, c, size, Out, Voters}: any) => n.lt(size).and(m.lt(size), axiom ? yes : op.is('become_leader')
    .implies(majority({at: (k: Term) => Voters.at(pk(n, k)).n, has: (k: Term) => Voters.at(pk(n, k))}, Out, c, size))))
  .flags(({n, q, Vote, Voters, member}: any) => ({
    didNotVote: everyKey(x => Vote.at(pk(n, x)).not()),
    holdsQuorum: axiom ? everyKey(k => member(k, q).eq(1).implies(Voters.at(pk(n, k)))) : yes,
  }))
  .flags(({op, n, m, didNotVote, holdsQuorum, Vote, Voters}: any) => ({
    // Voting(n1, n2) is (n, m); ReceiveVote(voter, n, vs) is (m, n)
    votes: op.is('voting').and(bug ? yes : didNotVote),
    receives: op.is('receive_vote').and(Vote.at(pk(m, n)), Voters.at(pk(n, m)).not()),
    leads: op.is('become_leader').and(holdsQuorum),
  }))
  .step(({n, m, votes, receives, leads, Vote, Voters, Leader}: any) => ({
    Vote: Vote.set(pk(n, m), when(votes, yes, Vote.at(pk(n, m)))),
    Voters: Voters.set(pk(n, m), when(receives, yes, Voters.at(pk(n, m)))),
    Leader: Leader.set(n, when(leads, yes, Leader.at(n))),
  }))
}

// --- pyv-consensus-epr: consensus_epr.tla. Quorum is the quorum sort; sender \in votes[n] is Votes[n·N + sender],
// v \in decided[n] Decided[n·N + v]; SendVote's `vote_request_msg' = ... \cup or \ {<<src, dst>>}` is `nondet`.
const consensusEpr = (bug?: Bug) => rule('consensus epr')
  .inputs({op: oneOf('send_request_vote', 'send_vote', 'recv_vote', 'become_leader', 'decide'), i: nat, j: nat, q: nat, v: nat, nondet: nat})
  .assume(({i, j, q, v, nondet}) => lt(i, j, q, v).and(nondet.atMost(1)))
  .fns({member, meet}).facts(quorumFacts)
  .maps({VoteRequestMsg: rel, Voted: rel, VoteMsg: rel, Votes: rel, Leader: rel, Decided: rel})
  .flags(({i, q, Votes, Decided, member}) => ({
    quorumVotes: everyKey(k => member(k, q).eq(1).implies(Votes.at(pk(i, k)))),
    undecided: everyKey(x => Decided.at(pk(i, x)).not()),
  }))
  .flags(({op, i, j, quorumVotes, undecided, Voted, VoteRequestMsg, VoteMsg, Leader}) => ({
    requests: op.is('send_request_vote'),
    // SendVote(src, dst) and RecvVote(n, sender) are (i, j)
    votes: op.is('send_vote').and(bug ? yes : Voted.at(i).not(), VoteRequestMsg.at(pk(j, i))),
    receives: op.is('recv_vote').and(VoteMsg.at(pk(j, i))),
    leads: op.is('become_leader').and(quorumVotes),
    decides: op.is('decide').and(Leader.at(i), undecided),
  }))
  .step(({i, j, v, nondet, requests, votes, receives, leads, decides, VoteRequestMsg, Voted, VoteMsg, Votes, Leader, Decided}) => ({
    VoteRequestMsg: VoteRequestMsg.set(pk(i, j), when(requests, yes, when(votes, nondet.eq(1), VoteRequestMsg.at(pk(i, j))))),
    VoteMsg: VoteMsg.set(pk(i, j), when(votes, yes, VoteMsg.at(pk(i, j)))),
    Voted: Voted.set(i, when(votes, yes, Voted.at(i))),
    Votes: Votes.set(pk(i, j), when(receives, yes, Votes.at(pk(i, j)))),
    Leader: Leader.set(i, when(leads, yes, Leader.at(i))),
    Decided: Decided.set(pk(i, v), when(decides, yes, Decided.at(pk(i, v)))),
  }))

// --- the protocols, with their safety laws, their instances and their TLC cfgs --------------------------------------
const one = (name: string, map: string) => (r: any) => [r.law(name, (env: any) => forall((a, b) => lt(a, b).and(env[map].at(a), env[map].at(b)).implies(a.eq(b))))]
const mutex = one('one holder', 'HoldsLock')
const N3 = range(3), N2 = range(2)

export const protocols: Protocol[] = [
  {id: 'consensus', ic3syn: 'tla-consensus', file: 'Consensus.tla', source: 'Endive benchmarks/Consensus.tla (Lamport\'s Consensus)', safety: 'Cardinality(chosen) <= 1',
    make: consensus, bug: 'Next without chosen = {}', laws: one('at most one value chosen', 'Chosen'),
    bad: r => twoDistinct(r, 'Chosen', N3),
    check: {inputs: {v: N3}, project: r => cells(r, 'Chosen', N3), tlc: tlc('Consensus', consts({Value: nodes(3, 'v')}), 'Inv')}},
  {id: 'tcommit', ic3syn: 'tla-tcommit', file: 'TCommit.tla', source: 'Endive benchmarks/TCommit.tla (Lamport\'s TCommit)', safety: '~(rmState[rm1] = "aborted" /\\ rmState[rm2] = "committed")',
    make: tcommit, bug: 'commit without canCommit',
    laws: r => [r.law('commit and abort exclude', ({size, St}: any) => forall((a, b) => a.lt(size).and(b.lt(size)).implies(St.at(a).eq(3).and(St.at(b).eq(2)).not())))],
    bad: r => cells(r, 'St', N3).includes(3) && cells(r, 'St', N3).includes(2),
    check: {params: {size: 3}, inputs: {op: range(3), rm: N3}, project: r => cells(r, 'St', N3), tlc: tlc('TCommit', consts({RM: nodes(3, 'rm')}), 'TCConsistent')}},
  {id: 'lock_server', ic3syn: 'i4-lock-server', file: 'lockserver.tla', source: 'Endive benchmarks/lockserver.tla (I4\'s lock server)', safety: 'clientlocks[ci] \\cap clientlocks[cj] # {} => ci = cj',
    make: lockServer, bug: 'connect without the semaphore',
    laws: r => [r.law('one client per server', ({Link}: any) => forall((c1, c2, s) => lt(c1, c2, s).and(Link.at(pk(c1, s)), Link.at(pk(c2, s))).implies(c1.eq(c2))))],
    bad: r => N2.some(s => twoDistinct(r, 'Link', N2.map(c => c * N + s))),
    check: {inputs: {op: range(2), c: N2, s: N2}, project: r => [cells(r, 'Semaphore', N2), cells(r, 'Link', pairs(N2, N2))],
      tlc: tlc('lockserver', consts({Server: nodes(2, 's'), Client: nodes(2, 'c')}, {Nil: 'Nil'}), 'Inv')}},
  ...[false, true].map((axiom): Protocol => ({id: `quorum_leader_election${axiom ? '@q' : ''}`, ic3syn: 'ex-quorum-leader-election', file: 'quorum_leader_election.tla',
    source: 'Endive benchmarks/quorum_leader_election.tla', safety: 'isleader[i] /\\ isleader[j] => i = j',
    make: quorumLeader(axiom), bug: 'vote twice',
    laws: r => [r.law('one leader', ({size, IsLeader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), IsLeader.at(a), IsLeader.at(b)).implies(a.eq(b))))],
    bad: r => twoDistinct(r, 'IsLeader', N3),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, j: N3, ...(axiom ? {q: N3} : {qm: range(8)})}, ...(axiom ? {} : {expand: withMajority(3)}),
      project: r => [cells(r, 'IsLeader', N3), cells(r, 'Voted', N3)], tlc: tlc('quorum_leader_election', consts({Node: nodes(3)}, {Nil: 'Nil'}), 'Inv')}})),
  ...[false, true].map((axiom): Protocol => ({id: `toy_consensus_forall${axiom ? '@q' : ''}`, ic3syn: 'pyv-toy-consensus-forall', file: 'toy_consensus_forall.tla',
    source: 'Endive benchmarks/toy_consensus_forall.tla (mypyvy\'s)', safety: '\\A vi, vj \\in decided: vi = vj',
    make: toyForall(axiom), bug: 'cast_vote without voted', laws: one('one value decided', 'Decided'),
    bad: r => twoDistinct(r, 'Decided', N2),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, v: N2, ...(axiom ? {q: N3} : {qm: range(8)})}, ...(axiom ? {} : {expand: withMajority(3)}),
      project: r => [cells(r, 'Vote', N3), cells(r, 'Voted', N3), cells(r, 'Decided', N2)],
      tlc: tlc('toy_consensus_forall', consts({Node: nodes(3), Value: nodes(2, 'v')}, {Nil: 'Nil'}), 'Inv')}})),
  ...[false, true].map((regular): Protocol => {
    const n = regular ? 3 : 4, P = range(n)
    return {id: regular ? 'simple_regular' : 'simple', ic3syn: regular ? 'tla-simpleregular' : 'tla-simple', file: regular ? 'SimpleRegular.tla' : 'Simple.tla',
      source: `Endive benchmarks/${regular ? 'SimpleRegular' : 'Simple'}.tla (Lamport's)`, safety: '(\\A i: pc[i] = "Done") => \\E i: y[i] = 1',
      make: simple(regular), bug: regular ? 'a2 leaves x = {0, 1}' : 'a leaves x',
      laws: r => [r.law('some process not done, or some y is 1', ({n: size, Pc, Y}: any) => exists(i => i.lt(size).and(Pc.at(i).eq(regular ? 3 : 2).not().or(Y.at(i).eq(1)))))],
      bad: r => P.every(i => r.cell('Pc', i) === (regular ? 3 : 2)) && P.every(i => r.cell('Y', i) === 0),
      check: {params: {n}, inputs: {op: regular ? range(3) : [0, 2], self: P, v: [0, 1]}, project: r => [cells(r, 'X', P), cells(r, 'Y', P), cells(r, 'Pc', P)],
        tlc: tlc(regular ? 'SimpleRegular' : 'Simple', `CONSTANTS\n  N = ${n}\n`, 'PCorrect')}}
  }),
  {id: 'lockserv_automaton', ic3syn: 'ex-lockserv-automaton', file: 'lockserv_automaton.tla', source: 'Endive benchmarks/lockserv_automaton.tla', safety: 'holds_lock[x] /\\ holds_lock[y] => x = y',
    make: lockservAutomaton, bug: 'recv_lock while held', laws: mutex, bad: r => twoDistinct(r, 'HoldsLock', N3),
    check: {inputs: {op: range(5), n: N3}, project: r => [['LockMsg', 'UnlockMsg', 'GrantMsg', 'HoldsLock'].map(m => cells(r, m, N3)), r.scalar('held')],
      tlc: tlc('lockserv_automaton', consts({Node: nodes(3)}), 'Mutex')}},
  ...[false, true].map((noLost): Protocol => ({id: noLost ? 'sharded_kv_no_lost_keys' : 'sharded_kv', ic3syn: noLost ? 'pyv-sharded-kv-no-lost-keys' : 'pyv-sharded-kv',
    file: noLost ? 'sharded_kv_no_lost_keys.tla' : 'sharded_kv.tla', source: `Endive benchmarks/${noLost ? 'sharded_kv_no_lost_keys' : 'sharded_kv'}.tla (mypyvy's)`,
    safety: noLost ? '(\\E n, k, v: <<n, k, v>> \\in transfer_msg) \\/ (\\A k: \\E n: k \\in owner[n])' : 'table[n1][k] = v1 /\\ table[n2][k] = v2 => n1 = n2 /\\ v1 = v2',
    make: shardedKv(noLost), bug: noLost ? 'reshard without the transfer message' : 'put without ownership',
    laws: r => [noLost
      ? r.law('a transfer in flight, or every key owned', ({keys, started, Owner, TransferMsg}: any) => forall(k => k.lt(keys).and(started.eq(1)).implies(
        exists(x => x.lt(N).and(Owner.at(pk(k, x)))).or(exists(z => TransferMsg.at(z))))))
      : r.law('one value per key', ({Table}: any) => forall((a, b, k, v, u) => lt(a, b, k, v, u).and(Table.at(pk(a, k)).eq(v.plus(1)), Table.at(pk(b, k)).eq(u.plus(1))).implies(a.eq(b).and(v.eq(u)))))],
    bad: noLost
      ? r => r.scalar('started') === 1 && !triples(N2, N2, N2).some(z => r.cell('TransferMsg', z)) && N2.some(k => !N2.some(n => r.cell('Owner', k * N + n)))
      : r => N2.some(k => N2.flatMap(n => r.cell('Table', n * N + k) ? [n] : []).length > 1),
    check: {params: noLost ? {keys: 2} : {}, inputs: {op: range(5), n: N2, k: N2, v: N2, n2: N2},
      project: r => r.scalar('started') ? [cells(r, 'Table', pairs(N2, N2)), cells(r, 'Owner', pairs(N2, N2)), cells(r, 'TransferMsg', triples(N2, N2, N2))] : undefined,
      tlc: tlc(noLost ? 'sharded_kv_no_lost_keys' : 'sharded_kv', consts({Node: nodes(2), Key: nodes(2, 'k'), Value: nodes(2, 'v')}, {Nil: 'Nil'}), 'Safety')}})),
  {id: 'lockserv', ic3syn: 'pyv-lockserv', file: 'lockserv.tla', source: 'Endive benchmarks/lockserv.tla (mypyvy\'s lockserv)', safety: 'holds_lock[x] /\\ holds_lock[y] => x = y',
    make: lockserv, bug: 'recv_lock without server_holds_lock', laws: mutex, bad: r => twoDistinct(r, 'HoldsLock', N3),
    check: {inputs: {op: range(5), n: N3}, project: r => [['LockMsg', 'GrantMsg', 'UnlockMsg', 'HoldsLock'].map(m => cells(r, m, N3)), r.scalar('serverHoldsLock')],
      tlc: tlc('lockserv', consts({Node: nodes(3)}), 'Mutex')}},
  {id: 'twophase', ic3syn: 'tla-twophase', file: 'TwoPhase.tla', source: 'Endive benchmarks/TwoPhase.tla (Lamport\'s TwoPhase)', safety: '~(rmState[rm1] = "aborted" /\\ rmState[rm2] = "committed")',
    make: twoPhase, bug: 'tm_commit before every RM is prepared',
    laws: r => [r.law('commit and abort exclude', ({size, Rm}: any) => forall((a, b) => a.lt(size).and(b.lt(size)).implies(Rm.at(a).eq(3).and(Rm.at(b).eq(2)).not())))],
    bad: r => cells(r, 'Rm', N3).includes(3) && cells(r, 'Rm', N3).includes(2),
    check: {params: {size: 3}, inputs: {op: range(7), rm: N3}, project: r => [cells(r, 'Rm', N3), r.scalar('tm'), cells(r, 'TmPrepared', N3), cells(r, 'PreparedMsg', N3), r.scalar('commitMsg'), r.scalar('abortMsg')],
      tlc: tlc('TwoPhase', consts({RM: nodes(3, 'rm')}), 'TCConsistent')}},
  {id: 'simple_decentralized_lock', ic3syn: 'ex-simple-decentralized-lock', file: 'simple_decentralized_lock.tla', source: 'Endive benchmarks/simple_decentralized_lock.tla', safety: 'x \\in has_lock /\\ y \\in has_lock => x = y',
    make: simpleDecentralizedLock, bug: 'send keeps the lock', laws: one('one node holds the lock', 'HasLock'), bad: r => twoDistinct(r, 'HasLock', N3),
    check: {inputs: {op: range(3), src: N3, dst: N3}, project: r => r.scalar('started') ? [cells(r, 'HasLock', N3), cells(r, 'Message', pairs(N3, N3))] : undefined,
      tlc: tlc('simple_decentralized_lock', consts({Node: nodes(3)}), 'Inv')}},
  {id: 'two_phase_commit', ic3syn: 'i4-two-phase-commit', file: 'two_phase_commit.tla', source: 'Endive benchmarks/two_phase_commit.tla (I4\'s)',
    safety: '(n \\in decide_commit => n2 \\notin decide_abort) /\\ (n \\in decide_commit => n2 \\in vote_yes) /\\ (n \\in decide_abort => abort_flag)',
    make: twoPhaseCommit, bug: 'go1 without every yes vote',
    laws: r => [r.law('commit and abort agree', ({size, abortFlag, VoteYes, DecideCommit, DecideAbort}: any) => forall((a, b) => a.lt(size).and(b.lt(size)).implies(
      DecideCommit.at(a).implies(DecideAbort.at(b).not().and(VoteYes.at(b))).and(DecideAbort.at(a).implies(abortFlag.eq(1))))))],
    bad: r => (N3.some(a => r.cell('DecideCommit', a)) && N3.some(b => r.cell('DecideAbort', b) || !r.cell('VoteYes', b))) || (N3.some(a => r.cell('DecideAbort', a)) && !r.scalar('abortFlag')),
    check: {params: {size: 3}, inputs: {op: range(7), n: N3, w: N3},
      project: r => [['VoteYes', 'VoteNo', 'Alive', 'GoCommit', 'GoAbort', 'DecideCommit', 'DecideAbort'].map(m => cells(r, m, N3)), r.scalar('abortFlag')],
      tlc: tlc('two_phase_commit', consts({Node: nodes(3)}), 'Safety')}},
  ...[false, true].map((decide): Protocol => ({id: decide ? 'consensus_forall' : 'consensus_wo_decide', ic3syn: decide ? 'pyv-consensus-forall' : 'pyv-consensus-wo-decide',
    file: decide ? 'consensus_forall.tla' : 'consensus_wo_decide.tla', source: `Endive benchmarks/${decide ? 'consensus_forall' : 'consensus_wo_decide'}.tla (mypyvy's)`,
    safety: decide ? '<<n1, v1>> \\in decided /\\ <<n2, v2>> \\in decided => v1 = v2' : 'leader[i] /\\ leader[j] => i = j',
    make: consensusWo(decide), bug: 'send_vote without voted',
    laws: decide
      ? r => [r.law('one value decided', ({Decided}: any) => forall((a, b, v, u) => lt(a, b, v, u).and(Decided.at(pk(a, v)), Decided.at(pk(b, u))).implies(v.eq(u))))]
      : one('one leader', 'Leader'),
    bad: decide ? r => new Set(N3.flatMap(n => N2.filter(v => r.cell('Decided', n * N + v)))).size > 1 : r => twoDistinct(r, 'Leader', N3),
    check: {inputs: {op: decide ? range(7) : range(6), i: N3, j: N3, q: N3, v: decide ? N2 : [0]},
      project: r => r.scalar('started') ? [['VoteRequestMsg', 'VoteMsg', 'Votes'].map(m => cells(r, m, pairs(N3, N3))), cells(r, 'Voted', N3), cells(r, 'Leader', N3), r.scalar('vq'), cells(r, 'Decided', pairs(N3, N2))] : undefined,
      tlc: tlc(decide ? 'consensus_forall' : 'consensus_wo_decide', `${consts({Node: nodes(3), ...(decide ? {Value: nodes(2, 'v')} : {})})}  ${decide ? 'Quorum' : 'Quorums'} = {{n1, n2}, {n2, n3}, {n1, n3}}\n`, 'Safety')}})),
  {id: 'naive_consensus', ic3syn: 'ex-naive-consensus', file: 'naive_consensus.tla', source: 'Endive benchmarks/naive_consensus.tla', safety: 'v1 \\in decision /\\ v2 \\in decision => v1 = v2',
    make: naiveConsensus, bug: 'cast_vote twice', laws: one('one value decided', 'Decision'), bad: r => twoDistinct(r, 'Decision', N2),
    check: {inputs: {op: range(3), n: N3, v: N2, q: N3}, project: r => [cells(r, 'Vote', pairs(N2, N3)), cells(r, 'Decide', pairs(N3, N2)), cells(r, 'Decision', N2)],
      tlc: tlc('naive_consensus', `${consts({Node: nodes(3), Value: nodes(2, 'v')})}  Quorum = {{n1, n2}, {n2, n3}, {n1, n3}}\n`, 'Safety')}},
  ...[false, true].map((db): Protocol => {
    const Ns = N2, R = N2, P = N2, I = N2
    return {id: db ? 'client_server_db_ae' : 'client_server_ae', ic3syn: db ? 'pyv-client-server-db-ae' : 'pyv-client-server-ae', file: db ? 'client_server_db_ae.tla' : 'client_server_ae.tla',
      source: `Endive benchmarks/${db ? 'client_server_db_ae' : 'client_server_ae'}.tla (mypyvy's)`, safety: '<<n, p>> \\in response_received => \\E r: <<n, r>> \\in request_sent /\\ <<r, p>> \\in match',
      make: clientServer(db), bug: db ? 'db_process_request without match' : 'respond without match',
      laws: r => [r.law('a received response was matched', ({RequestSent, Match, ResponseReceived}: any) => forall((n, p) => lt(n, p).and(ResponseReceived.at(pk(n, p))).implies(
        exists(x => x.lt(N).and(RequestSent.at(pk(n, x)), Match.at(pk(x, p)))))))],
      bad: r => Ns.some(n => P.some(p => r.cell('ResponseReceived', n * N + p) && !R.some(x => r.cell('RequestSent', n * N + x) && r.cell('Match', x * N + p)))),
      check: {inputs: {op: db ? range(7) : range(5), n: Ns, r: R, p: P, ...(db ? {i: I} : {})},
        project: r => r.scalar('started') ? [['Match', 'RequestSent', 'ResponseSent', 'ResponseReceived'].map(m => cells(r, m, pairs(N2, N2))),
          ...(db ? [['DbRequestSent', 'DbResponseSent', 'T'].map(m => cells(r, m, pairs(N2, N2)))] : [])] : undefined,
        tlc: tlc(db ? 'client_server_db_ae' : 'client_server_ae', consts({Node: nodes(2), Request: nodes(2, 'r'), Response: nodes(2, 'p'), ...(db ? {DbRequestId: nodes(2, 'i')} : {})}), 'Safety')}}
  }),
  {id: 'simple_election', ic3syn: 'ex-simple-election', file: 'simple_election.tla', source: 'Endive benchmarks/simple_election.tla', safety: 'pi \\in leader /\\ pj \\in leader => pi = pj',
    make: simpleElection, bug: 'send_1b after a promise', laws: one('one leader', 'Leader'), bad: r => twoDistinct(r, 'Leader', N2),
    check: {inputs: {op: range(3), a: N3, p: N2, q: N3}, project: r => [cells(r, 'Start', N2), cells(r, 'Promise', pairs(N2, N3)), cells(r, 'Leader', N2)],
      tlc: tlc('simple_election', `${consts({Acceptor: nodes(3, 'a'), Proposer: nodes(2, 'p')})}  Quorum = {{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}\n`, 'Safety')}},
  {id: 'toy_consensus_epr', ic3syn: 'pyv-toy-consensus-epr', file: 'toy_consensus_epr.tla', source: 'Endive benchmarks/toy_consensus_epr.tla (mypyvy\'s)', safety: '\\A vi, vj \\in decided: vi = vj',
    make: toyEpr, bug: 'cast_vote twice', laws: one('one value decided', 'Decided'), bad: r => twoDistinct(r, 'Decided', N2),
    check: {inputs: {op: range(2), n: N3, v: N2, q: N3}, project: r => [cells(r, 'Voted', N3), cells(r, 'Vote', pairs(N2, N3)), cells(r, 'Decided', N2)],
      tlc: tlc('toy_consensus_epr', `${consts({Node: nodes(3), Value: nodes(2, 'v')}, {Nil: 'Nil'})}  Quorum = {{n1, n2}, {n1, n3}, {n2, n3}}\n`, 'Safety')}},
  ...[false, true].map((axiom): Protocol => ({id: `toy_consensus${axiom ? '@q' : ''}`, ic3syn: 'ex-toy-consensus', file: 'toy_consensus.tla', source: 'Endive benchmarks/toy_consensus.tla',
    safety: '\\A vi, vj \\in decision: vi = vj', make: toyConsensus(axiom), bug: 'cast_vote twice', laws: one('one value decided', 'Decision'), bad: r => twoDistinct(r, 'Decision', N2),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, v: N2, ...(axiom ? {q: N3} : {qm: range(8)})}, ...(axiom ? {} : {expand: withMajority(3)}),
      project: r => [cells(r, 'Vote', N3), cells(r, 'Decision', N2)], tlc: tlc('toy_consensus', consts({Node: nodes(3), Value: nodes(2, 'v')}, {Nil: 'Nil'}), 'Inv')}})),
  {id: 'firewall', ic3syn: 'pyv-firewall', file: 'firewall.tla', source: 'Endive benchmarks/firewall.tla (mypyvy\'s)', safety: 'd \\in sent[s] /\\ internal[d] => \\E i: internal[i] /\\ s \\in sent[i]',
    make: firewall, bug: 'send_to_internal without allowed_in',
    laws: r => [r.law('a sender to the inside was sent to from the inside', ({Internal, Sent}: any) => forall((s, d) => lt(s, d).and(Sent.at(pk(s, d)), Internal.at(d)).implies(
      exists(x => x.lt(N).and(Internal.at(x), Sent.at(pk(x, s)))))))],
    bad: r => N3.some(s => N3.some(d => r.cell('Sent', s * N + d) && r.cell('Internal', d) && !N3.some(i => r.cell('Internal', i) && r.cell('Sent', i * N + s)))),
    check: {inputs: {op: range(4), s: N3, d: N3}, project: r => r.scalar('started') ? [cells(r, 'Internal', N3), cells(r, 'Sent', pairs(N3, N3)), cells(r, 'AllowedIn', N3)] : undefined,
      tlc: tlc('firewall', consts({Node: nodes(3)}), 'Inv')}},
  ...[false, true].map((axiom): Protocol => ({id: `majorityset_leader_election${axiom ? '@q' : ''}`, ic3syn: 'ex-majorityset-leader-election', file: 'majorityset_leader_election.tla',
    source: 'Endive benchmarks/majorityset_leader_election.tla', safety: 'x \\in leader /\\ y \\in leader => x = y', make: majoritySet(axiom), bug: 'vote twice',
    laws: r => [r.law('one leader', ({size, Leader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))],
    bad: r => twoDistinct(r, 'Leader', N3),
    check: {params: {size: 3}, inputs: {op: range(3), n: N3, m: N3, ...(axiom ? {q: N3} : {})},
      // (a majority of three leaves one node out at most: c = 0, or c = 1 and every rank 0)
      ...(axiom ? {} : {expand: (i: any) => [{...i, Out: new Map(), c: 0}, {...i, c: 1, Out: new Map(N3.map(k => [k, 0] as [number, number]))}]}),
      project: r => [cells(r, 'Vote', pairs(N3, N3)), cells(r, 'Voters', pairs(N3, N3)), cells(r, 'Leader', N3)],
      tlc: tlc('majorityset_leader_election', consts({Node: nodes(3)}), 'Safety')}})),
  {id: 'consensus_epr', ic3syn: 'pyv-consensus-epr', file: 'consensus_epr.tla', source: 'Endive benchmarks/consensus_epr.tla (mypyvy\'s)', safety: 'v1 \\in decided[n1] /\\ v2 \\in decided[n2] => v1 = v2',
    make: consensusEpr, bug: 'send_vote without voted',
    laws: r => [r.law('one value decided', ({Decided}: any) => forall((a, b, v, u) => lt(a, b, v, u).and(Decided.at(pk(a, v)), Decided.at(pk(b, u))).implies(v.eq(u))))],
    bad: r => new Set(N3.flatMap(n => N2.filter(v => r.cell('Decided', n * N + v)))).size > 1,
    check: {inputs: {op: range(5), i: N3, j: N3, q: N3, v: N2, nondet: [0, 1]},
      project: r => [['VoteRequestMsg', 'VoteMsg', 'Votes'].map(m => cells(r, m, pairs(N3, N3))), cells(r, 'Voted', N3), cells(r, 'Leader', N3), cells(r, 'Decided', pairs(N3, N2))],
      tlc: tlc('consensus_epr', `${consts({Node: nodes(3), Value: nodes(2, 'v')})}  Quorum = {{n1, n2}, {n2, n3}, {n1, n3}, {n1, n2, n3}}\n`, 'Safety')}},
]
