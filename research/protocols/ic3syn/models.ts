// The IC3Syn suite (Cao et al., arXiv 2605.24619): its 29 protocols, each a TLA+ spec of Endive's benchmarks (pyv-paxos-epr
// mypyvy's paxos_epr.pyv, which the TLA+ cites; README.md says where each is from), written as a gdp-wired rule by hand in
// the encoding of ../models.ts (its README): a sort is the naturals below N = 64 (or 0 .. size − 1, a param, where the spec
// reads the whole sort), a relation a map of 0/1 cells at a·N + b, a function into a sort a map of naturals (v + 1, with
// 0 for Nil), an enumeration a map of few values; each action a request (`op` and its parameters), its guard a flag, a
// request whose flag is false a stutter. An `Init` that picks from a set (`owner \in [Node -> SUBSET Key]`, a start node,
// a match relation) is a setup phase of requests before `start`; states before it project to no TLA+ state.
// Quorums: a majority (`Cardinality(Q) * 2 > Cardinality(Node)`) is common.ts's `majority`, exact; a TLA+ `CONSTANT
// Quorum` is the majorities too, which every config's quorums are (README.md: a quorum sort can't be written here).
// Each port has its correspondence beside it (`file`, and what differs), a broken variant (`bug`), `bad` (the safety
// property broken, read on the check's instance) and `check` (the instance and its TLC cfg; check.ts, tlc.py).
import {type Term, all, any, everyKey, exists, forall, nat, no, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {N, type Protocol, type Read, below, few, lt, majority, majorityWitness, pk, pk3, range, rel, relTrue} from './common.ts'

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
  const q = range(size).filter(k => i.qm >> k & 1), rest = Object.fromEntries(Object.entries(i).filter(([k]) => k !== 'qm'))
  return [{...rest, ...majorityWitness(q)}]
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

// A rule over nodes 0 .. size − 1 whose request carries a majority Q for the actions in `acts`: Q within the nodes, its
// size the count `members` (TLA+'s Cardinality(Q) * 2 > Cardinality(Node), as it reads).
const overMajority = (r: any, inputs: Record<string, unknown>, acts: string[], ok: (env: any) => any): any =>
  r.params({size: nat}).pre(({size}: any) => size.atMost(N)).inputs(inputs).carries('Q')
    .counts({members: ({Q, size}: any) => ({below: size, body: (_x: Term, k: Term) => Q.has(k)})})
    .assume((env: any) => all(ok(env), any(...acts.map(a => env.op.is(a))).implies(majority(env.Q, env.members, env.size))))

// --- ex-quorum-leader-election: quorum_leader_election.tla. voted[i] is Voted[i] (j + 1; 0 is Nil). Node is 0 .. size − 1.
// BecomeLeader(i, Q) for a majority Q.
const quorumLeader = (bug?: Bug) => overMajority(rule('quorum leader election'), {op: oneOf('vote', 'become_leader'), i: nat, j: nat}, ['become_leader'], ({i, j, size}: any) => i.lt(size).and(j.lt(size)))
  .maps({IsLeader: rel, Voted: 0})
  .flags(({i, Q, Voted}: any) => ({allVoted: everyKey(k => Q.has(k).implies(Voted.at(k).eq(i.plus(1))))}))
  .flags(({op, i, allVoted, Voted}: any) => ({votes: op.is('vote').and(bug ? yes : Voted.at(i).eq(0)), leads: op.is('become_leader').and(allVoted)}))
  .step(({i, j, votes, leads, IsLeader, Voted}: any) => ({
    Voted: Voted.set(i, when(votes, j.plus(1), Voted.at(i))),
    IsLeader: IsLeader.set(i, when(leads, yes, IsLeader.at(i))),
  }))

// --- pyv-toy-consensus-forall: toy_consensus_forall.tla. vote[i] is Vote[i] (v + 1; 0 is Nil). Node is 0 .. size − 1.
const toyForall = (bug?: Bug) => overMajority(rule('toy consensus forall'), {op: oneOf('cast_vote', 'decide'), i: nat, v: nat}, ['decide'], ({i, v, size}: any) => i.lt(size).and(v.lt(N)))
  .maps({Vote: 0, Voted: rel, Decided: rel})
  .flags(({v, Q, Vote}: any) => ({allVote: everyKey(k => Q.has(k).implies(Vote.at(k).eq(v.plus(1))))}))
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
    puts: op.is('put').and(started.eq(1), bug && !noLost ? yes : Owner.at(pk(k, n))),
  }))
  .step(({n, k, v, n2, owns, starts, reshards, receives, puts, started, Table, Owner, TransferMsg, Owned}: any) => ({
    started: when(starts, 1, started),
    Table: Table.set(pk(n, k), when(reshards, 0, when(receives.or(puts), v.plus(1), Table.at(pk(n, k))))),
    Owner: Owner.set(pk(k, n), when(owns.or(receives), yes, when(reshards, no, Owner.at(pk(k, n))))),
    TransferMsg: TransferMsg.each((z: Term) => when(reshards.and(z.eq(pk3(n2, k, v))), bug && noLost ? TransferMsg.at(z) : yes, when(receives.and(z.eq(pk3(n, k, v))), no, TransferMsg.at(z)))),
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
// majorities of Node, 0 .. size − 1 (the configs' {{n1, n2}, {n2, n3}, {n1, n3}}; the TLA+ states no intersection, and a
// set of quorums that may not meet makes the property false); voting_quorum is a set, VotingQuorum, and Init's
// `voting_quorum \in Quorums` an `init` request carrying it. <<i, j>> \in votes is Votes[i·N + j], <<i, v>> \in decided
// Decided[i·N + v].
const consensusWo = (decide: boolean) => (bug?: Bug) => overMajority(rule(decide ? 'consensus forall' : 'consensus wo decide'),
  {op: decide ? oneOf('init', 'send_request_vote', 'send_vote', 'recv_vote', 'choose_voting_quorum', 'become_leader', 'decide')
    : oneOf('init', 'send_request_vote', 'send_vote', 'recv_vote', 'choose_voting_quorum', 'become_leader'), i: nat, j: nat, ...(decide ? {v: nat} : {})},
  ['init', 'choose_voting_quorum'], ({i, j, v, size}: any) => i.lt(size).and(j.lt(size), ...(decide ? [v.lt(N)] : [])))
  .state({started: 0})
  .maps({VoteRequestMsg: rel, Voted: rel, VoteMsg: rel, Votes: rel, Leader: rel, VotingQuorum: rel, ...(decide ? {Decided: rel} : {})})
  .flags(({i, Q, VotingQuorum, Votes, Decided}: any) => ({
    quorumVotes: everyKey(k => Q.has(k).implies(Votes.at(pk(i, k)))),
    votingQuorumVotes: everyKey(k => VotingQuorum.at(k).implies(Votes.at(pk(i, k)))),
    ...(decide ? {undecided: everyKey(x => x.lt(N).implies(Decided.at(pk(i, x)).not()))} : {}),
  }))
  .flags(({op, i, j, started, quorumVotes, votingQuorumVotes, undecided, Voted, VoteRequestMsg, VoteMsg, Leader}: any) => ({
    inits: op.is('init').and(started.eq(0)),
    requests: op.is('send_request_vote').and(started.eq(1)),
    // SendVote(src, dst) is (i, j)
    votes: op.is('send_vote').and(started.eq(1), bug ? yes : Voted.at(i).not(), VoteRequestMsg.at(pk(j, i))),
    // RecvVote(i, sender) is (i, j)
    receives: op.is('recv_vote').and(started.eq(1), VoteMsg.at(pk(j, i))),
    chooses: op.is('choose_voting_quorum').and(started.eq(1), quorumVotes),
    // (voting_quorum # {} holds of every majority)
    leads: op.is('become_leader').and(started.eq(1), votingQuorumVotes),
    ...(decide ? {decides: op.is('decide').and(started.eq(1), Leader.at(i), undecided)} : {}),
  }))
  .step(({i, j, v, inits, requests, votes, receives, chooses, leads, decides, started, Q, VoteRequestMsg, Voted, VoteMsg, Votes, Leader, VotingQuorum, Decided}: any) => ({
    started: when(inits, 1, started),
    VotingQuorum: VotingQuorum.each((k: Term) => when(inits.or(chooses), Q.has(k), VotingQuorum.at(k))),
    VoteRequestMsg: VoteRequestMsg.set(pk(i, j), when(requests, yes, VoteRequestMsg.at(pk(i, j)))),
    VoteMsg: VoteMsg.set(pk(i, j), when(votes, yes, VoteMsg.at(pk(i, j)))),
    Voted: Voted.set(i, when(votes, yes, Voted.at(i))),
    Votes: Votes.set(pk(i, j), when(receives, yes, Votes.at(pk(i, j)))),
    Leader: Leader.set(i, when(leads, yes, Leader.at(i))),
    ...(decide ? {Decided: Decided.set(pk(i, v), when(decides, yes, Decided.at(pk(i, v))))} : {}),
  }))

// --- ex-naive-consensus: naive_consensus.tla. Quorum is the majorities of Node, 0 .. size − 1 (the config's). <<n, v>> \in
// vote is Vote[v·N + n], and CastVote's `\A x: <<n, x>> \notin vote` is read through Voted[n] (every write keeps Voted[n] =
// ∃x vote(n, x): a node's votes are only added). decide ⊆ Quorum \X Value is read only as `<<Q, v>> \in decide` for some
// Q (LearnValue's), so the port keeps its projection Decide[v] = ∃Q: <<Q, v>> \in decide (check.ts compares it with
// TLC's VIEW of the same).
const naiveConsensus = (bug?: Bug) => overMajority(rule('naive consensus'), {op: oneOf('cast_vote', 'collect_votes', 'learn_value'), n: nat, v: nat},
  ['collect_votes'], ({n, v, size}: any) => n.lt(size).and(v.lt(N)))
  .maps({Vote: rel, Voted: rel, Decide: rel, Decision: rel})
  .flags(({v, Q, Vote}: any) => ({allVote: everyKey(k => Q.has(k).implies(Vote.at(pk(v, k))))}))
  .flags(({op, n, v, allVote, Voted, Decide}: any) => ({
    casts: op.is('cast_vote').and(bug ? yes : Voted.at(n).not()),
    collects: op.is('collect_votes').and(allVote),
    learns: op.is('learn_value').and(Decide.at(v)),
  }))
  .step(({n, v, casts, collects, learns, Vote, Voted, Decide, Decision}: any) => ({
    Vote: Vote.set(pk(v, n), when(casts, yes, Vote.at(pk(v, n)))),
    Voted: Voted.set(n, when(casts, yes, Voted.at(n))),
    Decide: Decide.set(v, when(collects, yes, Decide.at(v))),
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
  .flags(({i, T}: any) => (db ? {noneWithId: everyKey(m => m.lt(N).implies(T.at(pk(i, m)).not()))} : {}))
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

// --- ex-simple-election: simple_election.tla. Quorum is the majorities of Acceptor, 0 .. size − 1 (the config's, with
// the full set: a superset enables what its subsets do); <<a, p>> \in promise is Promise[p·N + a], and DidNotPromise(a)
// is read through Promised[a] (kept = ∃p promise(a, p), as naive consensus's Voted).
const simpleElection = (bug?: Bug) => overMajority(rule('simple election'), {op: oneOf('send_1a', 'send_1b', 'decide'), a: nat, p: nat},
  ['decide'], ({a, p, size}: any) => a.lt(size).and(p.lt(N)))
  .maps({Start: rel, Promise: rel, Promised: rel, Leader: rel})
  .flags(({p, Q, Promise}: any) => ({chosenAt: everyKey(k => Q.has(k).implies(Promise.at(pk(p, k))))}))
  .flags(({op, a, p, chosenAt, Start, Promised}: any) => ({
    sends1a: op.is('send_1a'),
    sends1b: op.is('send_1b').and(Start.at(p), bug ? yes : Promised.at(a).not()),
    decides: op.is('decide').and(chosenAt),
  }))
  .step(({a, p, sends1a, sends1b, decides, Start, Promise, Promised, Leader}: any) => ({
    Start: Start.set(p, when(sends1a, yes, Start.at(p))),
    Promise: Promise.set(pk(p, a), when(sends1b, yes, Promise.at(pk(p, a)))),
    Promised: Promised.set(a, when(sends1b, yes, Promised.at(a))),
    Leader: Leader.set(p, when(decides, yes, Leader.at(p))),
  }))

// --- pyv-toy-consensus-epr: toy_consensus_epr.tla. Quorum is the majorities of Node, 0 .. size − 1 (the config's);
// <<n, v>> \in vote is Vote[v·N + n].
const toyEpr = (bug?: Bug) => overMajority(rule('toy consensus epr'), {op: oneOf('cast_vote', 'decide'), n: nat, v: nat}, ['decide'], ({n, v, size}: any) => n.lt(size).and(v.lt(N)))
  .maps({Voted: rel, Vote: rel, Decided: rel})
  .flags(({v, Q, Vote}: any) => ({chosenAt: everyKey(k => Q.has(k).implies(Vote.at(pk(v, k))))}))
  .flags(({op, n, chosenAt, Voted}: any) => ({casts: op.is('cast_vote').and(bug ? yes : Voted.at(n).not()), decides: op.is('decide').and(chosenAt)}))
  .step(({n, v, casts, decides, Voted, Vote, Decided}: any) => ({
    Vote: Vote.set(pk(v, n), when(casts, yes, Vote.at(pk(v, n)))),
    Voted: Voted.set(n, when(casts, yes, Voted.at(n))),
    Decided: Decided.set(v, when(decides, yes, Decided.at(v))),
  }))

// --- ex-toy-consensus: toy_consensus.tla. vote[i] is Vote[i] (v + 1; 0 is Nil); Node is 0 .. size − 1; Decide(v, Q) for a
// majority Q.
const toyConsensus = (bug?: Bug) => overMajority(rule('toy consensus'), {op: oneOf('cast_vote', 'decide'), i: nat, v: nat}, ['decide'], ({i, v, size}: any) => i.lt(size).and(v.lt(N)))
  .maps({Vote: 0, Decision: rel})
  .flags(({v, Q, Vote}: any) => ({chosenAt: everyKey(k => Q.has(k).implies(Vote.at(k).eq(v.plus(1))))}))
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
// voters[n], so neither carries it; BecomeLeader's vs \in Majority is majority() of the row voters[n].
const majoritySet = (bug?: Bug) => rule('majorityset leader election')
  .params({size: nat}).pre(({size}) => size.atMost(N))
  .inputs({op: oneOf('voting', 'receive_vote', 'become_leader'), n: nat, m: nat})
  .maps({Vote: rel, Voters: rel, Leader: rel})
  .counts({voters: ({Voters, size}: any) => ({below: size, body: (x: Term, k: Term) => Voters.at(pk(x, k))})})
  .assume(({op, n, m, size, voters}: any) => n.lt(size).and(m.lt(size), op.is('become_leader').implies(size.lt(voters.at(n).times(2)))))
  .flags(({n, Vote}) => ({didNotVote: everyKey(x => x.lt(N).implies(Vote.at(pk(n, x)).not()))}))
  .flags(({op, n, m, didNotVote, Vote, Voters}) => ({
    // Voting(n1, n2) is (n, m); ReceiveVote(voter, n, vs) is (m, n)
    votes: op.is('voting').and(bug ? yes : didNotVote),
    receives: op.is('receive_vote').and(Vote.at(pk(m, n)), Voters.at(pk(n, m)).not()),
    leads: op.is('become_leader'),
  }))
  .step(({n, m, votes, receives, leads, Vote, Voters, Leader}) => ({
    Vote: Vote.set(pk(n, m), when(votes, yes, Vote.at(pk(n, m)))),
    Voters: Voters.set(pk(n, m), when(receives, yes, Voters.at(pk(n, m)))),
    Leader: Leader.set(n, when(leads, yes, Leader.at(n))),
  }))

// --- pyv-consensus-epr: consensus_epr.tla. Quorum is the majorities of Node, 0 .. size − 1 (the config's, with the full
// set); sender \in votes[n] is Votes[n·N + sender], v \in decided[n] Decided[n·N + v]; SendVote's `vote_request_msg' =
// ... \cup or \ {<<src, dst>>}` is `nondet`.
const consensusEpr = (bug?: Bug) => overMajority(rule('consensus epr'),
  {op: oneOf('send_request_vote', 'send_vote', 'recv_vote', 'become_leader', 'decide'), i: nat, j: nat, v: nat, nondet: nat},
  ['become_leader'], ({i, j, v, nondet, size}: any) => i.lt(size).and(j.lt(size), v.lt(N), nondet.atMost(1)))
  .maps({VoteRequestMsg: rel, Voted: rel, VoteMsg: rel, Votes: rel, Leader: rel, Decided: rel})
  .flags(({i, Q, Votes, Decided}: any) => ({
    quorumVotes: everyKey(k => Q.has(k).implies(Votes.at(pk(i, k)))),
    undecided: everyKey(x => x.lt(N).implies(Decided.at(pk(i, x)).not())),
  }))
  .flags(({op, i, j, quorumVotes, undecided, Voted, VoteRequestMsg, VoteMsg, Leader}: any) => ({
    requests: op.is('send_request_vote'),
    // SendVote(src, dst) and RecvVote(n, sender) are (i, j)
    votes: op.is('send_vote').and(bug ? yes : Voted.at(i).not(), VoteRequestMsg.at(pk(j, i))),
    receives: op.is('recv_vote').and(VoteMsg.at(pk(j, i))),
    leads: op.is('become_leader').and(quorumVotes),
    decides: op.is('decide').and(Leader.at(i), undecided),
  }))
  .step(({i, j, v, nondet, requests, votes, receives, leads, decides, VoteRequestMsg, Voted, VoteMsg, Votes, Leader, Decided}: any) => ({
    VoteRequestMsg: VoteRequestMsg.set(pk(i, j), when(requests.or(votes.and(nondet.eq(1))), yes, when(votes, no, VoteRequestMsg.at(pk(i, j))))),
    VoteMsg: VoteMsg.set(pk(i, j), when(votes, yes, VoteMsg.at(pk(i, j)))),
    Voted: Voted.set(i, when(votes, yes, Voted.at(i))),
    Votes: Votes.set(pk(i, j), when(receives, yes, Votes.at(pk(i, j)))),
    Leader: Leader.set(i, when(leads, yes, Leader.at(i))),
    Decided: Decided.set(pk(i, v), when(decides, yes, Decided.at(pk(i, v)))),
  }))

// --- the three that need a composed key (README.md: "Composed keys"). A guard or write that ranges over a coordinate
// of a relation other than its last reads its key scaled (k·N), which the kernel's key rules refuse (a runtime decides
// a quantifier on the breakpoints of plain key terms, k + e and k ∸ e); a write of every pair of two coordinates at
// once reads a coordinate of its key (k mod N). Where only the low coordinates range, they are one key (the block of a
// radix key: MAXR·N + V below r·N is every MAXR below r); where a higher coordinate ranges, the action is a phase:
// steps in a fixed order, one value of that coordinate a step, nothing else between them (`busy`), so the steps
// together are the TLA+ action, and a state inside a phase is no state of the spec (it projects to none).
export const pk4 = (a: Term, b: Term, c: Term, d: Term) => a.times(N * N * N).plus(pk3(b, c, d))
// <<t, x, y>> \in table (route_tc) is x = y or T[t·N² + x·N + y]: Init puts the diagonal in, and both switches only add
// to a row (route_tc \ row ∪ a superset of the row), so T holds the rest and its diagonal stays 0.
const tab = (T: any, t: Term, x: Term, y: Term) => x.eq(y).or(T.at(pk3(t, x, y)))
// The switches' table write, row pa := {<<pa, x, y>> : <<pa, x, y>> \in table \/ (<<pa, x, sw1>> \in table /\ <<pa, sw0, y>>
// \in table)}, as a phase: the action stores pa, sw0 and sw1 (busy, row 0), then `row` writes row x = row of pa (every
// key of it, y below size) and moves to the next, the last one ending the phase. Row sw0 is the same after its step
// (row sw0 ∪ row sw0), and row x's cell <<pa, x, sw1>> is read at row x's own step, before it is written, so each step
// reads the table as TLA+'s single step does.
const rowWrite = (T: any, k: Term, on: any, size: Term, {row, rpa, rsw0, rsw1}: any, back = false) => {
  const base = pk3(rpa, row, 0)
  const inRow = k.atLeast(base).and(k.lt(base.plus(size)), k.eq(base.plus(row)).not())
  const fromSw0 = k.eq(base.plus(rsw0)).or(when(row.atLeast(rsw0), T.at(k.minus(row.minus(rsw0).times(N))), T.at(k.plus(rsw0.minus(row).times(N)))))
  // (back: a broken variant's, <<pa, sw0, sw1>> learned too, the route both ways)
  return when(on.and(inRow, tab(T, rpa, row, rsw1).and(fromSw0).or(back ? row.eq(rsw0).and(k.eq(base.plus(rsw1))) : no)), yes, T.at(k))
}
// The phase's scalars after a step: `starts` begins it at (pa, sw0, sw1), `rows` moves it on and ends it after row
// size − 1 (back to 0 then, so a finished phase leaves nothing behind).
const phaseStep = (starts: any, rows: any, size: Term, pa: Term, sw0: Term, sw1: Term, {busy, row, rpa, rsw0, rsw1}: any) => {
  const last = rows.and(row.plus(1).eq(size))
  return {busy: when(starts, 1, when(last, 0, busy)), row: when(rows.and(last.not()), row.plus(1), when(last, 0, row)),
    rpa: when(starts, pa, when(last, 0, rpa)), rsw0: when(starts, sw0, when(last, 0, rsw0)), rsw1: when(starts, sw1, when(last, 0, rsw1))}
}
// The table's safety law (both switches' Safety): reflexive, transitive, antisymmetric, and the successors of x a chain.
const tableSafe = (T: any, size: Term, idle: any) => forall((t, x, y, z) => idle.and(below(size, t, x, y, z)).implies(all(
  tab(T, t, x, y).and(tab(T, t, y, z)).implies(tab(T, t, x, z)),
  tab(T, t, x, y).and(tab(T, t, y, x)).implies(x.eq(y)),
  tab(T, t, x, y).and(tab(T, t, x, z)).implies(tab(T, t, y, z).or(tab(T, t, z, y))))))
const tableBad = (r: Read, n: number) => {
  const t3 = (t: number, x: number, y: number) => x === y || r.cell('T', t * N * N + x * N + y) === 1, P = range(n)
  return P.some(t => P.some(x => P.some(y => P.some(z => (t3(t, x, y) && t3(t, y, z) && !t3(t, x, z)) || (x !== y && t3(t, x, y) && t3(t, y, x))
    || (t3(t, x, y) && t3(t, x, z) && !t3(t, y, z) && !t3(t, z, y))))))
}
const tableCells = (r: Read, n: number) => triples(range(n), range(n), range(n)).map(k => (Math.floor(k / N) % N === k % N ? 1 : r.cell('T', k)))

// --- pyv-learning-switch: learning_switch.tla. Node is 0 .. size − 1 (Forward reads \A w \in Node and every d \in Node);
// the table as above; <<ps, pd, s, d>> \in pending is P[ps·N³ + pd·N² + s·N + d]. Forward(ps, pd, sw0, sw1, nondet) keeps
// the pending tuples whose first is nondet (keys nondet·N³ .. nondet·N³ + N³ − 1) and adds <<ps, pd, sw1, d>> for every d;
// where it learns (ps # sw1, no <<ps, sw1, w>> for w # sw1) the table write is the phase above.
const learningSwitch = (bug?: Bug) => rule('learning switch')
  .params({size: nat}).pre(({size}) => size.atLeast(1).and(size.atMost(N)))
  .inputs({op: oneOf('new_packet', 'forward', 'row'), ps: nat, pd: nat, sw0: nat, sw1: nat, nondet: nat})
  .assume(({ps, pd, sw0, sw1, nondet, size}) => below(size, ps, pd, sw0, sw1, nondet))
  .state({busy: 0, row: 0, rpa: 0, rsw0: 0, rsw1: 0})
  .maps({T: rel, P: rel})
  .flags(({ps, sw1, size, T}) => ({noRoute: everyKey(w => w.lt(size).implies(w.eq(sw1).or(T.at(pk3(ps, sw1, w)).not())))}))
  .flags(({op, ps, pd, sw0, sw1, busy, noRoute, P}) => {
    const forwards = op.is('forward').and(busy.eq(0), P.at(pk4(ps, pd, sw0, sw1)))
    return {news: op.is('new_packet').and(busy.eq(0)), forwards, learns: forwards.and(ps.eq(sw1).not(), bug ? yes : noRoute), rows: op.is('row').and(busy.eq(1))}
  })
  .step(({ps, pd, sw0, sw1, nondet, size, news, forwards, learns, rows, T, P, ...s}: any) => ({
    ...phaseStep(learns, rows, size, ps, sw0, sw1, s),
    T: T.each(k => rowWrite(T, k, rows, size, s)),
    P: P.each(k => {
      const kept = k.atLeast(nondet.times(N * N * N)).and(k.lt(nondet.times(N * N * N).plus(N * N * N)), P.at(k)), b = pk4(ps, pd, sw1, 0)
      return when(news.and(k.eq(pk4(ps, pd, ps, ps))), yes, when(forwards, kept.or(k.atLeast(b).and(k.lt(b.plus(size)))), P.at(k)))
    }),
  }))

// --- i4-learning-switch: learning_switch_i4.tla. Node is 0 .. size − 1, Packet 0 .. packets − 1; src[p], dst[p] and
// link[x] are Src, Dst and Link (v + 1: Init picks them, `src`, `dst` and `link` requests before `start`, which checks
// they are total; `link` pairs two unlinked nodes both ways, so link has no self-loop and is symmetric); <<p, x, y>> \in pending is Pend[p·N² + x·N + y], <<x, y>> \in
// route_dom Dom[x·N + y], route_tc the table above. Flood's and Route's route_tc write (row src[p], where cond1) is the
// phase; Flood's pending write (row <<p, sw1>> of pending: y where link[sw1] = y and y # sw0) is one write at every key.
const learningSwitchI4 = (bug?: Bug) => rule('learning switch i4')
  .params({size: nat, packets: nat}).pre(({size, packets}) => size.atLeast(1).and(size.atMost(N), packets.atMost(N)))
  .inputs({op: oneOf('src', 'dst', 'link', 'start', 'new_packet', 'flood', 'route', 'row'), p: nat, sw0: nat, sw1: nat, sw2: nat})
  .assume(({p, sw0, sw1, sw2, size, packets}) => p.lt(packets).and(below(size, sw0, sw1, sw2)))
  .state({started: 0, busy: 0, row: 0, rpa: 0, rsw0: 0, rsw1: 0})
  .maps({Src: 0, Dst: 0, Link: 0, Pend: rel, Dom: rel, T: rel})
  .flags(({p, sw1, sw2, size, packets, Src, Dst, Link, T}) => {
    const d = Dst.at(p).minus(1)
    return {
      total: everyKey(q => q.lt(packets).implies(Src.at(q).atLeast(1).and(Dst.at(q).atLeast(1)))),
      linked: everyKey(x => x.lt(size).implies(Link.at(x).atLeast(1))),
      // \A z \in Node : (<<dst[p], sw1, z>> \in route_tc /\ sw1 # z) => <<dst[p], sw2, z>> \in route_tc
      below2: everyKey(z => z.lt(size).implies(z.eq(sw1).or(T.at(pk3(d, sw1, z)).not(), tab(T, d, sw2, z)))),
    }
  })
  .flags(({op, p, sw0, sw1, sw2, started, busy, total, linked, below2, Src, Dst, Pend, Dom, T}) => {
    const s = Src.at(p).minus(1), d = Dst.at(p).minus(1), live = started.eq(1).and(busy.eq(0))
    const floods = op.is('flood').and(live, Pend.at(pk3(p, sw0, sw1)), Dom.at(pk(d, sw1)).not())
    const routes = op.is('route').and(live, Pend.at(pk3(p, sw0, sw1)), Dom.at(pk(d, sw1)), tab(T, d, sw1, sw2), sw1.eq(sw2).not(), below2)
    return {
      setup: started.eq(0), starts: op.is('start').and(started.eq(0), total, linked), news: op.is('new_packet').and(live),
      floods, routes, learns: floods.or(routes).and(Dom.at(pk(s, sw1)).not(), s.eq(sw1).not()), cond2: d.eq(sw1).not(),
      rows: op.is('row').and(busy.eq(1)),
    }
  })
  .step(({op, p, sw0, sw1, sw2, size, setup, starts, news, floods, routes, learns, cond2, rows, started, Src, Dst, Link, Pend, Dom, T, ...s}: any) => {
    const src = Src.at(p).minus(1), pb = pk3(p, sw1, 0)
    return {
      started: when(starts, 1, started),
      ...phaseStep(learns, rows, size, src, sw0, sw1, s),
      Src: Src.set(p, when(setup.and(op.is('src')), sw0.plus(1), Src.at(p))),
      Dst: Dst.set(p, when(setup.and(op.is('dst')), sw0.plus(1), Dst.at(p))),
      // link[sw0] = sw1 and link[sw1] = sw0 at once, both unset before: a total link is then symmetric with no self-loop
      Link: Link.each(k => when(setup.and(op.is('link'), sw0.eq(sw1).not(), Link.at(sw0).eq(0), Link.at(sw1).eq(0)), when(k.eq(sw0), sw1.plus(1), when(k.eq(sw1), sw0.plus(1), Link.at(k))), Link.at(k))),
      Dom: Dom.set(pk(src, sw1), when(learns, yes, Dom.at(pk(src, sw1)))),
      T: T.each(k => rowWrite(T, k, rows, size, s, !!bug)),
      Pend: Pend.each(k => when(news.and(k.eq(pk3(p, src, src))), yes,
        when(floods.and(cond2, k.atLeast(pb), k.lt(pb.plus(size))), k.eq(pb.plus(Link.at(sw1).minus(1))).and(k.eq(pb.plus(sw0)).not()),
          when(routes.and(cond2, k.eq(pk3(p, sw1, sw2))), yes, Pend.at(k))))),
    }
  })

// --- pyv-paxos-epr: mypyvy's paxos_epr.pyv (README.md: Endive's paxos_epr.tla is faulty), transcribed to TLA+ for TLC
// below (paxosTla). Node is 0 .. size − 1, the quorums its majorities (the axiom's intersection by counting, as every
// port's Quorum); rounds and values the naturals below N, `none` a round (a param), le the order. one_a(r) OneA[r];
// one_b(n, r) OneB[r·N + n]; left_round(n, r) Left[n·N + r]; proposal(r, v) Proposal[r·N + v]; vote(n, r, v)
// Vote[n·N² + r·N + v]; decision(r, v) Decision[r·N + v]. decide's \A N. member(N, q) -> vote(N, r, v) reads n, the high
// coordinate: a count of the request (`missing`, the members without that vote, 0). propose's \A N, MAXR, V reads
// all three: the phase above over N (`check`, one node a step in order; Q kept as Qs), each node's \A MAXR, V one key j =
// MAXR·N + V of its block (MAXR < r iff j < r·N, MAXR <= maxr iff j < (maxr + 1)·N); a node that fails it ends the phase
// with no proposal (the spec's propose not taken), the last one passing ends it with the proposal. propose's
// \E N. member(N, q) /\ ... /\ vote(N, maxr, v) is the request's w.
const paxos = (bug?: Bug) => overMajority(rule('paxos epr').params({none: nat}).pre(({none}) => none.lt(N)),
  {op: oneOf('send_1a', 'join_round', 'propose', 'check', 'cast_vote', 'decide'), n: nat, r: nat, v: nat, maxr: nat, w: nat}, ['propose', 'decide'],
  ({n, r, v, maxr, w, size}: any) => all(n.lt(size), w.lt(size), lt(r, v, maxr)))
  .state({busy: 0, cnt: 0, pr: 0, pmaxr: 0, pv: 0})
  .maps({OneA: rel, OneB: rel, Left: rel, Proposal: rel, Vote: rel, Decision: rel, Qs: rel})
  .counts({missing: ({Q, r, v, Vote, size}: any) => ({below: size, body: (_x: Term, k: Term) => Q.has(k).and(Vote.at(pk3(k, r, v)).not())})})
  .flags(({r, Q, cnt, pr, pmaxr, none, Proposal, OneB, Vote}: any) => ({
    noProposal: everyKey(x => x.lt(N).implies(Proposal.at(pk(r, x)).not())),
    joined: everyKey(k => Q.has(k).implies(OneB.at(pk(r, k)))),
    rowOk: everyKey(j => Vote.at(cnt.times(N * N).plus(j)).and(j.lt(pr.times(N))).implies(pmaxr.eq(none).not().and(j.lt(pmaxr.plus(1).times(N))))),
  }))
  .flags(({op, n, r, v, maxr, w, none, busy, cnt, size, noProposal, joined, rowOk, missing, Q, Qs, OneA, Left, Proposal, Vote}: any) => {
    const idle = busy.eq(0).and(r.eq(none).not()), checks = op.is('check').and(busy.eq(1)), fails = checks.and(Qs.at(cnt), bug ? no : rowOk.not())
    return {
      sends: op.is('send_1a').and(idle),
      joins: op.is('join_round').and(idle, OneA.at(r), Left.at(pk(n, r)).not()),
      proposes: op.is('propose').and(idle, noProposal, joined, maxr.eq(none).or(Q.has(w).and(maxr.lt(r), Vote.at(pk3(w, maxr, v))))),
      checks, fails, commits: checks.and(fails.not(), cnt.plus(1).eq(size)),
      casts: op.is('cast_vote').and(idle, Left.at(pk(n, r)).not(), Proposal.at(pk(r, v))),
      decides: op.is('decide').and(idle, missing.at(0).eq(0)),
    }
  })
  .step(({n, r, v, maxr, sends, joins, proposes, checks, fails, commits, casts, decides, busy, cnt, pr, pmaxr, pv, Q, Qs, OneA, OneB, Left, Proposal, Vote, Decision}: any) => {
    const ends = fails.or(commits)
    return {
      busy: when(proposes, 1, when(ends, 0, busy)), cnt: when(checks.and(ends.not()), cnt.plus(1), when(ends, 0, cnt)),
      pr: when(proposes, r, when(ends, 0, pr)), pmaxr: when(proposes, maxr, when(ends, 0, pmaxr)), pv: when(proposes, v, when(ends, 0, pv)),
      Qs: Qs.each(k => when(proposes, Q.has(k), when(ends, no, Qs.at(k)))),
      OneA: OneA.set(r, when(sends, yes, OneA.at(r))),
      OneB: OneB.set(pk(r, n), when(joins, yes, OneB.at(pk(r, n)))),
      Left: Left.each(k => when(joins.and(k.atLeast(pk(n, 0)), k.lt(pk(n, r))), yes, Left.at(k))),
      Proposal: Proposal.set(pk(pr, pv), when(commits, yes, Proposal.at(pk(pr, pv)))),
      Vote: Vote.set(pk3(n, r, v), when(casts, yes, Vote.at(pk3(n, r, v)))),
      Decision: Decision.set(pk(r, v), when(decides, yes, Decision.at(pk(r, v)))),
    }
  })
// paxos_epr.pyv as TLA+ (by hand, for TLC; mypyvy MIT, 12a8f54): rounds 0 .. MaxRound with None one of them, the
// quorums the majorities of Node, le the order of the naturals.
const paxosTla = `---- MODULE PaxosEprPyv ----
EXTENDS Naturals, FiniteSets
CONSTANTS Node, Value, MaxRound, None
Round == 0..MaxRound
Quorum == {Q \\in SUBSET Node : Cardinality(Q) * 2 > Cardinality(Node)}
VARIABLES one_a, one_b, left_round, proposal, vote, decision
Init == one_a = {} /\\ one_b = {} /\\ left_round = {} /\\ proposal = {} /\\ vote = {} /\\ decision = {}
Send1a(r) == r # None /\\ one_a' = one_a \\cup {r} /\\ UNCHANGED <<one_b, left_round, proposal, vote, decision>>
JoinRound(n, r) ==
  /\\ r # None /\\ r \\in one_a /\\ <<n, r>> \\notin left_round
  /\\ one_b' = one_b \\cup {<<n, r>>}
  /\\ left_round' = left_round \\cup {<<n, R>> : R \\in {R2 \\in Round : R2 < r}}
  /\\ UNCHANGED <<one_a, proposal, vote, decision>>
Propose(r, q, maxr, v) ==
  /\\ r # None
  /\\ \\A x \\in Value : <<r, x>> \\notin proposal
  /\\ \\A m \\in q : <<m, r>> \\in one_b
  /\\ \\/ maxr = None /\\ \\A m \\in q, MAXR \\in Round, x \\in Value : ~(MAXR < r /\\ <<m, MAXR, x>> \\in vote)
     \\/ /\\ maxr # None /\\ \\E m \\in q : maxr < r /\\ <<m, maxr, v>> \\in vote
        /\\ \\A m \\in q, MAXR \\in Round, x \\in Value : (MAXR < r /\\ <<m, MAXR, x>> \\in vote) => MAXR <= maxr
  /\\ proposal' = proposal \\cup {<<r, v>>}
  /\\ UNCHANGED <<one_a, one_b, left_round, vote, decision>>
CastVote(n, v, r) ==
  /\\ r # None /\\ <<n, r>> \\notin left_round /\\ <<r, v>> \\in proposal
  /\\ vote' = vote \\cup {<<n, r, v>>} /\\ UNCHANGED <<one_a, one_b, left_round, proposal, decision>>
Decide(r, v, q) ==
  /\\ r # None /\\ \\A m \\in q : <<m, r, v>> \\in vote
  /\\ decision' = decision \\cup {<<r, v>>} /\\ UNCHANGED <<one_a, one_b, left_round, proposal, vote>>
Next == \\/ \\E r \\in Round : Send1a(r)
        \\/ \\E n \\in Node, r \\in Round : JoinRound(n, r)
        \\/ \\E r \\in Round, q \\in Quorum, maxr \\in Round, v \\in Value : Propose(r, q, maxr, v)
        \\/ \\E n \\in Node, v \\in Value, r \\in Round : CastVote(n, v, r)
        \\/ \\E r \\in Round, v \\in Value, q \\in Quorum : Decide(r, v, q)
Safety == \\A r1, r2 \\in Round, v1, v2 \\in Value : (<<r1, v1>> \\in decision /\\ <<r2, v2>> \\in decision) => v1 = v2
====
`

// --- mldr: MongoLoglessDynamicRaft.tla. Server is 0 .. size − 1 (Quorums(S) reads its sets whole); currentTerm is CT[s],
// state St[s] (Secondary 0, Primary 1), configVersion CV[s] (1 at first), configTerm CfgT[s], s2 \in config[s]
// Config[s·N + s2]; InitTerm is 0. Init's `\E initConfig # {}: config = [i |-> initConfig]`: `pick` stores a nonempty
// set (S, its member j) as C0, `copy` gives it to server i, `start` once every server has it. A request names its sets
// whole (S: BecomeLeader's voteQuorum, Reconfig's newConfig, pick's initConfig; Q2: ConfigIsCommitted's quorum; X:
// config[i], equal to it at every key), and the sizes the guards read are counts of the request (the servers below size
// in each set):
//   - Q \in Quorums(config[i]): Q ⊆ config[i] and |Q| > |config[i] \ Q| (Cardinality(Q) * 2 > Cardinality(config[i]));
//   - QuorumsOverlap(X, Y) (Y = S): with dx = |X \ Y|, dy = |Y \ X|, m = |X ∩ Y| and hx, hy (inputs) the halves of |X| =
//     dx + m and |Y| = dy + m rounded down, two disjoint majorities need hx + 1 − dx (at least 0) of X ∩ Y and hy + 1 − dy
//     of it, so the quorums overlap iff (hx + 1 ∸ dx) + (hy + 1 ∸ dy) > m.
const mldr = (bug?: Bug) => rule('mongo logless dynamic raft')
  .params({size: nat}).pre(({size}) => size.atLeast(1).and(size.atMost(N)))
  .inputs({op: oneOf('pick', 'copy', 'start', 'update_terms', 'become_leader', 'reconfig', 'send_config'), i: nat, j: nat, hx: nat, hy: nat})
  .carries('S', 'Q2', 'X')
  .state({started: 0, picked: 0})
  .maps({C0: rel, Copied: rel, Config: rel, CT: 0, St: few(1), CV: 1, CfgT: 0})
  .counts({
    inS: ({S, size}: any) => ({below: size, body: (_x: Term, k: Term) => S.has(k)}),
    inQ2: ({Q2, size}: any) => ({below: size, body: (_x: Term, k: Term) => Q2.has(k)}),
    xNotS: ({S, X, size}: any) => ({below: size, body: (_x: Term, k: Term) => X.has(k).and(S.has(k).not())}),
    xNotQ2: ({Q2, X, size}: any) => ({below: size, body: (_x: Term, k: Term) => X.has(k).and(Q2.has(k).not())}),
    sNotX: ({S, X, size}: any) => ({below: size, body: (_x: Term, k: Term) => S.has(k).and(X.has(k).not())}),
    xAndS: ({S, X, size}: any) => ({below: size, body: (_x: Term, k: Term) => X.has(k).and(S.has(k))}),
  })
  .assume(({op, i, j, hx, hy, size, S, Q2, X: Xs, Config, inS, inQ2, xNotS, xNotQ2, sNotX, xAndS}: any) => {
    const X = (k: Term) => Config.at(pk(i, k))
    const majorityOf = (Q: any, q: Term, xq: Term) => all(everyKey(k => Q.has(k).implies(X(k))), bug ? yes : xq.lt(q))
    const dx = xNotS.at(0), dy = sNotX.at(0), m = xAndS.at(0)
    return all(i.lt(size), j.lt(size), everyKey(k => S.at(k).atMost(1).and(Q2.at(k).atMost(1), S.has(k).implies(k.lt(size)), Q2.has(k).implies(k.lt(size)))),
      everyKey(k => Xs.at(k).atMost(1).and(Xs.has(k).implies(X(k)), X(k).implies(Xs.has(k)))),
      op.is('pick').implies(S.has(j)),
      op.is('become_leader').implies(majorityOf(S, inS.at(0), xNotS.at(0))),
      op.is('reconfig').implies(all(majorityOf(Q2, inQ2.at(0), xNotQ2.at(0)),
        hx.times(2).atMost(dx.plus(m)), dx.plus(m).lt(hx.times(2).plus(2)), hy.times(2).atMost(dy.plus(m)), dy.plus(m).lt(hy.times(2).plus(2)))))
  })
  .flags(({i, size, S, Q2, Copied, CT, CV, CfgT}) => {
    const newerOrEqual = (x: Term, y: Term) => CfgT.at(x).gt(CfgT.at(y)).or(CfgT.at(x).eq(CfgT.at(y)).and(CV.at(x).atLeast(CV.at(y))))
    return {
      allCopied: everyKey(k => k.lt(size).implies(Copied.at(k))),
      canVote: everyKey(v => S.has(v).implies(CT.at(v).lt(CT.at(i).plus(1)).and(newerOrEqual(i, v)))),
      committedQuorum: everyKey(t => Q2.has(t).implies(CV.at(i).eq(CV.at(t)).and(CfgT.at(i).eq(CfgT.at(t)), CT.at(t).eq(CT.at(i))))),
    }
  })
  .flags(({op, i, j, hx, hy, started, picked, allCopied, canVote, committedQuorum, S, Config, CT, St, CV, CfgT, xNotS, sNotX, xAndS}: any) => ({
    picks: op.is('pick').and(started.eq(0), picked.eq(0)),
    copies: op.is('copy').and(started.eq(0), picked.eq(1)),
    starts: op.is('start').and(started.eq(0), picked.eq(1), allCopied),
    // UpdateTerms(i, j), SendConfig(i, j)
    updates: op.is('update_terms').and(started.eq(1), CT.at(i).gt(CT.at(j))),
    leads: op.is('become_leader').and(started.eq(1), Config.at(pk(i, i)), S.has(i), canVote),
    reconfigs: op.is('reconfig').and(started.eq(1), St.at(i).eq(1), CfgT.at(i).eq(CT.at(i)), committedQuorum,
      hx.plus(1).minus(xNotS.at(0)).plus(hy.plus(1).minus(sNotX.at(0))).gt(xAndS.at(0)), S.has(i)),
    sends: op.is('send_config').and(started.eq(1), St.at(j).eq(0), CfgT.at(i).gt(CfgT.at(j)).or(CfgT.at(i).eq(CfgT.at(j)).and(CV.at(i).gt(CV.at(j))))),
  }))
  .step(({i, j, picks, copies, starts, updates, leads, reconfigs, sends, started, picked, S, C0, Copied, Config, CT, St, CV, CfgT}) => ({
    started: when(starts, 1, started),
    picked: when(picks, 1, picked),
    C0: C0.each(z => when(picks, S.has(z), C0.at(z))),
    Copied: Copied.set(i, when(copies, yes, Copied.at(i))),
    // config[i] := initConfig (copy) or newConfig (reconfig); config[j] := config[i] (send)
    Config: Config.each(z => {
      const inRow = (x: Term) => z.atLeast(x.times(N)).and(z.lt(x.times(N).plus(N)))
      return when(copies.and(inRow(i)), C0.at(z.minus(i.times(N))), when(reconfigs.and(inRow(i)), S.has(z.minus(i.times(N))),
        when(sends.and(inRow(j)), when(i.atLeast(j), Config.at(z.plus(i.minus(j).times(N))), Config.at(z.minus(j.minus(i).times(N)))), Config.at(z))))
    }),
    CT: CT.each(s => when(leads.and(S.has(s)), CT.at(i).plus(1), when(updates.and(s.eq(j)), CT.at(i), CT.at(s)))),
    St: St.each(s => when(leads.and(s.eq(i)), 1, when(leads.and(S.has(s)).or(updates.and(s.eq(j))), 0, St.at(s)))),
    CV: CV.each(s => when(reconfigs.and(s.eq(i)), CV.at(i).plus(1), when(sends.and(s.eq(j)), CV.at(i), CV.at(s)))),
    CfgT: CfgT.each(s => when(leads.and(s.eq(i)), CT.at(i).plus(1), when(reconfigs.and(s.eq(i)), CT.at(i), when(sends.and(s.eq(j)), CfgT.at(i), CfgT.at(s))))),
  }))

// mldr's requests at a state of the check: each op's own inputs (the others 0), the sets from bitmasks, the halves of
// |config[i]| and |S| computed from the state (the counts are the runtime's).
const bits = (x: number) => range(3).filter(k => x >> k & 1)
const setOf = (xs: number[]) => new Map(xs.map(v => [v, 1] as [number, number]))
const mldrRequests = (inp: any, r?: Read) => {
  const {op, i, j, sm, qm} = inp, uses: Record<number, string> = {0: 'jS', 1: 'i', 2: '', 3: 'ij', 4: 'iS', 5: 'iSQ', 6: 'ij'}, u = uses[op]!
  if ((!u.includes('i') && i) || (!u.includes('j') && j) || (!u.includes('S') && sm) || (!u.includes('Q') && qm)) return []
  const X = range(3).filter(k => r!.cell('Config', i * N + k)), S = bits(sm)
  const base = {op, i, j, hx: 0, hy: 0, S: setOf(S), Q2: setOf(bits(qm)), X: setOf(X)}
  return op === 5 ? [{...base, hx: Math.floor(X.length / 2), hy: Math.floor(S.length / 2)}] : [base]
}

// --- the protocols, with their safety laws, their instances and their TLC cfgs --------------------------------------
const one = (name: string, map: string) => (r: any) => [r.law(name, (env: any) => forall((a, b) => lt(a, b).and(env[map].at(a), env[map].at(b)).implies(a.eq(b))))]
const mutex = one('one holder', 'HoldsLock')
const N3 = range(3), N2 = range(2), N4 = range(4)

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
  ...[false].map((): Protocol => ({id: 'quorum_leader_election', ic3syn: 'ex-quorum-leader-election', file: 'quorum_leader_election.tla',
    source: 'Endive benchmarks/quorum_leader_election.tla', safety: 'isleader[i] /\\ isleader[j] => i = j',
    make: quorumLeader, bug: 'vote twice',
    laws: r => [r.law('one leader', ({size, IsLeader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), IsLeader.at(a), IsLeader.at(b)).implies(a.eq(b))))],
    bad: r => twoDistinct(r, 'IsLeader', N3),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, j: N3, qm: range(8)}, expand: withMajority(3),
      project: r => [cells(r, 'IsLeader', N3), cells(r, 'Voted', N3)], tlc: tlc('quorum_leader_election', consts({Node: nodes(3)}, {Nil: 'Nil'}), 'Inv')}})),
  ...[false].map((): Protocol => ({id: 'toy_consensus_forall', ic3syn: 'pyv-toy-consensus-forall', file: 'toy_consensus_forall.tla',
    source: 'Endive benchmarks/toy_consensus_forall.tla (mypyvy\'s)', safety: '\\A vi, vj \\in decided: vi = vj',
    make: toyForall, bug: 'cast_vote without voted', laws: one('one value decided', 'Decided'),
    bad: r => twoDistinct(r, 'Decided', N2),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, v: N2, qm: range(8)}, expand: withMajority(3),
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
      ? r => [r.law('one value decided', ({size, Decided}: any) => forall((a, b, v, u) => a.lt(size).and(b.lt(size), v.lt(N), u.lt(N), Decided.at(pk(a, v)), Decided.at(pk(b, u))).implies(v.eq(u))))]
      : r => [r.law('one leader', ({size, Leader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))],
    bad: decide ? r => new Set(N3.flatMap(n => N2.filter(v => r.cell('Decided', n * N + v)))).size > 1 : r => twoDistinct(r, 'Leader', N3),
    // (the configs' Quorums are the three 2-sets, not the full set, which the port's majorities also take: the check reads
    // those three alone, since voting_quorum stores the set and a stored full set would be a state the config has not)
    check: {params: {size: 3}, inputs: {op: decide ? range(7) : range(6), i: N3, j: N3, qm: [3, 5, 6], ...(decide ? {v: N2} : {})}, expand: withMajority(3),
      uses: [['qm'], ['i', 'j'], ['i', 'j'], ['i', 'j'], ['i', 'qm'], ['i'], ['i', 'v']],
      project: r => r.scalar('started') ? [['VoteRequestMsg', 'VoteMsg', 'Votes'].map(m => cells(r, m, pairs(N3, N3))), cells(r, 'Voted', N3), cells(r, 'Leader', N3), cells(r, 'VotingQuorum', N3), cells(r, 'Decided', pairs(N3, N2))] : undefined,
      tlc: tlc(decide ? 'consensus_forall' : 'consensus_wo_decide', `${consts({Node: nodes(3), ...(decide ? {Value: nodes(2, 'v')} : {})})}  ${decide ? 'Quorum' : 'Quorums'} = {{n1, n2}, {n2, n3}, {n1, n3}}\n`, 'Safety')}})),
  {id: 'naive_consensus', ic3syn: 'ex-naive-consensus', file: 'naive_consensus.tla', source: 'Endive benchmarks/naive_consensus.tla', safety: 'v1 \\in decision /\\ v2 \\in decision => v1 = v2',
    make: naiveConsensus, bug: 'cast_vote twice', laws: one('one value decided', 'Decision'), bad: r => twoDistinct(r, 'Decision', N2),
    check: {params: {size: 3}, inputs: {op: range(3), n: N3, v: N2, qm: range(8)}, expand: withMajority(3), uses: [['n', 'v'], ['v', 'qm'], ['v']],
      project: r => [cells(r, 'Vote', pairs(N2, N3)), cells(r, 'Decide', N2), cells(r, 'Decision', N2)],
      tlc: {...tlc('naive_consensus', `${consts({Node: nodes(3), Value: nodes(2, 'v')})}  Quorum = {{n1, n2}, {n2, n3}, {n1, n3}}\n`, 'Safety', 'VIEW DecideView\n'),
        // decide's projection to its values, as the port keeps it
        fix: [`sed -i 's/^====/DecideView == <<vote, {v \\\\in Value : \\\\E Q \\\\in Quorum : <<Q, v>> \\\\in decide}, decision>>\\n====/' naive_consensus.tla`]}}},
  ...[false, true].map((db): Protocol => {
    const Ns = N2, R = N2, P = N2, I = N2
    return {id: db ? 'client_server_db_ae' : 'client_server_ae', ic3syn: db ? 'pyv-client-server-db-ae' : 'pyv-client-server-ae', file: db ? 'client_server_db_ae.tla' : 'client_server_ae.tla',
      source: `Endive benchmarks/${db ? 'client_server_db_ae' : 'client_server_ae'}.tla (mypyvy's)`, safety: '<<n, p>> \\in response_received => \\E r: <<n, r>> \\in request_sent /\\ <<r, p>> \\in match',
      make: clientServer(db), bug: db ? 'db_process_request without match' : 'respond without match',
      laws: r => [r.law('a received response was matched', ({RequestSent, Match, ResponseReceived}: any) => forall((n, p) => lt(n, p).and(ResponseReceived.at(pk(n, p))).implies(
        exists(x => x.lt(N).and(RequestSent.at(pk(n, x)), Match.at(pk(x, p)))))))],
      bad: r => Ns.some(n => P.some(p => r.cell('ResponseReceived', n * N + p) && !R.some(x => r.cell('RequestSent', n * N + x) && r.cell('Match', x * N + p)))),
      check: {inputs: {op: db ? range(7) : range(5), n: Ns, r: R, p: P, ...(db ? {i: I} : {})},
        uses: db ? [['r', 'p'], [], ['n', 'r'], ['n', 'p'], ['n', 'r', 'i'], ['i', 'r', 'p'], ['n', 'i', 'p']] : [['r', 'p'], [], ['n', 'r'], ['n', 'r', 'p'], ['n', 'p']],
        project: r => r.scalar('started') ? [['Match', 'RequestSent', 'ResponseSent', 'ResponseReceived'].map(m => cells(r, m, pairs(N2, N2))),
          ...(db ? [['DbRequestSent', 'DbResponseSent', 'T'].map(m => cells(r, m, pairs(N2, N2)))] : [])] : undefined,
        tlc: tlc(db ? 'client_server_db_ae' : 'client_server_ae', consts({Node: nodes(2), Request: nodes(2, 'r'), Response: nodes(2, 'p'), ...(db ? {DbRequestId: nodes(2, 'i')} : {})}), 'Safety')}}
  }),
  {id: 'simple_election', ic3syn: 'ex-simple-election', file: 'simple_election.tla', source: 'Endive benchmarks/simple_election.tla', safety: 'pi \\in leader /\\ pj \\in leader => pi = pj',
    make: simpleElection, bug: 'send_1b after a promise', laws: one('one leader', 'Leader'), bad: r => twoDistinct(r, 'Leader', N2),
    check: {params: {size: 3}, inputs: {op: range(3), a: N3, p: N2, qm: range(8)}, expand: withMajority(3), uses: [['p'], ['a', 'p'], ['p', 'qm']], project: r => [cells(r, 'Start', N2), cells(r, 'Promise', pairs(N2, N3)), cells(r, 'Leader', N2)],
      tlc: tlc('simple_election', `${consts({Acceptor: nodes(3, 'a'), Proposer: nodes(2, 'p')})}  Quorum = {{a1, a2}, {a1, a3}, {a2, a3}, {a1, a2, a3}}\n`, 'Safety')}},
  {id: 'toy_consensus_epr', ic3syn: 'pyv-toy-consensus-epr', file: 'toy_consensus_epr.tla', source: 'Endive benchmarks/toy_consensus_epr.tla (mypyvy\'s)', safety: '\\A vi, vj \\in decided: vi = vj',
    make: toyEpr, bug: 'cast_vote twice', laws: one('one value decided', 'Decided'), bad: r => twoDistinct(r, 'Decided', N2),
    check: {params: {size: 3}, inputs: {op: range(2), n: N3, v: N2, qm: range(8)}, expand: withMajority(3), uses: [['n', 'v'], ['v', 'qm']], project: r => [cells(r, 'Voted', N3), cells(r, 'Vote', pairs(N2, N3)), cells(r, 'Decided', N2)],
      tlc: tlc('toy_consensus_epr', `${consts({Node: nodes(3), Value: nodes(2, 'v')}, {Nil: 'Nil'})}  Quorum = {{n1, n2}, {n1, n3}, {n2, n3}}\n`, 'Safety')}},
  ...[false].map((): Protocol => ({id: 'toy_consensus', ic3syn: 'ex-toy-consensus', file: 'toy_consensus.tla', source: 'Endive benchmarks/toy_consensus.tla',
    safety: '\\A vi, vj \\in decision: vi = vj', make: toyConsensus, bug: 'cast_vote twice', laws: one('one value decided', 'Decision'), bad: r => twoDistinct(r, 'Decision', N2),
    check: {params: {size: 3}, inputs: {op: range(2), i: N3, v: N2, qm: range(8)}, expand: withMajority(3),
      project: r => [cells(r, 'Vote', N3), cells(r, 'Decision', N2)], tlc: tlc('toy_consensus', consts({Node: nodes(3), Value: nodes(2, 'v')}, {Nil: 'Nil'}), 'Inv')}})),
  {id: 'firewall', ic3syn: 'pyv-firewall', file: 'firewall.tla', source: 'Endive benchmarks/firewall.tla (mypyvy\'s)', safety: 'd \\in sent[s] /\\ internal[d] => \\E i: internal[i] /\\ s \\in sent[i]',
    make: firewall, bug: 'send_to_internal without allowed_in',
    laws: r => [r.law('a sender to the inside was sent to from the inside', ({Internal, Sent}: any) => forall((s, d) => lt(s, d).and(Sent.at(pk(s, d)), Internal.at(d)).implies(
      exists(x => x.lt(N).and(Internal.at(x), Sent.at(pk(x, s)))))))],
    bad: r => N3.some(s => N3.some(d => r.cell('Sent', s * N + d) && r.cell('Internal', d) && !N3.some(i => r.cell('Internal', i) && r.cell('Sent', i * N + s)))),
    check: {inputs: {op: range(4), s: N3, d: N3}, project: r => r.scalar('started') ? [cells(r, 'Internal', N3), cells(r, 'Sent', pairs(N3, N3)), cells(r, 'AllowedIn', N3)] : undefined,
      tlc: tlc('firewall', consts({Node: nodes(3)}), 'Inv')}},
  ...[false].map((): Protocol => ({id: 'majorityset_leader_election', ic3syn: 'ex-majorityset-leader-election', file: 'majorityset_leader_election.tla',
    source: 'Endive benchmarks/majorityset_leader_election.tla', safety: 'x \\in leader /\\ y \\in leader => x = y', make: majoritySet, bug: 'vote twice',
    laws: r => [r.law('one leader', ({size, Leader}: any) => forall((a, b) => a.lt(size).and(b.lt(size), Leader.at(a), Leader.at(b)).implies(a.eq(b))))],
    bad: r => twoDistinct(r, 'Leader', N3),
    check: {params: {size: 3}, inputs: {op: range(3), n: N3, m: N3},
      project: r => [cells(r, 'Vote', pairs(N3, N3)), cells(r, 'Voters', pairs(N3, N3)), cells(r, 'Leader', N3)],
      tlc: tlc('majorityset_leader_election', consts({Node: nodes(3)}), 'Safety')}})),
  {id: 'consensus_epr', ic3syn: 'pyv-consensus-epr', file: 'consensus_epr.tla', source: 'Endive benchmarks/consensus_epr.tla (mypyvy\'s)', safety: 'v1 \\in decided[n1] /\\ v2 \\in decided[n2] => v1 = v2',
    make: consensusEpr, bug: 'send_vote without voted',
    laws: r => [r.law('one value decided', ({size, Decided}: any) => forall((a, b, v, u) => a.lt(size).and(b.lt(size), v.lt(N), u.lt(N), Decided.at(pk(a, v)), Decided.at(pk(b, u))).implies(v.eq(u))))],
    bad: r => new Set(N3.flatMap(n => N2.filter(v => r.cell('Decided', n * N + v)))).size > 1,
    check: {params: {size: 3}, inputs: {op: range(5), i: N3, j: N3, qm: range(8), v: N2, nondet: [0, 1]}, expand: withMajority(3),
      uses: [['i', 'j'], ['i', 'j', 'nondet'], ['i', 'j'], ['i', 'qm'], ['i', 'v']],
      project: r => [['VoteRequestMsg', 'VoteMsg', 'Votes'].map(m => cells(r, m, pairs(N3, N3))), cells(r, 'Voted', N3), cells(r, 'Leader', N3), cells(r, 'Decided', pairs(N3, N2))],
      tlc: tlc('consensus_epr', `${consts({Node: nodes(3), Value: nodes(2, 'v')})}  Quorum = {{n1, n2}, {n2, n3}, {n1, n3}, {n1, n2, n3}}\n`, 'Safety')}},
  {id: 'learning_switch', ic3syn: 'pyv-learning-switch', file: 'learning_switch.tla', source: 'Endive benchmarks/learning_switch.tla (mypyvy\'s)',
    safety: 'table(t, ·, ·) reflexive, transitive, antisymmetric, its successors a chain', make: learningSwitch, bug: 'forward learns without the no-route check',
    laws: r => [r.law('the table is a forest', ({size, busy, T}: any) => tableSafe(T, size, busy.eq(0)))],
    bad: r => r.scalar('busy') === 0 && tableBad(r, 3),
    check: {params: {size: 3}, inputs: {op: range(3), ps: N3, pd: N3, sw0: N3, sw1: N3, nondet: N3}, uses: [['ps', 'pd'], ['ps', 'pd', 'sw0', 'sw1', 'nondet'], []],
      keep: r => r.scalar('busy') === 1 || N3.flatMap(a => triples(N3, N3, N3).map(k => r.cell('P', a * N * N * N + k))).filter(Boolean).length < 5,
      project: r => r.scalar('busy') ? undefined : [tableCells(r, 3), N3.flatMap(a => triples(N3, N3, N3).map(k => r.cell('P', a * N * N * N + k)))],
      tlc: tlc('learning_switch', consts({Node: nodes(3)}), 'Safety', 'CONSTRAINT StateConstraint\n')}},
  {id: 'learning_switch_i4', ic3syn: 'i4-learning-switch', file: 'learning_switch_i4.tla', source: 'Endive benchmarks/learning_switch_i4.tla (I4\'s)',
    safety: 'route_tc(n, ·, ·) reflexive, transitive, antisymmetric, its successors a chain', make: learningSwitchI4, bug: 'a route learned both ways',
    laws: r => [r.law('the routes are a forest', ({size, started, busy, T}: any) => tableSafe(T, size, started.eq(1).and(busy.eq(0))))],
    bad: r => r.scalar('started') === 1 && r.scalar('busy') === 0 && tableBad(r, 4),
    check: {params: {size: 4, packets: 1}, inputs: {op: range(8), p: [0], sw0: N4, sw1: N4, sw2: N4},
      uses: [['p', 'sw0'], ['p', 'sw0'], ['sw0', 'sw1'], [], ['p'], ['p', 'sw0', 'sw1'], ['p', 'sw0', 'sw1', 'sw2'], []],
      project: r => r.scalar('started') && !r.scalar('busy') ? [cells(r, 'Src', [0]), cells(r, 'Dst', [0]), cells(r, 'Link', N4), cells(r, 'Dom', pairs(N4, N4)),
        cells(r, 'Pend', triples([0], N4, N4)), tableCells(r, 4)] : undefined,
      tlc: tlc('learning_switch_i4', consts({Node: nodes(4), Packet: ['p1']}), 'Safety')}},
  {id: 'paxos_epr', ic3syn: 'pyv-paxos-epr', file: 'paxos_epr.pyv', source: 'mypyvy examples/pd/paxos_epr.pyv (12a8f54; Endive benchmarks/paxos_epr.tla is faulty)',
    safety: 'decision(R1, V1) & decision(R2, V2) -> V1 = V2', make: paxos, bug: 'propose without the votes check',
    laws: r => [r.law('one value decided', ({Decision}: any) => forall((r1, v1, r2, v2) => lt(r1, v1, r2, v2).and(Decision.at(pk(r1, v1)), Decision.at(pk(r2, v2))).implies(v1.eq(v2))))],
    bad: r => new Set(N3.flatMap(x => N2.filter(v => r.cell('Decision', x * N + v)))).size > 1,
    check: {params: {size: 3, none: 0}, inputs: {op: range(6), n: N3, r: N3, v: N2, maxr: N3, w: N3, qm: range(8)}, expand: withMajority(3),
      uses: [['r'], ['n', 'r'], ['r', 'v', 'maxr', 'w', 'qm'], [], ['n', 'r', 'v'], ['r', 'v', 'qm']],
      project: r => r.scalar('busy') ? undefined : [cells(r, 'OneA', N3), cells(r, 'OneB', pairs(N3, N3)), cells(r, 'Left', pairs(N3, N3)), cells(r, 'Proposal', pairs(N3, N2)),
        cells(r, 'Vote', triples(N3, N3, N2)), cells(r, 'Decision', pairs(N3, N2))],
      tlc: {...tlc('PaxosEprPyv', `${consts({Node: nodes(3), Value: nodes(2, 'v')})}  MaxRound = 2\n  None = 0\n`, 'Safety'), fix: [`cat > PaxosEprPyv.tla <<'EOF'\n${paxosTla}EOF`]}}},
  {id: 'mldr', ic3syn: 'mldr', file: 'MongoLoglessDynamicRaft.tla', source: 'Endive benchmarks/MongoLoglessDynamicRaft.tla (MongoDB\'s logless dynamic Raft)',
    safety: 'state[s] = Primary /\\ state[t] = Primary /\\ currentTerm[s] = currentTerm[t] => s = t', make: mldr, bug: 'become_leader without a majority',
    laws: r => [r.law('one primary per term', ({size, St, CT}: any) => forall((a, b) => a.lt(size).and(b.lt(size), St.at(a).eq(1), St.at(b).eq(1), CT.at(a).eq(CT.at(b))).implies(a.eq(b))))],
    bad: r => N3.some(a => N3.some(b => a !== b && r.cell('St', a) === 1 && r.cell('St', b) === 1 && r.cell('CT', a) === r.cell('CT', b))),
    check: {params: {size: 3}, inputs: {op: range(7), i: N3, j: N3, sm: range(8), qm: range(8)}, byState: true, expand: mldrRequests,
      keep: r => N3.every(s => r.cell('CT', s) <= 2 && r.cell('CV', s) <= 2),
      project: r => r.scalar('started') ? [cells(r, 'CT', N3), cells(r, 'St', N3), cells(r, 'CV', N3), cells(r, 'CfgT', N3), cells(r, 'Config', pairs(N3, N3))] : undefined,
      tlc: tlc('MongoLoglessDynamicRaft', `${consts({Server: nodes(3)}, {Secondary: 'Secondary', Primary: 'Primary', Nil: 'Nil', InitTerm: '0', MaxTerm: '2', MaxLogLen: '0', MaxConfigVersion: '2'})}`, 'OnePrimaryPerTerm', 'CONSTRAINT StateConstraint\n')}},
]
