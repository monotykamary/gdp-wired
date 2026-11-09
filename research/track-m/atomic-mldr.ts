// MongoLoglessDynamicRaft.tla at Endive 8b6f2ab: one native step per action.
// Init's nonempty configuration is a single carried set, copied to every server
// atomically. The dummy pre-Init state projects to no source state. Native tuple
// keys let the comprehension name both row and member without arithmetic phases.
import {type RelRef, type Term, all, everyKey, nat, oneOf, rule, when, yes} from '../../core/dsl.ts'
import {N, below, few} from '../protocols/ic3syn/common.ts'

export const mldr = (bug?: string) => rule('mongo logless dynamic raft')
  .params({size: nat}).pre(({size}) => size.atLeast(1).and(size.atMost(N)))
  .sorts('Server').relations({Config: ['Server', 'Server']})
  .inputs({op: oneOf('init', 'update_terms', 'become_leader', 'reconfig', 'send_config'), i: nat, j: nat, hx: nat, hy: nat})
  .carries('S', 'Q2').state({started: 0}).maps({CT: 0, St: few(1), CV: 1, CfgT: 0})
  .counts({
    inS: ({S, size}: any) => ({below: size, body: (_a: Term, k: Term) => S.has(k)}),
    inQ2: ({Q2, size}: any) => ({below: size, body: (_a: Term, k: Term) => Q2.has(k)}),
    inX: ({i, Config, size}: any) => ({below: size, body: (_a: Term, k: Term) => Config.has(i, k)}),
    xNotS: ({i, S, Config, size}: any) => ({below: size, body: (_a: Term, k: Term) => Config.has(i, k).and(S.has(k).not())}),
    sNotX: ({i, S, Config, size}: any) => ({below: size, body: (_a: Term, k: Term) => S.has(k).and(Config.has(i, k).not())}),
    xAndS: ({i, S, Config, size}: any) => ({below: size, body: (_a: Term, k: Term) => Config.has(i, k).and(S.has(k))}),
  })
  .assume(({op, i, j, hx, hy, size, S, Q2, Config, inS, inQ2, inX, xNotS, sNotX, xAndS}: any) => {
    const majorityOf = (Q: any, q: Term) => all(everyKey(k => Q.has(k).implies(Config.has(i, k))), bug ? yes : inX.at(0).lt(q.times(2)))
    const dx = xNotS.at(0), dy = sNotX.at(0), m = xAndS.at(0)
    return all(below(size, i, j), everyKey(k => S.at(k).atMost(1).and(Q2.at(k).atMost(1), S.has(k).implies(k.lt(size)), Q2.has(k).implies(k.lt(size)))),
      op.is('init').implies(S.has(j)),
      op.is('become_leader').implies(majorityOf(S, inS.at(0))),
      op.is('reconfig').implies(all(majorityOf(Q2, inQ2.at(0)),
        hx.times(2).atMost(dx.plus(m)), dx.plus(m).lt(hx.times(2).plus(2)), hy.times(2).atMost(dy.plus(m)), dy.plus(m).lt(hy.times(2).plus(2)))))
  })
  .flags(({i, S, Q2, CT, CV, CfgT}: any) => ({
    canVote: everyKey(v => S.has(v).implies(CT.at(v).lt(CT.at(i).plus(1)).and(CfgT.at(i).gt(CfgT.at(v)).or(CfgT.at(i).eq(CfgT.at(v)).and(CV.at(i).atLeast(CV.at(v))))))),
    committedQuorum: everyKey(t => Q2.has(t).implies(CV.at(i).eq(CV.at(t)).and(CfgT.at(i).eq(CfgT.at(t)), CT.at(t).eq(CT.at(i))))),
  }))
  .flags(({op, i, j, hx, hy, started, canVote, committedQuorum, S, Config, CT, St, CV, CfgT, xNotS, sNotX, xAndS}: any) => ({
    initializes: op.is('init').and(started.eq(0)),
    updates: op.is('update_terms').and(started.eq(1), CT.at(i).gt(CT.at(j))),
    leads: op.is('become_leader').and(started.eq(1), Config.has(i, i), S.has(i), canVote),
    reconfigs: op.is('reconfig').and(started.eq(1), St.at(i).eq(1), CfgT.at(i).eq(CT.at(i)), committedQuorum,
      hx.plus(1).minus(xNotS.at(0)).plus(hy.plus(1).minus(sNotX.at(0))).gt(xAndS.at(0)), S.has(i)),
    sends: op.is('send_config').and(started.eq(1), St.at(j).eq(0), CfgT.at(i).gt(CfgT.at(j)).or(CfgT.at(i).eq(CfgT.at(j)).and(CV.at(i).gt(CV.at(j))))),
  }))
  .step(({i, j, size, initializes, updates, leads, reconfigs, sends, started, S, Config, CT, St, CV, CfgT}: Record<string, any> & {Config: RelRef}) => ({
    started: when(initializes, 1, started),
    Config: Config.each((a: Term, b: Term) => when(initializes, a.lt(size).and(b.lt(size), S.has(b)),
      when(reconfigs.and(a.eq(i)), S.has(b), when(sends.and(a.eq(j)), Config.has(i, b), Config.has(a, b))))),
    CT: CT.each((s: Term) => when(initializes, 0, when(leads.and(S.has(s)), CT.at(i).plus(1), when(updates.and(s.eq(j)), CT.at(i), CT.at(s))))),
    St: St.each((s: Term) => when(initializes, 0, when(leads.and(s.eq(i)), 1, when(leads.and(S.has(s)).or(updates.and(s.eq(j))), 0, St.at(s))))),
    CV: CV.each((s: Term) => when(initializes, 1, when(reconfigs.and(s.eq(i)), CV.at(i).plus(1), when(sends.and(s.eq(j)), CV.at(i), CV.at(s))))),
    CfgT: CfgT.each((s: Term) => when(initializes, 0, when(leads.and(s.eq(i)), CT.at(i).plus(1), when(reconfigs.and(s.eq(i)), CT.at(i), when(sends.and(s.eq(j)), CfgT.at(i), CfgT.at(s)))))),
  }))
