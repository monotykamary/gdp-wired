// MongoLoglessDynamicRaft.tla: P* (MLDR-DESIGN.md, §1.4).
// Pick row 0, copy it to each server, then start. CV=0 marks an uncopied
// row; copying sets CV=1. Equal (version, term) therefore identifies equal
// rows even during setup. Only started states project to the source spec.
import {type Term, all, everyKey, nat, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {N, few, pk, rel} from './common.ts'

export const mldr = (bug?: string) => rule('mongo logless dynamic raft')
  .params({size: nat}).pre(({size}) => size.atLeast(1).and(size.atMost(N)))
  .inputs({op: oneOf('pick', 'copy', 'start', 'update_terms', 'become_leader', 'reconfig', 'send_config'), i: nat, j: nat, hx: nat, hy: nat})
  .carries('S', 'Q2')
  .state({started: 0})
  .maps({Config: rel, CT: 0, St: few(1), CV: 0, CfgT: 0})
  .counts({
    inS: ({S, size}: any) => ({below: size, body: (_x: Term, k: Term) => S.has(k)}),
    inQ2: ({Q2, size}: any) => ({below: size, body: (_x: Term, k: Term) => Q2.has(k)}),
    inX: ({i, Config, size}: any) => ({below: size, body: (_x: Term, k: Term) => Config.at(pk(i, k))}),
    xNotS: ({i, S, Config, size}: any) => ({below: size, body: (_x: Term, k: Term) => Config.at(pk(i, k)).and(S.has(k).not())}),
    sNotX: ({i, S, Config, size}: any) => ({below: size, body: (_x: Term, k: Term) => S.has(k).and(Config.at(pk(i, k)).not())}),
    xAndS: ({i, S, Config, size}: any) => ({below: size, body: (_x: Term, k: Term) => Config.at(pk(i, k)).and(S.has(k))}),
  })
  .assume(({op, i, j, hx, hy, size, S, Q2, Config, inS, inQ2, inX, xNotS, sNotX, xAndS}: any) => {
    const X = (k: Term) => Config.at(pk(i, k))
    const majorityOf = (Q: any, q: Term) => all(everyKey(k => Q.has(k).implies(X(k))), bug ? yes : inX.at(0).lt(q.times(2)))
    const dx = xNotS.at(0), dy = sNotX.at(0), m = xAndS.at(0)
    return all(i.lt(size), j.lt(size), everyKey(k => S.at(k).atMost(1).and(Q2.at(k).atMost(1), S.has(k).implies(k.lt(size)), Q2.has(k).implies(k.lt(size)))),
      op.is('pick').implies(S.has(j)),
      op.is('become_leader').implies(majorityOf(S, inS.at(0))),
      op.is('reconfig').implies(all(majorityOf(Q2, inQ2.at(0)),
        hx.times(2).atMost(dx.plus(m)), dx.plus(m).lt(hx.times(2).plus(2)), hy.times(2).atMost(dy.plus(m)), dy.plus(m).lt(hy.times(2).plus(2)))))
  })
  .flags(({i, size, S, Q2, CT, CV, CfgT}) => {
    const newerOrEqual = (x: Term, y: Term) => CfgT.at(x).gt(CfgT.at(y)).or(CfgT.at(x).eq(CfgT.at(y)).and(CV.at(x).atLeast(CV.at(y))))
    return {
      noneCopied: everyKey(k => k.lt(size).implies(CV.at(k).eq(0))),
      allCopied: everyKey(k => k.lt(size).implies(CV.at(k).eq(1))),
      canVote: everyKey(v => S.has(v).implies(CT.at(v).lt(CT.at(i).plus(1)).and(newerOrEqual(i, v)))),
      committedQuorum: everyKey(t => Q2.has(t).implies(CV.at(i).eq(CV.at(t)).and(CfgT.at(i).eq(CfgT.at(t)), CT.at(t).eq(CT.at(i))))),
    }
  })
  .flags(({op, i, j, hx, hy, started, noneCopied, allCopied, canVote, committedQuorum, S, Config, CT, St, CV, CfgT, xNotS, sNotX, xAndS}: any) => ({
    picks: op.is('pick').and(started.eq(0), noneCopied),
    copies: op.is('copy').and(started.eq(0), CV.at(0).eq(1), CV.at(i).eq(0)),
    starts: op.is('start').and(started.eq(0), allCopied),
    updates: op.is('update_terms').and(started.eq(1), CT.at(i).gt(CT.at(j))),
    leads: op.is('become_leader').and(started.eq(1), Config.at(pk(i, i)), S.has(i), canVote),
    reconfigs: op.is('reconfig').and(started.eq(1), St.at(i).eq(1), CfgT.at(i).eq(CT.at(i)), committedQuorum,
      hx.plus(1).minus(xNotS.at(0)).plus(hy.plus(1).minus(sNotX.at(0))).gt(xAndS.at(0)), S.has(i)),
    sends: op.is('send_config').and(started.eq(1), St.at(j).eq(0), CfgT.at(i).gt(CfgT.at(j)).or(CfgT.at(i).eq(CfgT.at(j)).and(CV.at(i).gt(CV.at(j))))),
  }))
  .step(({i, j, picks, copies, starts, updates, leads, reconfigs, sends, started, S, Config, CT, St, CV, CfgT}) => ({
    started: when(starts, 1, started),
    // config[0] := initConfig (pick), config[i] := config[0] (copy) or newConfig (reconfig); config[j] := config[i] (send)
    Config: Config.each(z => {
      const inRow = (x: Term) => z.atLeast(x.times(N)).and(z.lt(x.times(N).plus(N)))
      return when(picks.and(z.lt(N)), S.has(z), when(copies.and(inRow(i)), Config.at(z.minus(i.times(N))), when(reconfigs.and(inRow(i)), S.has(z.minus(i.times(N))),
        when(sends.and(inRow(j)), when(i.atLeast(j), Config.at(z.plus(i.minus(j).times(N))), Config.at(z.minus(j.minus(i).times(N)))), Config.at(z)))))
    }),
    CT: CT.each(s => when(leads.and(S.has(s)), CT.at(i).plus(1), when(updates.and(s.eq(j)), CT.at(i), CT.at(s)))),
    St: St.each(s => when(leads.and(s.eq(i)), 1, when(leads.and(S.has(s)).or(updates.and(s.eq(j))), 0, St.at(s)))),
    CV: CV.each(s => when(picks.and(s.eq(0)).or(copies.and(s.eq(i))), 1, when(reconfigs.and(s.eq(i)), CV.at(i).plus(1), when(sends.and(s.eq(j)), CV.at(i), CV.at(s))))),
    CfgT: CfgT.each(s => when(leads.and(s.eq(i)), CT.at(i).plus(1), when(reconfigs.and(s.eq(i)), CT.at(i), when(sends.and(s.eq(j)), CfgT.at(i), CfgT.at(s))))),
  }))
