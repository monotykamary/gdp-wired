// Research only: the shapes of Endive's IndAuto, never imported by production.
// MongoLoglessDynamicRaft_IndProofs.tla at 8b6f2ab. Count encodings use the
// ordinary checked counting lemmas; no invariant is assumed as a trusted fact.
import {MapRef, all, forall, type Term} from '../../core/dsl.ts'
import {mldr} from './atomic-mldr.ts'
import {N, pk} from '../protocols/ic3syn/common.ts'
export const published = () => {
  const r = mldr().counts({
    sizeRow: ({size, Config}: any) => ({below: size, body: (a: Term, k: Term) => Config.has(a, k)}),
    eligible: ({size, Config, CfgT, CV}: any) => ({below: size, body: (a: Term, k: Term) => {
      const ak = CfgT.at(a), kk = CfgT.at(k)
      const older = kk.lt(ak).or(kk.eq(ak).and(CV.at(k).atMost(CV.at(a))))
      return Config.has(a, k).and(older)
    }}),
    diff: ({size, Config}: any) => ({below: size, base: N, body: (a: Term, k: Term, b: Term) => Config.has(a, k).and(Config.has(b, k).not())}),
    meet: ({size, Config}: any) => ({below: size, base: N, body: (a: Term, k: Term, b: Term) => Config.has(a, k).and(Config.has(b, k))}),
    low: ({size, Config, CT, CfgT}: any) => ({below: size, base: N, body: (a: Term, k: Term, b: Term) => Config.has(a, k).and(CT.at(k).lt(CfgT.at(b)))}),
  })
  const sizeRow = new MapRef('sizeRow', 0), eligible = new MapRef('eligible', 0), diff = new MapRef('diff', 0), meet = new MapRef('meet', 0), low = new MapRef('low', 0)
  const laws = [
    ...r.kindLaws(),
    r.law('TypeOK: role range', ({size, St}: any) => forall(a => a.lt(size).implies(St.at(a).atMost(1)))),
    r.law('TypeOK: relation range', ({Config}: any) => forall((a, k) => Config.at(a, k).atMost(1))),
    r.law('TypeOK: relation domain', ({size, Config}: any) => forall((a, k) => Config.has(a, k).implies(a.lt(size).and(k.lt(size))))),
    r.law('one primary per term', ({size, St, CT}: any) => forall((a, b) => all(a.lt(size), b.lt(size), St.at(a).eq(1), St.at(b).eq(1), CT.at(a).eq(CT.at(b))).implies(a.eq(b)))),
    r.law('Inv1758: equal version tuples identify a configuration', ({size, Config, CfgT, CV}: any) => forall((a, b, k) => all(a.lt(size), b.lt(size), k.lt(size), CfgT.at(a).eq(CfgT.at(b)), CV.at(a).eq(CV.at(b))).implies(Config.at(a, k).eq(Config.at(b, k))))),
    r.law('Inv3915: primary has newest version at its configuration term', ({size, St, CfgT, CV}: any) => forall((a, b) => all(a.lt(size), b.lt(size), St.at(a).eq(1), CfgT.at(a).eq(CfgT.at(b))).implies(CV.at(b).atMost(CV.at(a))))),
    r.law('Inv866: primary current term equals configuration term', ({size, St, CT, CfgT}: any) => forall(a => all(a.lt(size), St.at(a).eq(1)).implies(CT.at(a).eq(CfgT.at(a))))),
    r.law('Inv2973: active configurations have overlapping quorums', ({size}: any) => forall((a, b, u, w) => {
      const intersection = meet.at(pk(a, b)), ad = diff.at(pk(a, b)), bd = diff.at(pk(b, a))
      const disabled = (z: Term) => eligible.at(z).times(2).atMost(sizeRow.at(z))
      return all(a.lt(size), b.lt(size)).implies(disabled(a).or(disabled(b), all(intersection.lt(ad.plus(u.times(2))), intersection.lt(bd.plus(w.times(2)))).implies(intersection.lt(u.plus(w)))))
    })),
    r.law('Inv3246: active quorum reaches every configuration term', ({size}: any) => forall((a, b) => all(a.lt(size), b.lt(size)).implies(eligible.at(b).times(2).atMost(sizeRow.at(b)).or(low.at(pk(b, a)).times(2).atMost(sizeRow.at(b)))))),
    r.law('TypeOK: positive configuration version', ({size, CV}: any) => forall(a => a.lt(size).implies(CV.at(a).atLeast(1)))),
    r.law('TypeOK: nonempty configuration after init', ({size, started}: any) => forall(a => a.lt(size).and(started.eq(1)).implies(sizeRow.at(a).atLeast(1)))),
  ]
  return {r, laws}
}
