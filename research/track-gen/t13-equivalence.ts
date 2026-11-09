// Semantic readout only: hand laws are comparison oracles, never prover inputs.
import {protocols} from '../protocols/ic3syn/models.ts'
import {mldrHandSet} from '../protocols/ic3syn/mldr2-probe.ts'
import {guardLaws, candidates} from '../../core/counts.ts'
import {smallOf} from '../../core/exists.ts'
import {type Law, type State, carriedView, compileC, seeded} from '../../core/machine.ts'
import {counted, clock, fullRate, withWall} from '../../kernel/prove.ts'
const p = protocols.find(p => p.id === 'mldr')!, r = p.make(), g = guardLaws(r.machine), m = {...r.machine, counts: {...r.machine.counts, ...g.counts}}
smallOf(m, r.machine)
const caller = [...r.kindLaws(), ...p.laws(r)]
const actual = withWall(performance.now() + 60000, () => counted(fullRate, () => candidates(r.machine, m, caller, caller, g.laws, 60000, clock() + 60000), true))
const hand = mldrHandSet(), both = {...m, counts: {...m.counts, ...hand.m.counts}}, rng = seeded(13013)
const expected = hand.laws.filter(l => /^Inv1758:|^Inv2973:|^Inv\*:/.test(l.name))
const keys = (l: Law) => [l.forall, ...(l.keys ?? [])].filter((k): k is string => !!k)
const plans = expected.map(law => ({law, test: compileC(law.holds, both), choices: actual.filter(a => keys(a).length === keys(law).length).map(a => ({law: a, test: compileC(a.holds, both), matches: true})), yes: 0, no: 0}))
for (let sample = 0; sample < 2000; sample++) {
  const st: State = {scalars: {started: rng(2)}, maps: Object.fromEntries(Object.keys(r.machine.maps!).map(map => [map, new Map<number, number>()]))}
  for (let a = 0; a < 3; a++) {
    for (const map of ['CT', 'CV', 'CfgT']) st.maps[map]!.set(a, rng(4))
    st.maps.St!.set(a, rng(2))
    for (let b = 0; b < 3; b++) st.maps.Config!.set(64 * a + b, rng(2))
  }
  const view = carriedView(both, st, {S: new Map(), Q2: new Map()}, undefined, {size: 3})
  for (const plan of plans) {
    const count = keys(plan.law).length
    for (let tuple = 0; tuple < 4 ** count; tuple++) {
      let code = tuple; const values = Array.from({length: count}, () => { const v = code % 4; code = Math.floor(code / 4); return v })
      const env = (law: Law) => ({size: 3, started: st.scalars.started!, ...Object.fromEntries(keys(law).map((k, i) => [k, values[i]!]))})
      const truth = plan.test(env(plan.law), view); if (truth) plan.yes++; else plan.no++
      for (const choice of plan.choices) if (choice.matches && choice.test(env(choice.law), view) !== truth) choice.matches = false
    }
  }
}
const matches = plans.map(p => ({expected: p.law.name, matches: p.choices.filter(c => c.matches).map(c => c.law.name), trueInstances: p.yes, falseInstances: p.no}))
console.log(JSON.stringify({seed: 13013, states: 2000, size: 3, binderValues: [0, 1, 2, 3], generated: actual.length + caller.length, matches}))
if (matches.some(p => !p.matches.length || !p.trueInstances || !p.falseInstances)) throw Error('T-13 semantic equivalence failed')
