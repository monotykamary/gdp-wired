import {expect, test} from 'bun:test'
import {bool, everyKey, forall, nat, oneOf, proveRule, proveSteps, record, rule, when} from './dsl.ts'
import {orderedPairSeed} from './ordered-pair-seeds.ts'
import {stepProofOutput} from './proof-output.ts'
import {stepSeedFamilies} from './step-seeds.ts'
import {checkStepLaws} from '../kernel/kernel.ts'

function allocation(broken = false) {
  const Row = record({occupied: bool, frozen: bool, data: nat})
  const r = rule('allocation and freezing').inputs({kind: oneOf('allocate', 'freeze'), ix: nat, payload: nat})
    .maps({row: Row.from({occupied: false, frozen: false, data: 0})})
    .flags(({kind, ix, row}) => ({allocate: kind.is('allocate').and(row.at(ix).occupied.not()),
      freeze: broken ? kind.is('freeze') : kind.is('freeze').and(row.at(ix).occupied)}))
    .step(({ix, payload, row, allocate, freeze}) => ({row: row.each(k => {
      const old = row.at(k), make = ix.eq(k).and(allocate), seal = ix.eq(k).and(freeze)
      return {occupied: make.or(old.occupied), frozen: seal.or(old.frozen), data: when(make, payload, old.data)}
    })}))
  const law = r.stepLaw('a frozen cell keeps its value', ({row}, after) => forall(k =>
    row.at(k).frozen.implies(after.row.at(k).data.eq(row.at(k).data))))
  return {r, law}
}

test('automatic same-key support checks the original step law from reachable states', () => {
  const {r, law} = allocation()
  expect(stepSeedFamilies(r.machine, law)[0]).toHaveLength(1)
  let replay = false, rejected = false
  stepProofOutput.on = ({machine, family, step, report}) => {
    const proof = report.proof!
    replay = checkStepLaws(machine, family, [step], proof)
    rejected = !checkStepLaws(machine, family, [step], {...proof, trees: {[`${step.name} @step law`]: {leaf: []}}})
  }
  try {
    const v = proveSteps(r, [], [law], {search: {ms: 10_000}})
    expect(v).toMatchObject({proven: true, checked: true, assumes: {states: 'reachable'}})
    expect(replay && rejected).toBe(true)
    const any = proveSteps(r, [], [law], {from: 'any', search: {ms: 10_000}})
    expect(any.proven).toBe(false)
  } finally { stepProofOutput.on = undefined }
}, 20_000)

test('a reachable allocation counterexample takes precedence over a support proposal', () => {
  const {r, law} = allocation(true)
  const v = proveSteps(r, [], [law], {search: {ms: 10_000}})
  expect(v.proven).toBe(false)
  expect(v.run?.trace).toHaveLength(2)
}, 15_000)

function catalog(hidden: boolean) {
  const Phase = oneOf('unused', 'queued', 'ready')
  const r = rule('append-only catalog').inputs({category: nat})
    .state({end: 0}).maps({Category: 0, Phase: Phase.from('unused'), Hidden: bool.from(false)})
    .assume(({Category, Phase, category, end}) => everyKey(k => k.lt(end).and(Category.at(k).eq(category), Phase.at(k).is('queued')).not()))
    .step(({Category, Phase, Hidden, end}) => ({end: end.plus(1), Category: Category.set(end, 0), Phase: Phase.set(end, 'ready'), Hidden: Hidden.set(end, hidden)}))
  const law = r.law('at most one visible ready entry per category', ({end, Category, Phase, Hidden}) => forall((a, b) =>
    a.lt(b).and(b.lt(end), Phase.at(a).is('ready'), Hidden.at(a).not(), Phase.at(b).is('ready'), Hidden.at(b).not()).implies(Category.at(a).eq(Category.at(b)).not())))
  return {r, law}
}

test('false ordered-pair proposals are discarded, not used to refute a true original', () => {
  const {r, law} = catalog(true)
  const m = r.machine, seed = orderedPairSeed(m, law)
  expect(seed).toBeDefined()
  expect(orderedPairSeed({...m, step: {...m.step, flags: {}}}, law)).toBeUndefined()
  expect(proveRule(r, [seed!, law], {search: false}).proven).toBe(false)
  const v = proveRule(r, [law], {search: {ms: 10_000}})
  expect(v).toMatchObject({proven: true, checked: true})
  expect(v.found?.laws?.some(l => l.text === seed?.name) ?? false).toBe(false)
}, 20_000)

test('a reachable duplicate takes precedence over an ordered-pair proposal', () => {
  const {r, law} = catalog(false)
  expect(orderedPairSeed(r.machine, law)).toBeDefined()
  const v = proveRule(r, [law], {search: {ms: 10_000}})
  expect(v.run?.trace).toHaveLength(2)
}, 15_000)
