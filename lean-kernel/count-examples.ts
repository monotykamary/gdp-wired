// Hand-built examples of the two kinds Count.lean and GhostMap.lean add, their certificates found by the untrusted search
// and checked by kernel.ts, and their Lean export (the suite's lean-count job: `bun count-examples.ts <dir>` writes
// CountExamples.lean, which Lean checks against the twin):
// - counts: a majority-quorum safety step (a toy consensus's Decide keeps agreement, the two majorities meeting), and
//   two thresholds (f + 1 of 2f + 1; n − t of n with n > 3t and at most t faulty, meeting outside the faulty);
// - a ghost map: grants that each name a valid ticket, ∀ k. granted[k] = 1 ⇒ ∃ t. t < T ∧ valid[t] = 1, the ticket a
//   Skolem function of k the step keeps (W[k] := t where Grant(k, t) fires).
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type C, type E, type Law, type Machine, all, any, atMost, get, ite, less, n, not, plus, same, times, x} from '../core/machine.ts'
import {type CountedGoal, type CountInst, type Ghosted, type Tree, checkCounted, checkGhostedLaws, countedGoal, ghostedMachine} from '../kernel/kernel.ts'
import {grow, proveLaws} from '../kernel/prove.ts'
import {countedToLean, smachineToLean} from './emit.ts'

const one = n(1), zero = n(0)
// A set's indicator at the key n: 1 where c holds.
const ind = (c: C): E => ite(c, one, zero)
const count = (v: string, body: E, below: E = x('N')) => ({v, key: 'n', below, body})

// --- counts --------------------------------------------------------------------------------------------------------------

// Toy consensus, its Decide(v) step, agreement at keys a and b: vote[n] = v + 1 is n's vote for v; a value is decided
// with a majority of the N nodes (2·|{n < N: vote[n] = v + 1}| > N), and stays decided. Before the step: every decided
// value has a majority (at a and at b) and agreement holds; the step's guard (v has a majority); after it, a and b
// decided and different. The votes don't change in this step, so each count reads the same cells before and after.
export function majorityStep(): {g: CountedGoal, insts: CountInst[]} {
  const decided = (k: E) => same(get('decided', k), one), after = (k: E) => same(ite(same(k, x('v')), one, get('decided', k)), one)
  const votes = (k: string) => ind(same(get('vote', x('n')), plus(x(k), one)))
  const g: CountedGoal = {name: 'a majority-quorum safety step: Decide(v) keeps agreement', hyps: [
    any(not(decided(x('a'))), less(x('N'), times(2, x('cA')))),
    any(not(decided(x('b'))), less(x('N'), times(2, x('cB')))),
    less(x('N'), times(2, x('cV'))),
    any(not(all(decided(x('a')), decided(x('b')))), same(x('a'), x('b'))),
    after(x('a')), after(x('b')), not(same(x('a'), x('b'))),
  ], counts: [count('cA', votes('a')), count('cB', votes('b')), count('cV', votes('v'))]}
  // Two majorities meet: cV + cB − N > 0 gives a node that voted for both v and b (so v = b), and likewise cA + cV.
  const insts: CountInst[] = [
    {wit: 'w1', below: x('N'), terms: [[1, 'cV'], [1, 'cB']], unit: -1},
    {wit: 'w2', below: x('N'), terms: [[1, 'cA'], [1, 'cV']], unit: -1},
  ]
  return {g, insts}
}

// f + 1 of 2f + 1: two sets of at least f + 1 of the 2f + 1 nodes, the votes for x and for y, meet, so x = y.
export function thresholdStep(): {g: CountedGoal, insts: CountInst[]} {
  const votes = (k: string) => ind(same(get('vote', x('n')), plus(x(k), one)))
  const g: CountedGoal = {name: 'f + 1 of 2f + 1: two such sets of votes meet', hyps: [
    same(x('N'), plus(times(2, x('f')), one)), atMost(plus(x('f'), one), x('cX')), atMost(plus(x('f'), one), x('cY')), not(same(x('x'), x('y'))),
  ], counts: [count('cX', votes('x')), count('cY', votes('y'))]}
  return {g, insts: [{wit: 'w', below: x('N'), terms: [[1, 'cX'], [1, 'cY']], unit: -1}]}
}

// More than two thirds with faults: n > 3t, at most t faulty, and two sets of at least n − t (a node is in the set for x
// when it is faulty, which may say anything, or it sent x); they meet at a node that isn't faulty, which sent one value.
export function byzantineStep(): {g: CountedGoal, insts: CountInst[]} {
  const faulty = same(get('faulty', x('n')), one), sent = (k: string) => same(get('sent', x('n')), plus(x(k), one))
  const g: CountedGoal = {name: 'n − t of n, n > 3t, at most t faulty: two such sets meet at a correct node', hyps: [
    less(times(3, x('t')), x('N')), atMost(x('cF'), x('t')), atMost(x('N'), plus(x('cX'), x('t'))), atMost(x('N'), plus(x('cY'), x('t'))), not(same(x('x'), x('y'))),
  ], counts: [count('cX', ind(any(faulty, sent('x')))), count('cY', ind(any(faulty, sent('y')))), count('cF', ind(faulty))]}
  return {g, insts: [{wit: 'w', below: x('N'), terms: [[1, 'cX'], [1, 'cY'], [-1, 'cF']], unit: -1}]}
}

export const countExamples = () => [{id: 'majority', ...majorityStep()}, {id: 'threshold', ...thresholdStep()}, {id: 'byzantine', ...byzantineStep()}]

// The untrusted search's tree for the goal with the instances' hypotheses.
export function countTree(g: CountedGoal, insts: CountInst[]): Tree | undefined {
  const goal = countedGoal(g, insts)
  if (!goal) return undefined
  const out = grow(goal)
  return 'tree' in out ? out.tree : undefined
}

// --- a ghost map ---------------------------------------------------------------------------------------------------------

// Grants with tickets: op 0 validates ticket t (t < T); op 1 grants k with a valid ticket t. The ghost map W keeps, for
// each granted k, the ticket it was granted with.
export function grants(): {g: Ghosted, laws: Law[], forallSome: {law: string, map: string, at: E, as: string}[]} {
  const fires = all(same(x('op'), one), same(get('valid', x('t')), one), less(x('t'), x('T')))
  const orig: Machine = {name: 'grants', params: ['T'], inputs: ['op', 'k', 't'], state: {}, maps: {valid: 0, granted: 0},
    step: {maps: {
      valid: {key: x('t'), value: ite(all(same(x('op'), zero), less(x('t'), x('T'))), one, get('valid', x('t')))},
      granted: {key: x('k'), value: ite(fires, one, get('granted', x('k')))},
    }}}
  const g: Ghosted = {orig, vars: {}, maps: {W: {start: 0, write: {key: x('k'), value: ite(fires, x('t'), get('W', x('k')))}}}}
  const laws: Law[] = [
    {name: 'a grant names a valid ticket', forall: 'j', holds: any(not(same(get('granted', x('j')), one)), all(less(get('W', x('j')), x('T')), same(get('valid', get('W', x('j'))), one)))},
    {name: 'granted is 0 or 1', forall: 'j', holds: atMost(get('granted', x('j')), one)},
  ]
  return {g, laws, forallSome: [{law: 'a grant names a valid ticket', map: 'W', at: x('j'), as: 'tk'}]}
}

// --- the Lean export -----------------------------------------------------------------------------------------------------

export function countExamplesLean(): string {
  const parts: string[] = []
  for (const {id, g, insts} of countExamples()) {
    const tree = countTree(g, insts)
    if (!tree || !checkCounted(g, {insts, tree})) throw new Error(`${id}: not proven`)
    // Tampered: a witness that is a count's variable (not fresh); the instances without their last; the unit 0.
    const tampered = [
      {what: 'the first witness is a count\'s variable', insts: insts.map((i, j) => (j === 0 ? {...i, wit: g.counts[0]!.v} : i))},
      ...(insts.length > 1 ? [{what: 'the last instance dropped', insts: insts.slice(0, -1)}] : []),
      {what: 'the first instance\'s unit coefficient 0', insts: insts.map((i, j) => (j === 0 ? {...i, unit: 0} : i))},
    ]
    for (const t of tampered) if (checkCounted(g, {insts: t.insts, tree})) throw new Error(`${id}: kernel.ts accepts the tampered certificate (${t.what})`)
    parts.push(countedToLean(id, g, {insts, tree}, tampered))
  }
  const {g, laws, forallSome} = grants(), m = ghostedMachine(g), r = proveLaws(m, laws)
  if (!r.proven || !r.proof || !checkGhostedLaws(g, laws, r.proof)) throw new Error('grants: not proven')
  // Tampered: the original's assumption reads the ghost map.
  const tOrig: Machine = {...g.orig, assume: same(get('W', x('k')), zero)}
  parts.push(smachineToLean('grants', m, laws, {ghosted: g, forallSome, free: forallSome.map(f => f.as), noFacts: true,
    after: (_ix, _mx, lit) => `-- TAMPERED: the original's assumption reads the ghost map. Lean computes smghostOk to false, as kernel.ts's ghostedOk.
example : smghostOk { grants_gm with orig := ${lit(tOrig)} } = false := by decide +kernel`}))
  return `import Count
import GhostMap
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Count.lean's and GhostMap.lean's kinds on hand-built examples: kernel.ts's certificates, checked by Lean. -/

${parts.join('\n\n')}

#print axioms majority
#print axioms threshold
#print axioms byzantine
#print axioms grants_orig_laws
#print axioms grants_skolem
#print axioms grants_some0
`
}

if (import.meta.main) {
  const dir = process.argv[2] ?? '.'
  writeFileSync(join(dir, 'CountExamples.lean'), countExamplesLean())
  console.log('wrote CountExamples.lean')
}
