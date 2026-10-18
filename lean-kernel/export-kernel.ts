// Real kernel trees as Lean data, each a theorem by Kern.sound with `decide +kernel`: the TypeScript kernel's verdicts,
// re-checked by a Lean twin whose soundness is proven. Usage: bun export-kernel.ts > Trees.lean
// The exporter is untrusted: it names columns, orders rows and claims cell equalities; Lean checks every claim.
import type {C, Law, Machine} from '../core/machine.ts'
import {all, any, atMost, bit, get, ite, less, max, min, minus, n, not, plus, prod, same, times, x} from '../core/machine.ts'
import {admit, admitFlagged, boundedLoss, capLaws, inflight, inflightLoss, loss, windowCeiling, windowLimit} from '../core/models.ts'
import {agree, product} from '../research/next/relational.ts'
import {type Fold, type Goal, type Loop, historyMachine, obligations} from '../kernel/kernel.ts'
import {grow, proveLaws} from '../kernel/prove.ts'
import {counterLaws, counterSteps, counters, escrowLaws, escrowSteps, escrowWatched, meterRefinement, poolLaws, poolTotal, pooled, twoPhaseRefinement} from '../examples/composition.ts'
import {type Exported, TRUE, encode, foldToLean, grown, hasSets, hmachineToLean, loopToLean, machineToLean, mmachineToLean, goalToLean, smachineToLean} from './emit.ts'
import {authority, authorityLaws, authorityPairs, authoritySteps} from '../examples/sets.ts'

const out: Exported[] = []
function machine(what: string, m: Machine, laws: Law[]) {
  const r = proveLaws(m, laws)
  if (!r.proven || !r.proof) throw new Error(`${what}: not proven`)
  for (const g of obligations(m, laws, r.proof.instances)) out.push({name: `${what}: ${g.name}`, goal: g, tree: r.proof.trees[g.name]!})
}
function goals(what: string, gs: Goal[]) {
  for (const g of gs) {
    const o = grow(g)
    if (!('tree' in o)) throw new Error(`${what}: ${g.name} stuck`)
    out.push({name: `${what}: ${g.name}`, goal: g, tree: o.tree})
  }
}

machine('budget rule', loss(), [boundedLoss])
const strong: Law = {name: 's + 50p <= b + 150', holds: atMost(plus(x('s'), times(50, x('p'))), plus(x('b'), n(150)))}
machine('in-flight', inflight, [inflightLoss, strong])
const perAccount: Machine = (() => {
  const base = {...admit(), step: {maps: {Acct: {key: x('acct'), value: ite(all(same(x('ok'), n(1)), less(get('Acct', x('acct')), n(1))), plus(get('Acct', x('acct')), n(1)), get('Acct', x('acct')))}}}}
  const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
  const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))))
  return product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
})()
// The examples (../examples): every proven law of a domain, or of all of them, through the Lean twin: machines by
// machine_sound, fmachine/fmmachine_sound (flags, maps) or hmachine_sound (histories), loops by loop_halts_of, decisions
// as goals by Kern.sound. Usage: bun export-kernel.ts --examples [domain] > Examples.lean
if (process.argv.includes('--examples')) {
  const which = process.argv[process.argv.indexOf('--examples') + 1]
  // A path to a module exporting `domain` (e.g. ../compare/domain.ts), or a domain of ../examples by name.
  const {domains} = which?.endsWith('.ts')
    ? {domains: [((await import(`${process.cwd()}/${which}`)) as {domain: {domain: string, cases: unknown[]}}).domain] as Awaited<typeof import('../examples/index.ts')>['domains']}
    : await import('../examples/index.ts')
  const parts: string[] = [], theorems: string[] = []
  let goal = 0, sets = false, live = false
  for (const d of domains.filter(dd => !which || which.startsWith('--') || which.endsWith('.ts') || dd.domain === which)) {
    d.cases.forEach((c, i) => {
      const id = `${d.domain}_${i}`.replace(/[^A-Za-z0-9_]/g, '_')
      if (c.kind === 'rule') {
        const m = c.rule.machine
        if (hasSets(m)) {
          sets = true
          parts.push(`-- ${d.domain}: ${c.name}\n${smachineToLean(id, m, c.laws, {stepLaws: c.steps})}`)
          theorems.push(`${id}_laws`, ...(c.steps ?? []).map((_, j) => `${id}_step${j}_holds`))
          return
        }
        if (m.history) sets = true
        // A rule with step laws alone has no laws for these twins to prove; its step laws go through the sets twin below.
        if (c.laws.length) {
          parts.push(`-- ${d.domain}: ${c.name}\n${m.history ? hmachineToLean(id, m, c.laws) : m.maps && Object.keys(m.maps).length ? mmachineToLean(id, m, c.laws) : machineToLean(id, m, c.laws)}`)
          theorems.push(`${id}_laws`, ...(m.history ? [`${id}_hlaws`] : []))
        }
        if (c.steps?.length) {
          // Step laws, one step or k, through the one twin (Sets.lean's skstep_sound), about the plain machine: a history's
          // sums as state, its queries as inputs (kernel.ts's historyMachine, whose relations its laws' proof above checks
          // per record).
          sets = true
          parts.push(`-- ${d.domain}: ${c.name}, step laws\n${smachineToLean(`${id}s`, m.history ? historyMachine(m).machine : m, c.laws, {stepLaws: c.steps})}`)
          c.steps.forEach((_, j) => theorems.push(`${id}s_step${j}_holds`))
        }
      } else if (c.kind === 'loop') {
        live = true
        parts.push(`-- ${d.domain}: ${c.name}\n${loopToLean(id, c.loop.loop, c.laws, c.loop.rankTerms)}`)
        theorems.push(`${id}_halts`)
      } else for (const dd of c.decisions) {
        parts.push(goalToLean({name: `${d.domain}: ${c.name}: ${dd.name}`, goal: dd.goal, tree: grown(dd.goal)}, goal, false))
        theorems.push(`t${goal++}`)
      }
    })
  }
  console.log(`import History
import ${live ? 'Live' : sets ? 'Sets' : 'Steps'}
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${which?.endsWith('.ts') ? which : `The examples (gdp-wired/examples${which && !which.startsWith('--') ? `/${which}.ts` : ''})`}: the kernel's trees for every proven law, checked by the Lean twin. -/

${parts.join('\n\n')}

${theorems.map(t => `#print axioms ${t}`).join('\n')}`)
  process.exit(0)
}

// Sets (examples/sets.ts): the derived authority's laws, step laws and two-step laws through Kern.smachine_sound and Kern.skstep_sound,
// and its proof offered for the variant that keeps the child on a refused derivation. Usage: bun export-kernel.ts --sets
if (process.argv.includes('--sets')) {
  const a = authority(), steps = [...authoritySteps(a), ...authorityPairs(a)]
  const text = smachineToLean('authority', a.machine, authorityLaws(a), {stepLaws: steps, tamper: {what: 'the authority proof offered for the variant that keeps the child on a refused derivation', machine: authority('keeps the child on refusal').machine}})
  console.log(`import Sets
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A derived authority over sets of names (examples/sets.ts): a request carries a candidate set, the child is accepted
only if the grants cover it, and holds exactly it; through Kern.smachine_sound and Kern.skstep_sound, with the kernel's
trees. -/

${text}

#print axioms authority_laws
${steps.map((_, j) => `#print axioms authority_step${j}_holds`).join('\n')}`)
  process.exit(0)
}

if (process.argv.includes('--history')) {
  const m = windowLimit()
  const laws = [windowCeiling]
  const yes: C = same(n(0), n(0))
  const text = hmachineToLean('window', m, laws, [
    {what: 'the relation claimed at every t (not only t <= now), offered the same proofs', relations: [{when: yes, holds: atMost(x('ours'), x('seen'))}], withRecordTrees: true},
    {what: 'the relation left out (no record goal), offered the same machine proof', relations: [], withRecordTrees: false},
  ], ix => `-- The window ceiling in plain Lean: in every reachable state, the admitted requests in the window (variable ${ix('ours')},
-- the sum over the history) are at most c (variable ${ix('c')}), for every history of forced and admitted requests.
theorem window_ceiling (ρ : Nat → Nat) (M : Nat → Nat → Nat) (hist : List (Nat → Nat)) (h : HReach window_hist ρ M hist) :
    ρ ${ix('ours')} ≤ ρ ${ix('c')} :=
  window.law0 ρ M hist h`)
  console.log(`import History
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! A sliding-window limit with a history (core/models.ts's windowLimit) through Kern.hmachine_sound: the window ceiling,
with the kernel's trees. -/

${text}

#print axioms window_hlaws
#print axioms window_ceiling`)
  process.exit(0)
}

const machines = [
  machineToLean('policy', loss(), [boundedLoss], `-- the budget rule's law in plain Lean: in every reachable state, s <= b + m (b, m, c, s are variables 0..3).
theorem bounded_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach policy_machine maps ρ) : ρ 3 ≤ ρ 0 + ρ 1 := by
  have := policy_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`),
  machineToLean('inflight', inflight, [inflightLoss, strong], `-- the in-flight law in plain Lean: s <= b + 150 (b, t, done, s, p are variables 0..4).
theorem inflight_loss (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach inflight_machine maps ρ) : ρ 3 ≤ ρ 0 + 150 := by
  have := inflight_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`),
]

// TAMPERED: the budget rule's proof offered for the machine with the max_tokens cap forgotten (s + c, not s + min(c, m)).
const uncapped = loss(false), uv = [...uncapped.params, ...uncapped.inputs, ...Object.keys(uncapped.state)]
const ue = encode({name: 'uncapped', goal: obligations(uncapped, [boundedLoss])[0]!, tree: {leaf: []}}, false, true, uv)
// Products: a machine whose law is s <= m × requests (grind's lemma), a fold with a cap given as a param, and a goal
// that needs the product of two rows.
const counted: Machine = {name: 'loss, counted', params: ['m'], inputs: ['c'], state: {s: n(0), r: n(0)}, step: {state: {s: plus(x('s'), min(x('c'), x('m'))), r: plus(x('r'), n(1))}}}
machines.push(machineToLean('counted', counted, [{name: 's <= m × requests', holds: atMost(x('s'), prod(x('m'), x('r')))}], `-- In plain Lean: after any requests, s <= m · r (m, c, s, r are variables 0..3).
theorem loss_per_request (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (h : Reach counted_machine maps ρ) : ρ 2 ≤ ρ 0 * ρ 3 := by
  have := counted_laws maps ρ h _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`))
goals('products', [{name: 'x <= x·x', hyps: [not(atMost(x('x'), prod(x('x'), x('x'))))]}])
machines.push(`-- TAMPERED: the budget rule's proof offered for the machine with the max_tokens cap forgotten. Lean computes the check to false.
def uncapped_machine : Machine := ⟨[${uv.indexOf('c')}], [(${uv.indexOf('s')}, ${ue.e(uncapped.state.s!)})], [(${uv.indexOf('s')}, ${ue.e(uncapped.step.state!.s!)})], ${TRUE}, ${TRUE}⟩
example : checkMachine uncapped_machine policy_proof = false := by decide +kernel`)

const positive: Law[] = [{name: 'a >= 1', holds: atMost(n(1), x('a'))}, {name: 'b >= 1', holds: atMost(n(1), x('b'))}]
const euclid: Loop = {
  name: 'gcd by subtraction', params: ['A', 'B'], inputs: [], state: {a: x('A'), b: x('B')}, while: not(same(x('a'), x('b'))),
  body: {a: ite(less(x('b'), x('a')), minus(x('a'), x('b')), x('a')), b: ite(less(x('a'), x('b')), minus(x('b'), x('a')), x('b'))},
  pre: all(atMost(n(1), x('A')), atMost(n(1), x('B'))),
}
const {pre: _drop, ...noPre} = euclid
machines.push(loopToLean('gcd', euclid, positive, plus(x('a'), x('b')), {what: 'the gcd proof without the precondition A, B >= 1', loop: noPre}))
const pages: Loop = {name: 'pagination', params: ['total'], inputs: ['page'], state: {cur: n(0)}, while: less(x('cur'), x('total')), body: {cur: plus(x('cur'), min(x('page'), minus(x('total'), x('cur'))))}, assume: atMost(n(1), x('page'))}
machines.push(loopToLean('pages', pages, [], minus(x('total'), x('cur')), {what: 'the pagination proof when a page may be empty', loop: {...pages, assume: atMost(n(0), x('page'))}}))
const retry: Loop = {name: 'retry', params: ['budget'], inputs: ['wait'], state: {spent: n(0), tries: n(0)}, while: less(x('spent'), x('budget')), body: {spent: plus(x('spent'), max(n(1), x('wait'))), tries: plus(x('tries'), n(1))}}
machines.push(loopToLean('retry', retry, [], minus(x('budget'), x('spent'))))
const grid: Loop = {
  name: 'every cell of an n × m grid', params: ['n', 'm'], inputs: [], state: {i: n(0), j: n(0)}, while: less(x('i'), x('n')),
  body: {i: ite(less(x('j'), x('m')), x('i'), plus(x('i'), n(1))), j: ite(less(x('j'), x('m')), plus(x('j'), n(1)), n(0))},
}
machines.push(loopToLean('grid', grid, [], [minus(x('n'), x('i')), minus(x('m'), x('j'))]))
// TAMPERED: a rank that reads the turn's input; the loop runs forever (w = x + 1 each turn). kernel.ts refuses such a
// rank, and a `while` that reads one; Lean's check of a liveness refuses both too and computes to false.
machines.push(`-- TAMPERED: while x < w, x := x + 1, with the rank w ∸ x (w the turn's input): the rank drops each turn, yet the loop
-- runs forever when every turn sends w = x + 1. Its halting, stated as a liveness, reads the input w in \`to\` and the rank;
-- Lean's check refuses it (kernel.ts refuses both).
def forever_loop : Loop := ⟨[0], [(1, .const 0)], [(1, .add (.var 1) (.const 1))], .lt (.var 1) (.var 0), ${TRUE}, ${TRUE}⟩
def forever_live : Live := ⟨${TRUE}, .not (.lt (.var 1) (.var 0)), [.sub (.var 0) (.var 1)], [(${TRUE}, [])], [(1, 2)], []⟩
example : sliveOk forever_loop.machine forever_live = false := by decide +kernel`)
const shape: Fold = {
  name: 'shape', params: [], inputs: [], leaf: {leaves: n(1), nodes: n(0), height: n(0)},
  node: {leaves: plus(x('l_leaves'), x('r_leaves')), nodes: plus(plus(x('l_nodes'), x('r_nodes')), n(1)), height: plus(max(x('l_height'), x('r_height')), n(1))},
}
machines.push(foldToLean('shape', shape, [{name: 'leaves = nodes + 1', holds: same(x('leaves'), plus(x('nodes'), n(1)))}, {name: 'height <= nodes', holds: atMost(x('height'), x('nodes'))}, {name: 'height < leaves', holds: less(x('height'), x('leaves'))}], `
-- In plain Lean: every binary tree has one more leaf than it has nodes (leaves, nodes, height are variables 0..2).
theorem leaves_eq_nodes_succ (maps : Nat → Nat → Nat) (ρ : Nat → Nat) (t : BTree) :
    foldT shape_fold ρ maps t 0 = foldT shape_fold ρ maps t 1 + 1 := by
  have := shape_laws maps ρ rfl t (allowed_trivial _ rfl ρ maps t) _ (List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩)
  simp only [evalC, evalE] at this
  exact of_decide_eq_true this`))
const rollup = (cap: number): Fold => ({name: 'spend roll-up', params: [], inputs: ['c'], leaf: {spend: min(x('c'), n(cap)), count: n(1)}, node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))}})
machines.push(foldToLean('rollup', rollup(50), [{name: 'spend <= 50 count', holds: atMost(x('spend'), times(50, x('count')))}], `
-- TAMPERED: the same proof offered for leaves capped at 51. Lean computes the check to false.
def rollup51_fold : Fold := { rollup_fold with leaf := [(1, .min (.var 0) (.const 51)), (2, .const 1)] }
example : checkFold rollup51_fold rollup_proof = false := by decide +kernel`))

machines.push(mmachineToLean('admit', admit(), capLaws, {
  corollary: `-- the caps rule's day cap in plain Lean: in every reachable state, every Day count is at most d (variable 0; Day is map 1).
theorem day_cap (ρ : Nat → Nat) (M : Nat → Nat → Nat) (h : FMReach admit_machine ρ M) (k : Nat) : M 1 k ≤ ρ 0 :=
  admit.law1 ρ M h k`,
  tamper: {what: 'the admit proof offered for the machine whose Day cap is unguarded', machine: admit(['Acct', 'Hour', 'Dom'])},
}))
// Flags: budget rule with its guard named (room := s < b), and its proof offered for a guard that always admits.
const flagged = (room: C): Machine => ({...loss(), name: 'loss, guard as a flag', step: {flags: {room}, state: {s: ite({op: 'flag', name: 'room'}, plus(x('s'), min(x('c'), x('m'))), x('s'))}}})
machines.push(machineToLean('fpolicy', flagged(less(x('s'), x('b'))), [boundedLoss], `-- TAMPERED: the proof offered for the machine whose flag always admits (room := 0 <= 0). Lean computes the check to false.
def fpolicy_tampered : FMachine := { fpolicy_machine with flags := [(4, .le (.const 0) (.const 0))] }
example : checkFMachine fpolicy_tampered fpolicy_proof = false := by decide +kernel`))
machines.push(mmachineToLean('fadmit', admitFlagged(), capLaws, {tamper: {what: 'the flagged admit proof offered for a grant flag without the Day cap', machine: (() => {
  const m = admitFlagged(), f = m.step.flags!.granted! as {op: 'and', xs: C[]}
  return {...m, step: {...m.step, flags: {granted: {op: 'and', xs: f.xs.filter(c2 => !JSON.stringify(c2).includes('"Day"'))}}}}
})()}}))
// Composition (examples/composition.ts): machines built by core/compose.ts are plain machines, checked here as any other.
// The refinement's laws (the relation) by induction, and the spec allowing every request it is sent as a step law; the
// interleaving's caps, and that one turn, or two, of one side leave the other.
const refines = meterRefinement()
machines.push(mmachineToLean('refines', refines.machine, refines.laws, {stepLaws: refines.stepLaws}))
machines.push(smachineToLean('interleaved', counters, counterLaws, {stepLaws: counterSteps}))
// Stuttering refinement, and laws about whole histories through ghosts (a release remembered; the holdings totalled).
const phased = twoPhaseRefinement()
machines.push(mmachineToLean('twophase', phased.machine, phased.laws, {stepLaws: phased.stepLaws}))
machines.push(mmachineToLean('escrow', escrowWatched(), escrowLaws, {stepLaws: escrowSteps}))
machines.push(mmachineToLean('pooltotal', pooled(), [...poolLaws, ...poolTotal]))
machines.push(`-- TAMPERED: the two-turn law's proof offered without its whens (b may move on its own turns). Lean computes the check to false.
example : checkSKStep interleaved_machine interleaved_proof { interleaved_step1 with k := { interleaved_step1.k with whens := [${TRUE}, ${TRUE}] } } = false := by decide +kernel`)
// Progress (run-progress.ts's cases), through the machine with maps and flags.
const keysP = {A: x('A'), D: x('D'), H: x('H'), M: x('M')}
const underP = all(less(get('Acct', keysP.A), n(1)), less(get('Day', keysP.D), x('d')), less(get('Hour', keysP.H), x('hr')), less(get('Dom', keysP.M), x('dm')))
const instP = Object.fromEntries(capLaws.map(l => [l.name, [keysP.A, keysP.D, keysP.H, keysP.M]]))
const reqP = {acct: keysP.A, day: keysP.D, hour: keysP.H, dom: keysP.M, ok: n(1)}
machines.push(mmachineToLean('pflight', inflight, [inflightLoss, strong], {progress: [
  {id: 'flight_complete', name: 'in-flight: a request in flight can always complete', when: atMost(n(1), x('p')), then: less(x("p'"), x('p')), request: {t: n(0), done: n(1)}, instances: {},
    tamper: {what: 'with none in flight, one completes (false)', when: same(x('p'), n(0))}},
  {id: 'flight_admit', name: 'in-flight: under budget with room, one is admitted', when: all(less(x('s'), x('b')), less(x('p'), n(3))), then: same(x("p'"), plus(x('p'), n(1))), request: {t: n(0), done: n(0)}, instances: {}},
]}))
machines.push(mmachineToLean('padmit', admit(), capLaws, {free: ['A', 'D', 'H', 'M'], progress: [
  {id: 'admit_grant', name: 'admit: an account under every cap gets its grant', when: underP, then: same(get("Acct'", keysP.A), n(1)), request: reqP, instances: instP,
    tamper: {what: 'even with the day full (false)', when: all(less(get('Acct', keysP.A), n(1)), less(get('Hour', keysP.H), x('hr')), less(get('Dom', keysP.M), x('dm')))}},
]}))
machines.push(mmachineToLean('pfadmit', admitFlagged(), capLaws, {free: ['A', 'D', 'H', 'M'], progress: [
  {id: 'fadmit_grant', name: 'admit, the grant as a flag: an account under every cap gets its grant', when: underP, then: same(get("Acct'", keysP.A), n(1)), request: reqP, instances: instP},
]}))
machines.push(mmachineToLean('peracct', perAccount, [{name: 'a.Acct[B] = b.Acct[B]', holds: same(get('a_Acct', x('Bacct')), get('b_Acct', x('Bacct')))}]))
if (process.argv.includes('--big')) {
  const iso = (() => {
    const base = admitFlagged()
    const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
    const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))), not(same(x('day'), x('Bday'))), not(same(x('hour'), x('Bhour'))), not(same(x('dom'), x('Bdom'))))
    return product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
  })()
  const atB = (kk: string, key: string): Law => ({name: `a.${kk}[B] = b.${kk}[B]`, holds: same(get(`a_${kk}`, x(key)), get(`b_${kk}`, x(key)))})
  machines.push(mmachineToLean('iso', iso, [atB('Acct', 'Bacct'), atB('Day', 'Bday'), atB('Hour', 'Bhour'), atB('Dom', 'Bdom')]))
  const a1 = admit()
  const caps = [['Dom', 'dom', x('dm')], ['Hour', 'hour', x('hr')], ['Day', 'day', x('d')], ['Acct', 'acct', n(1)]] as const
  const granted2 = all(...caps.map(([kk, f, cap]) => atMost(plus(get(kk, x(f)), n(1)), cap)), same(x('ok'), n(1)))
  const a2: Machine = {...a1, step: {maps: Object.fromEntries(caps.map(([kk, f]) => [kk, {key: x(f), value: ite(granted2, plus(get(kk, x(f)), n(1)), get(kk, x(f)))}]))}}
  machines.push(mmachineToLean('migration', product(admitFlagged(), a2), agree(a1)))
}

const rollupM: Fold = {name: 'spend roll-up, cap m a param', params: ['m'], inputs: ['c'], leaf: {spend: min(x('c'), x('m')), count: n(1)}, node: {spend: plus(x('l_spend'), x('r_spend')), count: plus(x('l_count'), x('r_count'))}}
machines.push(foldToLean('rollupM', rollupM, [{name: 'spend <= m count', holds: atMost(x('spend'), prod(x('m'), x('count')))}]))

const parts = [...machines, ...out.map((ex, i) => goalToLean(ex, i))]
parts.push(goalToLean(out[1]!, 1, true))
// The proof of s <= b + m offered for s <= b (false: the step admits up to m past b).
// The proof of x <= x·x offered for x·x <= x (false at x = 2).
const sq = out.findIndex(o => o.name === 'products: x <= x·x')
parts.push(goalToLean({name: 'the x <= x·x tree offered for x·x <= x', goal: {name: 'x·x <= x', hyps: [not(atMost(prod(x('x'), x('x')), x('x')))]}, tree: out[sq]!.tree}, 1002, true, false))
const wrong = obligations(loss(), [{name: 'wrong', holds: atMost(x('s'), x('b'))}])[1]!
parts.push(goalToLean({name: 'budget rule: the bounded_loss tree offered for s <= b', goal: wrong, tree: out[1]!.tree}, 1001, true, false))
console.log(`import Live
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ${out.length} goals from gdp-wired's kernel (kernel/prove.ts trees), each checked by Lean's kernel against Kern.checkGoal,
whose soundness (Kern.sound) is proven in Kernel.lean. Goals: ${[...new Set(out.map(o => o.name.split(':')[0]))].join('; ')}. -/

${parts.join('\n\n')}

#print axioms t0
#print axioms t${out.length - 1}
#print axioms bounded_loss
#print axioms inflight_loss
#print axioms gcd_halts
#print axioms grid_halts
#print axioms leaves_eq_nodes_succ
#print axioms rollup_laws
#print axioms day_cap
#print axioms loss_per_request
#print axioms rollupM_laws
#print axioms peracct_laws
#print axioms fpolicy_laws
#print axioms fadmit_laws
#print axioms flight_complete_holds
#print axioms flight_admit_holds
#print axioms admit_grant_holds
#print axioms fadmit_grant_holds
#print axioms refines_laws
#print axioms refines_step0_holds
#print axioms interleaved_laws
#print axioms interleaved_step0_holds
#print axioms interleaved_step1_holds
#print axioms twophase_laws
#print axioms twophase_step0_holds
#print axioms escrow_laws
#print axioms escrow_step0_holds
#print axioms pooltotal_laws${process.argv.includes('--big') ? '\n#print axioms iso_laws\n#print axioms migration_laws' : ''}`)
console.error(out.map((o, i) => `t${i}  ${o.name}`).join('\n'))
