// The CHC-COMP items: tasks of CHC-COMP 2026's LIA-Lin track (chc-comp/chc-comp26-benchmarks at b4fa7a7, the .smt2
// files in tasks/chc/ byte for byte as the benchmark has them) that gdp-wired 0.21.0 doesn't solve and Spacer, Golem or
// Eldarica does, each one of groups_chc.py's groups. Each is read by compare/chc's own translation (translate.ts's
// `build`: the rule whose law, error is never reached, is the system's satisfiability), so the statement is the task's.
//   - a sat task: `today` is the prover alone on the law, `frontier` the library's invariant search (inferLaws) with the
//     benchmark's 60 s as its counted budget
//   - an unsat task (groups H and I): the claim is that the error is reached. It counts as proven only where the
//     library's verdict on the law carries a run (its refutation by runs) that the CHC itself confirms, step by step
//     (translate.ts's checkDerivation, which uses no gdp-wired code); `today` is the prover alone, `frontier` with its
//     search
// A broken variant is the task changed so that its claim is false: for a sat task an error that is reached, for an
// unsat one an error that isn't. Where the benchmark has the task with one mutation more or less (the Lustre tasks'
// `_e<k>_<n>` mutants), that is the variant; otherwise a change written here (`.broken.smt2`, the change beside it).
// Every task and variant's answer is Spacer's and Golem's on boat (truth-chc.json, runs/corpus2/truth-chc).
import {readFileSync} from 'node:fs'
import {type Chc, parseChc} from '../../compare/chc/chc.ts'
import {type Built, type Step, build, checkDerivation} from '../../compare/chc/translate.ts'
import {type Verdict, proveRule} from '../../core/dsl.ts'
import {inferLaws} from '../../core/infer.ts'
import type {Item, Source, Track} from './corpus.ts'

const DIR = `${import.meta.dir}/tasks/chc`
// The search's counted budget: the benchmark gave each task 60 s of wall time in all.
const FRONTIER_MS = 60_000
const load = (file: string): {chc: Chc, b: Built} => { const chc = parseChc(readFileSync(`${DIR}/${file}`, 'utf8')); return {chc, b: build(chc, file.replace(/\.smt2$/, ''))} }

// A refutation, confirmed: the verdict's run replayed on the compiled rule and checked against the CHC.
function confirmed(chc: Chc, b: Built, v: Verdict): Verdict {
  if (!v.run) return {proven: false, checked: false, ...(v.goal ? {goal: v.goal, stuck: v.stuck} : {}), why: `no run reaches the error${v.why ? ` (${v.why})` : ''}`}
  const r = b.rule, g = r.compiled(), steps: Step[] = []
  let st = g.init({})
  try {
    for (const t of v.run.trace) {
      const raw: Record<string, number | boolean | string> = {c: b.clauseNames[t.c as number]!}
      for (let k = 0; k < b.inInt; k++) raw[`x${k}`] = (t[`x${k}`] as number) - (t[`x${k}$neg`] as number)
      for (let k = 0; k < b.inBool; k++) raw[`y${k}`] = t[`y${k}`] === 1
      const before = r.decode(st), next = g.step({}, st, r.encodeInput(raw as never))
      steps.push({clause: Number(String(raw.c).slice(1)), input: raw, before, after: r.decode(next)})
      st = next
    }
  } catch (e) { return {proven: false, checked: false, why: `the run doesn't replay: ${(e as Error).message.slice(0, 120)}`} }
  const bad = checkDerivation(b, chc, steps)
  return bad ? {proven: false, checked: false, why: `the CHC refuses the run: ${bad}`} : {proven: true, checked: true, why: `a derivation of false in ${steps.length} steps, confirmed by the CHC`}
}

type Spec = {id: string, track: Track, group: string, task: string, file: string, removed: string, truth: string, unsat?: boolean, broken?: {id: string, file: string, removed: string, truth: string}[]}
function items(s: Spec): Item[] {
  const source: Source = {benchmark: 'CHC-COMP 2026 LIA-Lin', task: s.task, group: s.group}
  const one = (id: string, file: string, removed: string, truth: string, unsat: boolean, broken?: string): Item => ({
    id, track: s.track, removed, source, truth, ...(broken ? {broken} : {}),
    today: () => { const {chc, b} = load(file); const v = proveRule(b.rule, [b.law], {search: false}); return unsat ? confirmed(chc, b, v) : v },
    frontier: () => {
      const {chc, b} = load(file)
      if (unsat) return confirmed(chc, b, proveRule(b.rule, [b.law]))
      return inferLaws(b.rule, [b.law], [], {ms: FRONTIER_MS})
    },
  })
  // A broken variant's claim is the item's: a sat item's variant is still claimed sat (its error never reached), an
  // unsat item's still claimed unsat.
  return [one(s.id, s.file, s.removed, s.truth, !!s.unsat), ...(s.broken ?? []).map(x => one(x.id, x.file, x.removed, x.truth, !!s.unsat, s.id))]
}

const L = 'vmt-chc-benchmarks/lustre/'
const specs: Spec[] = [
  // A: the step goal of a one-value invariant over a wide transition (55 Int and 22 Bool slots), left undecided.
  {id: 'chc/A/FIREFLY_1', track: 'step goal', group: 'A', task: `${L}FIREFLY_1_000_001.yml`, file: 'FIREFLY_1_000.smt2',
    removed: "Spacer's invariant, one yes/no slot (b13); the search stops on its step goal, 1 <= b13, undecided", truth: "Spacer sat, Golem sat, Eldarica no answer in 200 s (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/A/FIREFLY_1 (mutant e1_1092)', file: 'FIREFLY_1_e1_1092_000.smt2', removed: 'the same claim of the benchmark\'s mutant FIREFLY_1_e1_1092 (one constant, −1 to −2), unsat', truth: "Spacer unsat, Golem unsat (a derivation of 4 steps), Eldarica no answer in 200 s (runs/corpus2/truth-chc); the benchmark's verdict unsat (its .yml)"}]},
  {id: 'chc/A/MESI_i3_e1_447_e3_1180', track: 'step goal', group: 'A', task: `${L}MESI_i3_e1_447_e3_1180_000_001.yml`, file: 'MESI_i3_e1_447_e3_1180_000.smt2',
    removed: "Spacer's invariant: b8, and i6 <= i4 (44 Int and 13 Bool slots); the search stops on i2 + 1 <= b8's step goal, undecided", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/A/MESI_i3_e1_447_e3_1180 (mutant e2_1098 for e3_1180)', file: 'MESI_i3_e1_447_e2_1098_000.smt2', removed: 'the same claim of the benchmark\'s MESI_i3_e1_447_e2_1098, its second mutation e2_1098 in place of e3_1180, unsat', truth: "Spacer unsat, Golem unsat (a derivation of 3 steps), Eldarica unsat (runs/corpus2/truth-chc); the benchmark's verdict unsat (its .yml)"}]},
  // B: Lustre, within the templates, proven once given; the search doesn't find it.
  {id: 'chc/B/hysteresis_2', track: 'search', group: 'B', task: `${L}hysteresis_2_000_001.yml`, file: 'hysteresis_2_000.smt2',
    removed: "Spacer's invariant: b9, and 1 <= i1 or not b1 (proven at once when given)", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/B/hysteresis_2 (the property negated)', file: 'hysteresis_2_000.broken.smt2', removed: 'the query (not O) as O: the property\'s output true, which it is', truth: "Spacer unsat, Golem unsat (a derivation of 2 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  // G: not Lustre, within the templates.
  {id: 'chc/G/s_split_34', track: 'search', group: 'G', task: 'aeval-benchmarks/multi-phase/s_split_34_000_000.yml', file: 's_split_34_000.smt2',
    removed: "Spacer's invariant: −100 <= i0 <= 100, −100 <= i0 + i1 <= 100, −1 <= i1 <= 1 (proven at once when given)", truth: "Spacer sat, Golem no answer in 200 s, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/G/s_split_34 (bound 99)', file: 's_split_34_000.broken.smt2', removed: 'the query i0 > 100 as i0 > 99: i0 reaches 100', truth: "Spacer unsat, Golem unsat (a derivation of 103 steps), Eldarica no answer in 200 s (runs/corpus2/truth-chc)"}]},
  // C: a program counter in yes/no slots, the invariant a bound at a pc.
  {id: 'chc/C/simple.c', track: 'disjunction', group: 'C', task: 'vmt-chc-benchmarks/ctigar/simple.c_000_001.yml', file: 'simple.c_000.smt2',
    removed: "Spacer's invariant: not b0 or not b3, not b2 or not b3, i0 <= i1 or not b2, b2 or b3 or i0 <= 0 or not b0, ... (5 clauses)", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/C/simple.c (query at a reached pc)', file: 'simple.c_000.broken.smt2', removed: 'the query moved to another pc (b1 and b3 set, b0 and b2 not), which the program reaches (Golem: 10 steps)', truth: "Spacer unsat, Golem unsat (a derivation of 10 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  // D: clauses of several linear literals.
  {id: 'chc/D/reve 015', track: 'disjunction', group: 'D', task: 'eldarica-misc/LIA/reve/015-horn_000.yml', file: '015-horn_000.smt2',
    removed: "Spacer's invariant at REC_f_f: i0 + 1 <= i2 or i1 <= i3 or i2 + 1 <= i0, and two more of three linear literals", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/D/reve 015 (off by one)', file: '015-horn_000.broken.smt2', removed: 'a query f(n) + ... = f(n) + ... + 1: the two programs\' results claimed apart by one', truth: "Spacer unsat, Golem unsat (a derivation of 3 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  {id: 'chc/D/gulwani_fig1a', track: 'disjunction', group: 'D', task: 'vmt-chc-benchmarks/ctigar/gulwani_fig1a.c_000_001.yml', file: 'gulwani_fig1a.c_000.smt2',
    removed: "Spacer's invariant: 1 <= i1 or i0 + 50 <= 0 or not b0, beside pc clauses (6 clauses)", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/D/gulwani_fig1a (query at a reached pc)', file: 'gulwani_fig1a.c_000.broken.smt2', removed: 'the query moved to another pc (every pc bit unset), which the program reaches (Golem: 11 steps)', truth: "Spacer unsat, Golem unsat (a derivation of 11 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  // E: atoms over four values or more.
  {id: 'chc/E/three_dots_moving_2', track: 'wide atom', group: 'E', task: 'extra-small-lia/three_dots_moving_2_000.yml', file: 'three_dots_moving_2_000.smt2',
    removed: "Spacer's invariant: i1 + i2 <= 2·i0 + i3, i1 <= i2 + i3, i0 <= i1", truth: "Spacer sat, Golem sat, Eldarica no answer in 200 s (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/E/three_dots_moving_2 (the dots may meet)', file: 'three_dots_moving_2_000.broken.smt2', removed: 'the query without i1 ≠ i2: the count reaching 0 where the dots meet', truth: "Spacer unsat, Golem unsat (a derivation of 3 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  {id: 'chc/E/loop2', track: 'wide atom', group: 'E', task: 'llreve-bench/smt2/clausified/loop__loop2_000_001.yml', file: 'loop__loop2_000.smt2',
    removed: "Spacer's invariant: i0 + i5 = i2 + i3 + 1 (four values), i1 = i4", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/E/loop2 (equal results)', file: 'loop__loop2_000.broken.smt2', removed: 'the query i1 ≠ i4 as i1 = i4: the two programs\' equal results, which they are', truth: "Spacer unsat, Golem unsat (a derivation of 2 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  // F: an invariant that keeps an existential (a projection) or reads a remainder.
  {id: 'chc/F/break_safe.c-1', track: 'projection', group: 'F', task: 'eldarica-misc/LIA/llreve/break_safe.c-1_000.yml', file: 'break_safe.c-1_000.smt2',
    removed: "Spacer's invariant, an existential kept from its projection at inv_main29, bounds and disjunctions at inv_main20 (i3 <= 10, i1 <= 11, 11 <= i1 or i2 <= i1, ...; 49 clauses)", truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/F/break_safe.c-1 (equal results)', file: 'break_safe.c-1_000.broken.smt2', removed: 'the query i1 ≠ i2 as i1 = i2: the two loops\' equal results, which they are', truth: "Spacer unsat, Golem unsat (a derivation of 5 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  {id: 'chc/F/HOLA 38', track: 'projection', group: 'F', task: 'eldarica-misc/LIA/HOLA/38.c_000.yml', file: '38.c_000.smt2',
    removed: "Spacer's invariant, over 22 predicates, reading i mod 2 (at h19: 2·i6 <= i5, i4 <= i7, a remainder), the final check x = 2y made at even i", truth: "Spacer sat, Golem no answer in 200 s, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)",
    broken: [{id: 'chc/F/HOLA 38 (checked at odd i too)', file: '38.c_000.broken.smt2', removed: 'the final check x = 2y made at odd i as well (its guard i mod 2 = 0 dropped)', truth: "Spacer unsat, Golem unsat (a derivation of 21 steps), Eldarica unsat (runs/corpus2/truth-chc)"}]},
  // H: unsat, Lustre: a short derivation.
  {id: 'chc/H/durationThm_1_e1_197', track: 'derivation', group: 'H', task: `${L}durationThm_1_e1_197_000.yml`, file: 'durationThm_1_e1_197_000.smt2', unsat: true,
    removed: "Golem's derivation of false (3 steps): requests that are models of the wide clause with the query in view", truth: "Spacer unsat, Golem unsat (a derivation of 3 steps), Eldarica unsat (runs/corpus2/truth-chc); the benchmark's verdict unsat (its .yml)",
    broken: [{id: 'chc/H/durationThm_1_e1_197 (the original, durationThm_1)', file: 'durationThm_1_000.smt2', removed: 'the claim of the benchmark\'s durationThm_1, the task without mutation e1_197 (three constants −2 back to −1), sat', truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc); the benchmark's verdict sat (its .yml)"}]},
  // I: unsat, the others.
  {id: 'chc/I/O0_terminator_01', track: 'derivation', group: 'I', task: 'hcai-bench/svcomp/O0/O0_terminator_01_false-unreach-call_true-termination_000.yml', file: 'O0_terminator_01_false-unreach-call_true-termination_000.smt2', unsat: true,
    removed: "Golem's derivation of false (4 steps): a start value of at least 100 (any start is allowed)", truth: "Spacer unsat, Golem unsat (a derivation of 4 steps), Eldarica unsat (runs/corpus2/truth-chc); the benchmark's verdict unsat (its .yml)",
    broken: [{id: 'chc/I/O0_terminator_01 (start at most 0, error past 100)', file: 'O0_terminator_01_false-unreach-call_true-termination_000.broken.smt2', removed: 'the start at most 0 and the error at x >= 101: the loop stops at 100', truth: "Spacer sat, Golem sat, Eldarica sat (runs/corpus2/truth-chc)"}]},
  {id: 'chc/I/s_split_01', track: 'derivation', group: 'I', task: 'aeval-unsafe/s_split_01_000_001.yml', file: 's_split_01_000.smt2', unsat: true,
    removed: "Golem's derivation of false: 10,002 steps (a loop to 10,000; past a guided run's 2,000), which an accelerated loop summarizes", truth: "Spacer no answer in 200 s, Golem unsat (a derivation of 10002 steps), Eldarica no answer in 200 s (runs/corpus2/truth-chc); the benchmark's verdict unsat (its .yml)",
    broken: [{id: 'chc/I/s_split_01 (from 4999)', file: 's_split_01_000.broken.smt2', removed: 'the second counter from 4,999: at 10,000 it is 9,999', truth: "Spacer no answer in 200 s, Golem no answer in 200 s, Eldarica no answer in 200 s (runs/corpus2/truth-chc); an inductive invariant, (d <= 5000 and c = 4999) or (d >= 5000 and c = d − 1), checked by z3 (tasks/chc/s_split_01_000.broken.invariant.smt2, three unsat in the same run)"}]},
]

export const chcItems: Item[] = specs.flatMap(items)
