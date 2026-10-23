// The second frontier corpus: benchmark tasks gdp-wired's benchmark runs of 0.21.0 left unproven, each standing for a
// group of tasks it fails on for one reason (CHC-COMP 2026's LIA-Lin, TIP 2015, TermComp's integer transition systems,
// SV-COMP's termination tasks), where another tool succeeds (README.md: the groups, and the score at 0.21.0). Each item is a task as the library's own language states it: the
// task's file (tasks/, vendored at the benchmark's pinned commit) read by the translation its benchmark run used
// (compare/chc, compare/tip, compare/term), so the statement is the task's, not a weaker one. Its broken variants are
// the same task changed so that it is false (checked by an outside tool), which nothing may prove.
//
// The interface is round 1's (research/frontier/corpus.ts): `today` is the library's prover alone, `frontier` the
// library with its search (what the benchmark run did), each a Verdict, and an item counts when it is proven and checked.
// `bun research/frontier2/score.ts` runs both, `jobs.ts` makes the per-item job list.
import type {Verdict} from '../../core/dsl.ts'
import {chcItems} from './chc.ts'
import {tipItems} from './tip.ts'
import {termItems} from './term.ts'
import {nontermItems} from './nonterm.ts'

// The areas, each a reason the library fails on a group of tasks (README.md has the groups and their counts).
export type Track =
  | 'step goal' // a small invariant's step goal over a wide transition, undecided at the prover's budget
  | 'search' // an invariant within the templates the search didn't find
  | 'disjunction' // an invariant clause of several literals (a program counter in bits, case splits)
  | 'wide atom' // an invariant atom over four or more values
  | 'projection' // an invariant that keeps an existential from its projection
  | 'derivation' // a refutation: a derivation of false the runs don't find (the claim: the error is reached)
  | 'lemma' // a lemma about another function the proof needs (an equation, a conditional lemma, a theory)
  | 'generalization' // an accumulator's or a recursion's generalization past the conjectures
  | 'integer recursion' // integer arithmetic computed through recursion (binary numbers, powers)
  | 'nested recursion' // a function called in its own argument
  | 'induction' // an induction the search doesn't choose (two lists together), or more time
  | 'termination' // a definition whose termination needs a lemma about another function
  | 'rank' // a rank of a shape the search finds but doesn't fit (reading no param, in order)
  | 'nonlinear rank' // a rank past linear: multiphase, by cases of a sign, a min
  | 'sampling' // a loop whose runs the search doesn't sample (inputs an equation pins, no turn at all)
  | 'nontermination' // a run that never ends: no state repeats on it, or the random runs don't reach where it starts

// The tasks an item stands for: its benchmark and file, and the group of the README it is one of.
export type Source = {benchmark: 'CHC-COMP 2026 LIA-Lin' | 'TIP 2015' | 'TermComp ITS' | 'SV-COMP termination', task: string, group: string}
// `broken`: a broken variant (of the item named), which counts when nothing proves it. `truth`: how the statement was
// checked true (or, for a broken variant, false) outside the library.
export type Item = {id: string, track: Track, removed: string, broken?: string, today: () => Verdict, frontier?: () => Verdict, source?: Source, truth?: string}

export const corpus: Item[] = [...chcItems, ...tipItems, ...termItems, ...nontermItems]
