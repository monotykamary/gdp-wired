// The corpus's TIP 2015 items: problems the benchmark run translates (or whose definitions the library refuses) and
// doesn't prove at 0.21.0 (runs/modal/arith/tip-gdp), each read from tasks/tip/ (tip-org/benchmarks at bace5b2) by
// compare/tip's own translation, which agrees with TIP's evaluator on random values (compare/tip/solve.ts's `agree`).
// `frontier` is proveData as the benchmark ran it (57 s of counted work); `today` is proveData without induction (the
// definitions unfolded, the kernel's prover alone). A problem whose definitions the library refuses (a termination it
// doesn't prove: a heap sort's toList, McCarthy's nested m on an Int) is still an item: its statement is TIP's, the
// library refuses to take its functions, and the verdict is not proven with the refusal as `why`.
// Each has a broken variant, the same problem with its goal made false (`.broken.smt2`, the change in its first line),
// which must be refused. groups_tip.py counts the groups. Outside the library: each problem through the benchmark's own
// runner, Vampire and cvc5 with conjecture generation at 600 s (`modal run compare/tip/modal_tip.py --out
// runs/corpus2/truth-tip-tools --tools vampire,cvc5cg --limit 600 --only <the 15 problems>`), and truth-tip.json's jobs
// (`python3 modal/run.py --jobs research/frontier2/truth-tip.json --out runs/corpus2/truth-tip-eval`): TIP's evaluator
// at random values on every problem and variant (tipeval.ts), and compare/tip/solve.ts on each broken variant.
import {readFileSync} from 'node:fs'
import type {Verdict} from '../../core/dsl.ts'
import {type DataVerdict, proveData} from '../../core/data.ts'
import {Unsupported, parseTip} from '../../compare/tip/tip.ts'
import {translate} from '../../compare/tip/translate.ts'
import type {Item, Track} from './corpus.ts'

const asVerdict = (v: DataVerdict): Verdict => ({proven: v.proven, checked: v.checked, ...(v.goal ? {goal: v.goal, stuck: v.stuck} : {}),
  ...(v.counterexample ? {why: `broken at ${JSON.stringify(v.counterexample)}`} : {}),
  ...(v.proven ? {found: {facts: [`by ${v.scheme}`, ...v.lemmas.map(x => `lemma: ${x}`)]}} : {})})
// The problem translated, then proven; a refusal of the translation (Unsupported: the library doesn't take a definition)
// is the verdict's `why`.
function run(task: string, broken: boolean, prove: (l: ReturnType<typeof translate>['law']) => DataVerdict): Verdict {
  const file = `${task}${broken ? '.broken' : ''}.smt2`
  let tr
  try { tr = translate(parseTip(readFileSync(`${import.meta.dir}/tasks/tip/${file}`, 'utf8')), file) } catch (e) {
    if (e instanceof Unsupported) return {proven: false, checked: false, why: `refused: ${e.message}`}
    throw e
  }
  return asVerdict(prove(tr.law))
}
const today = (task: string, broken: boolean) => run(task, broken, l => proveData(l, {induction: false, ms: 30_000}))
const frontier = (task: string, broken: boolean) => run(task, broken, l => proveData(l, {ms: 57_000}))

type Spec = {task: string, track: Track, group: string, removed: string, truth: string, change: string}
// truth: what proves it outside the library (runs/corpus2/truth-tip-tools: compare/tip/modal_tip.py's Vampire and cvc5cg at
// 600 s on the benchmark's own file; runs/modal/tip/full2 at 60 s), or, where nothing does, TIP's own statement (a
// theorem, not in its false/) and TIP's evaluator at random values (runs/corpus2/truth-tip-eval, tipeval.ts).
const specs: Spec[] = [
  {task: 'prod/lemma_09', track: 'lemma', group: 'an equation about another function (6 of the 20 read)', change: 'rev (y ++ x) for rev (x ++ y)',
    removed: '++ associative and rev (l ++ [z]) = z :: rev l, equations about other functions', truth: 'Vampire (0.04 s) and cvc5cg (0.02 s) in truth-tip-tools; cvc5, cvc5cg, Vampire at 60 s in full2. The translation takes the goal\'s sort variable at the naturals (its `changes`), the same claim by parametricity: no function here reads an element.'},
  {task: 'isaplanner/prop_53', track: 'lemma', group: 'an equation about another function (6 of the 20 read)', change: 'sort (n :: xs) for sort xs',
    removed: 'the bridges for == and <=, then count n (insort x xs) = count n (x :: xs)', truth: ''},
  {task: 'prod/prop_14', track: 'lemma', group: 'a conditional lemma (5 of the 20 read)', change: 'sorted (1 :: isort x) for sorted (isort x)',
    removed: 'a conditional lemma: sorted xs ⇒ sorted (insert y xs) (and the bridge for <=)', truth: ''},
  {task: 'prod/prop_42', track: 'lemma', group: 'a conditional lemma (5 of the 20 read)', change: 'the implication reversed',
    removed: 'a conditional lemma about another argument: elem x z ⇒ elem x (union y z); x == y ⇒ x = y', truth: ''},
  {task: 'tip2015/sort_nat_ISortPermutes', track: 'lemma', group: 'a theory of several lemmas (6 of the 20 read)', change: 'zero :: xs as the permuted list',
    removed: 'a theory of permutations: isPermutation ys zs ⇒ isPermutation (insert x ys) (x :: zs), elem x (insert x ys), ...', truth: ''},
  {task: 'prod/prop_35', track: 'generalization', group: "an accumulator's generalisation (2 of the 20 read)", change: 'qexp y x 1 for qexp x y 1',
    removed: "the accumulator's generalisation qexp x y z = exp x y · z, with · associative and commutative", truth: ''},
  {task: 'isaplanner/prop_49', track: 'generalization', group: "an accumulator's generalisation (2 of the 20 read)", change: 'butlastConcat ys xs for butlastConcat xs ys',
    removed: 'a generalisation past 8 symbols: butlast (xs ++ y :: ys) = xs ++ butlast (y :: ys)', truth: 'Vampire (0.31 s) and cvc5cg (0.11 s) in truth-tip-tools; cvc5, cvc5cg, Vampire at 60 s in full2. The translation takes the goal\'s sort variable at the naturals (its `changes`), the same claim by parametricity: no function here reads an element.'},
  {task: 'tip2015/weird_nat_add3acc_spec', track: 'generalization', group: 'add3acc by well-founded recursion (9 tasks, none proven)', change: 'z + 1 for z on the right',
    removed: "the accumulator's generalisation over add3acc's own recursion, with TIP's plus related to +", truth: 'Vampire (0.17 s) in truth-tip-tools (cvc5cg out of its 600 s); Vampire at 60 s in full2.'},
  {task: 'isaplanner/prop_84', track: 'induction', group: 'induction on two lists together (1 of the 20 read)', change: 'len zs for len ys in take and drop',
    removed: 'induction on ys with cases of xs at each step (two lists together)', truth: 'Vampire (0.31 s) and cvc5cg (0.09 s) in truth-tip-tools; cvc5, cvc5cg, Vampire at 60 s in full2. The translation takes the goal\'s sort variable at the naturals (its `changes`), the same claim by parametricity: no function here reads an element.'},
  {task: 'tip2015/list_PairOdds', track: 'induction', group: 'more time (7 proven by diag-t300 only)', change: 'evens xs for odds xs',
    removed: 'time: the search finds it in 137.68 s (diag-t300), past the 60 s', truth: 'Vampire (0.91 s) in truth-tip-tools (cvc5cg out of its 600 s); Vampire at 60 s in full2. The translation takes the goal\'s sort variable at the naturals (its `changes`), the same claim by parametricity: no function here reads an element.'},
  {task: 'tip2015/bin_nat_plus', track: 'integer recursion', group: 'binary numbers (16 tip2015/bin_* theorems, 14 unproven)', change: 'toNat (s y) for toNat y on the right',
    removed: 'toNat (s x) = 1 + toNat x, then + associative and commutative (TIP asserts the last two)', truth: ''},
  {task: 'tip2015/nat_pow_pow', track: 'integer recursion', group: 'powers and factorials (4 that threw in full2, all 4 unproven)', change: 'x^(y + z) for x^(y·z)',
    removed: 'x^(y·z) = (x^y)^z through recursive times and plus: pow of a product, times associative and commutative, distributive', truth: ''},
  {task: 'tip2015/sort_HSortCount', track: 'termination', group: "termination not proven (91 theorems; toList's 16 among them)", change: 'count x (x :: xs) on the right',
    removed: "toList (hmerge p q)'s decrease: size (hmerge p q) = size p + size q − 1, a lemma about another function; then the count's lemmas", truth: ''},
  {task: 'tip2015/mccarthy91_M1', track: 'nested recursion', group: "recursion on an Int (14 theorems; McCarthy's m, nested, 2 of them)", change: 'n <= 102 for n <= 100 (m 102 = 92)',
    removed: "m's termination (a call in its own argument, on an Int: the measure 101 − n where n <= 100) and the induction it gives", truth: ''},
  {task: 'tip2015/mccarthy91_M2', track: 'nested recursion', group: "recursion on an Int (14 theorems; McCarthy's m, nested, 2 of them)", change: 'n >= 100 for n >= 101 (m 100 = 91)',
    removed: "m's termination (a call in its own argument, on an Int), then m n = n − 10 above 100 by unfolding", truth: 'Vampire (11.42 s) in truth-tip-tools (cvc5cg out of its 600 s); Vampire at 60 s in full2.'},
]

const source = (s: Spec) => ({benchmark: 'TIP 2015' as const, task: `tip-org/benchmarks@bace5b2 benchmarks/${s.task}.smt2`, group: s.group})
export const tipItems: Item[] = specs.flatMap((s): Item[] => [
  {id: `tip/${s.task}`, track: s.track, removed: s.removed, source: source(s), truth: s.truth || "no outside prover within 600 s (Vampire and cvc5cg, truth-tip-tools); TIP's theorem (not in its false/), and TIP's evaluator held at 5,000 random values (truth-tip-eval)",
    today: () => today(s.task, false), frontier: () => frontier(s.task, false)},
  {id: `tip/${s.task} (broken: ${s.change})`, track: s.track, removed: s.removed, broken: `tip/${s.task}`, source: source(s), truth: "false: TIP's evaluator breaks it at random values (truth-tip-eval's eval-broken), and compare/tip/solve.ts refutes it with a counterexample TIP's evaluator confirms, where the library takes its definitions (solve-broken)",
    today: () => today(s.task, true), frontier: () => frontier(s.task, true)},
])
