// The nontermination items: TermComp's integer transition systems (TPDB-ARI at 183f29d) another tool proves
// nonterminating and gdp-wired's benchmark runs left unanswered, with no lasso found (README.md's language gap:
// runs/corpus2/failures-its-term-gdp.txt's "long runs, no state repeated" and "the runs stop within 5 turns on
// average"). Each is the task as compare/term/translate.ts reads it, one loop over every location from any integers,
// and the claim is NonTerm.lean's NeverEnds of that loop: some run from the entrypoint never ends, exactly when the task
// doesn't terminate. `today` is the lassos of random runs (core/nonterm.ts with `lassos`, all compare/term found before
// the claim), `frontier` the whole search (policies, a recurrent set) within the benchmark's 51 s; each certificate is
// checked by the kernel (kernel.ts's checkRecur). A broken variant is the task changed so that every run ends (its
// terminating twin, checked by another tool), which nothing may prove never ends.
import {readFileSync} from 'node:fs'
import type {Verdict} from '../../core/dsl.ts'
import {findNeverEnds} from '../../core/nonterm.ts'
import {type Loop, checkRecur} from '../../kernel/kernel.ts'
import {parseAri} from '../../compare/term/ari.ts'
import {build} from '../../compare/term/translate.ts'
import type {Item, Source} from './corpus.ts'

const loopOf = (file: string): Loop => build(parseAri(readFileSync(`${import.meta.dir}/tasks/${file}`, 'utf8')), file.split('/').pop()!).loop
function never(l: Loop, lassos: boolean): Verdict {
  const v = findNeverEnds(l, {ms: lassos ? 2000 : 51_000, lassos})
  if (!v.recur) return {proven: false, checked: false, why: v.why ?? 'none found'}
  return {proven: v.proven, checked: v.checked && checkRecur(l, v.recur), found: {facts: [`${v.by}: a stem of ${v.recur.stem.length} turns, a set of ${JSON.stringify(v.recur.set).length} bytes`]}}
}

type Spec = {task: string, file: string, removed: string, group: string, truth: string, broken: {file: string, what: string, truth: string}}
const specs: Spec[] = [
  {task: 'Integer_Transition_Systems/Britikov_26/toy2.t2.ari', file: 'its/toy2.t2.ari', group: 'the runs stop within 5 turns on average',
    removed: 'a start past the guard\'s constant: while x >= 100: x := x + 1 (the random starts are within 64), the set x >= 100',
    truth: 'LoAT NO, LoAT abmc NO (runs/modal/term/full1, and again in runs/corpus2/truth-nonterm)', broken: {file: 'its/toy2.t2.broken.ari', what: 'x := x + 1 made x := x − 1', truth: 'KoAT2 Finite on the same task entered through a fresh location (tasks/its/toy2.t2.broken.entry.ari: KoAT2 refuses a rule back to the entrypoint), LoAT abmc YES, LoAT MAYBE (runs/corpus2/truth-nonterm, truth-nonterm-entry)'}},
  {task: 'Integer_Transition_Systems/Britikov_26/toy4.t2.ari', file: 'its/toy4.t2.ari', group: 'the runs stop within 5 turns on average',
    removed: 'a turn whose fresh y is chosen outside {0, 1} (while y > 1 or y < 0: x := x + 1, y free once x >= 100)',
    truth: 'LoAT NO, LoAT abmc NO (runs/modal/term/full1, and again in runs/corpus2/truth-nonterm)', broken: {file: 'its/toy4.t2.broken.ari', what: 'y := 0 once x >= 100 (toy3\'s rule)', truth: 'KoAT2 Finite, LoAT abmc YES, LoAT MAYBE (runs/corpus2/truth-nonterm)'}},
  {task: 'Integer_Transition_Systems/From_AProVE_2014/Choose.jar-obl-8.ari', file: 'its/Choose.jar-obl-8.ari', group: 'long runs, no state repeated',
    removed: 'a growing run: from 3, +1 while below 6, then +3 forever (the set x >= 3, the rule chosen by its guard)',
    truth: 'LoAT NO, LoAT abmc NO (runs/modal/term/full1, and again in runs/corpus2/truth-nonterm)', broken: {file: 'its/Choose.jar-obl-8.broken.ari', what: 'the +3 rule bounded by x < 20', truth: 'KoAT2 Finite, LoAT abmc YES, LoAT MAYBE (runs/corpus2/truth-nonterm)'}},
  {task: 'Integer_Transition_Systems/From_AProVE_2014/NO_10.jar-obl-8.ari', file: 'its/NO_10.jar-obl-8.ari', group: 'long runs, no state repeated',
    removed: 'two counters climbing together: from 0 and 100, both + 1 while the second is above (the set y − x = 100)',
    truth: 'LoAT NO, LoAT abmc NO (runs/modal/term/full1, and again in runs/corpus2/truth-nonterm)', broken: {file: 'its/NO_10.jar-obl-8.broken.ari', what: 'the second counter kept (y\' = y)', truth: 'KoAT2 Finite, LoAT abmc YES, LoAT MAYBE (runs/corpus2/truth-nonterm)'}},
  {task: 'Integer_Transition_Systems/From_AProVE_2014/EvenOdd.jar-obl-8.ari', file: 'its/EvenOdd.jar-obl-8.ari', group: 'long runs, no state repeated',
    removed: 'two locations alternating while a value falls below 0 forever (even and odd on a negative number)',
    truth: 'LoAT NO, LoAT abmc NO (runs/modal/term/full1, and again in runs/corpus2/truth-nonterm)', broken: {file: 'its/EvenOdd.jar-obl-8.broken.ari', what: 'the negative branches\' x − 1 made x + 1', truth: 'KoAT2 Finite, LoAT MAYBE, LoAT abmc no answer in 70 s (runs/corpus2/truth-nonterm)'}},
]

const its = 'TermComp ITS' as const
const id = (s: Spec) => `nonterm/${s.task.split('/').pop()!.replace(/\.ari$/, '')}`
export const nontermItems: Item[] = specs.flatMap(s => {
  const source: Source = {benchmark: its, task: s.task, group: s.group}
  return [
    {id: id(s), track: 'nontermination' as const, removed: s.removed, source, truth: s.truth, today: () => never(loopOf(s.file), true), frontier: () => never(loopOf(s.file), false)},
    {id: `${id(s)} (broken: ${s.broken.what})`, track: 'nontermination' as const, removed: s.removed, broken: id(s), source, truth: s.broken.truth,
      today: () => never(loopOf(s.broken.file), true), frontier: () => never(loopOf(s.broken.file), false)},
  ]
})
