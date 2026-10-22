// The datatype track's corpus: laws about recursive datatypes as values (examples/data.ts), each stated with nothing a
// proof needs: no induction, no rank, no lemma. `frontier` is core/data.ts's search (`proveData`); `today` is what the
// library proves of the same law without it, on the same encoding (the same facts, so only the search differs):
//   - the kernel's prover on the law with the definitions unfolded, no cycle (`proveData` with `induction: false`)
//   - core/cycles.ts's `findCycles` on the law as a claim over the encoding's facts, with each map's values on the
//     codes Lean's twin defines (`codeValues`) and that a value's fields have smaller codes (`orderFacts`), so a rank
//     linear in the codes exists for it to find
// Either proving the law counts for today. A broken variant is an item too (`broken`): it counts when nothing proves it.
import type {Verdict} from '../../core/dsl.ts'
import {type DataLaw, type DataVerdict, codeValues, encY, factsOf, orderFacts, programOf, proveData} from '../../core/data.ts'
import {findCycles} from '../../core/cycles.ts'
import {broken, laws} from '../../examples/data.ts'
import {intWalls} from '../../examples/arith.ts'
import type {Item} from './corpus.ts'

const asVerdict = (v: DataVerdict): Verdict => ({proven: v.proven, checked: v.checked, ...(v.goal ? {goal: v.goal, stuck: v.stuck} : {}),
  ...(v.counterexample ? {why: `broken at ${JSON.stringify(v.counterexample)}`} : {}),
  ...(v.proven ? {found: {facts: [`by ${v.scheme}`, ...v.lemmas.map(x => `lemma: ${x}`)]}} : {})})
function today(l: DataLaw): Verdict {
  const plain = proveData(l, {induction: false, ms: 30_000})
  if (plain.proven && plain.checked) return asVerdict(plain)
  const p = programOf([l]), out = findCycles([...factsOf(p).facts, ...orderFacts(p)], [{name: l.name, concl: encY(p, l.holds, new Map())}], {values: codeValues(p), ms: 30_000})
  return {proven: out.proven, checked: out.checked, ...(out.goal ? {goal: out.goal, stuck: out.stuck} : {}), ...(out.why ? {why: out.why} : {})}
}
const frontier = (l: DataLaw): Verdict => asVerdict(proveData(l))

export const dataItems: Item[] = [
  // Integers (core/data.ts's integer sort) through recursion.
  ...Object.entries(intWalls).map(([name, mk]): Item => ({id: `datatype/integers/${name}`, track: 'datatype', removed: 'the induction and any lemma', today: () => today(mk()), frontier: () => frontier(mk())})),
  ...Object.entries(laws).map(([name, mk]): Item => ({id: `datatype/${name}`, track: 'datatype', removed: 'the induction (which argument, where each cycle returns, the rank) and any lemma',
    today: () => today((mk as () => DataLaw)()), frontier: () => frontier((mk as () => DataLaw)())})),
  ...Object.entries(broken).map(([name, mk]): Item => ({id: `datatype/${name} (broken)`, track: 'datatype', removed: 'the induction and any lemma', broken: `datatype/${name}`,
    today: () => today(mk()), frontier: () => frontier(mk())})),
]
