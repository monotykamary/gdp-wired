// The definitions research/termination admits (a decrease through a size law the kernel proved, a weighted size of a
// list of trees, halves' size laws, a merge's by cases on the user's ≤) checked again in Lean: each law's cyclic proof exported as lean-kernel/package-check.ts exports its
// datatype items (lean-kernel/data.ts's dataLean: each well-founded function with `termination_by` its measure and
// `decreasing_by` its decrease, the size laws it reads as theorems before it). `[ONLY=id,..] bun
// research/termination/lean-termination.ts <empty folder>`, then `lean <folder>/Proofs.lean` with the library on
// LEAN_PATH (research/termination/lean-termination.sh does both).
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type DataLaw, type Nat, type Val, data, define, law, natural, proveData, self, when} from '../../core/data.ts'
import {dataLean} from '../../lean-kernel/data.ts'
import {Heap as UHeap, List, bsort, heapList} from '../../examples/data.ts'
import {leanProject, toLean} from '../../lean-kernel/emit.ts'

const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat
// A skew heap merged, and read off in order: toList's call is on the merge of its two subheaps, below the heap by the
// merge's size law (size(hm(x, y)) + 1 <= size(x) + size(y), proven by the merge's own recursion).
const Heap = data('THeap', {node: {l: self, v: natural, r: self}, nil: {}}), Nats = data('TNats', {nil: {}, cons: {h: natural, t: self}})
const hm: ReturnType<typeof define> = define('thmerge', {x: Heap, y: Heap}, Heap, ({x, y}) => L(x).match({
  node: ({l: z, v: x2, r: x3}) => L(y).match({node: ({l: x4, v: x5, r: x6}) => when(N(x2).atMost(x5), Heap.node(hm(x3, y), x2, z), Heap.node(hm(x, x6), x5, x4)), nil: () => L(x)}),
  nil: () => L(y)}))
const toList: ReturnType<typeof define> = define('ttoList', {x: Heap}, Nats, ({x}) => L(x).match({node: ({l, v, r}) => Nats.cons(v, toList(hm(l, r))), nil: () => Nats.nil}))
// A ring weighted across its functions, with a call in another's argument (TIP's propositional models): ¬(l ∧ r) read
// again as l ∧ ¬r, its measure (a fold of the formula, Not weighing twice, then 1 at tboth and 0 at tev), Lean's
// `mutual` block, `termination_by` each, the nested call's value an atom of the decrease.
const Form = data('TForm', {and: {l: self, r: self}, not: {f: self}, atom: {}})
const ev: ReturnType<typeof define> = define('tev', {f: Form, k: natural}, natural, ({f, k}) => L(f).match({
  and: ({l, r}) => N(both(r, ev(l, k))),
  not: ({f: g}) => L(g).match({and: ({l, r}) => N(ev(Form.and(l, Form.not(r)), k)), not: ({f: h}) => N(ev(h, k)), atom: () => N(k)}),
  atom: () => N(k).plus(2)}))
const both: ReturnType<typeof define> = define('tboth', {f: Form, k: natural}, natural, ({f, k}) => N(ev(f, N(k).plus(1))))
// Bitonic sort's halves (examples/data.ts): bmerge's and bsort's calls on evens and odds, below by the halves' size law
// (2·size(evens(x)) <= size(x) + 2 and 2·size(odds(x)) <= size(x) + 1, one law proven by induction on both at once);
// a skew heap over the user's ≤ read off, its merge's size law proven by cases on that ≤.
export const laws: Record<string, () => DataLaw> = {
  toListOne: () => law('one node read off', {v: natural}, ({v}) => L(toList(Heap.node(Heap.nil, v, Heap.nil))).eq(Nats.cons(v, Nats.nil))),
  // (by name only, `ONLY=bsortNil`: Lean takes bmerge's and bsort's definitions, their decrease lemmas and the halves'
  // size law by mutual induction, and leaves the program's facts_hold unsolved at sort2's `if decide (y ≤ x)`, an
  // export gap outside termination)
  bsortNil: () => law('bitonic sort of the empty list', {}, () => L(bsort(List.nil)).eq(List.nil)),
  heapListOne: () => law('one node read off a heap over the user\'s ≤', {v: natural}, ({v}) => L(heapList(UHeap.node(UHeap.nil, v, UHeap.nil))).eq(List.cons(v, List.nil))),
  evRing: () => law('an atom under two nots, read by both', {k: natural}, ({k}) => N(both(Form.not(Form.not(Form.atom)), k)).eq(N(k).plus(3))),
}
if (import.meta.main) {
  const only = process.env.ONLY?.split(',')
  const items = Object.entries(laws).filter(([id]) => (only ? only.includes(id) : id !== 'bsortNil')).map(([id, mk]) => {
    const l = mk(), v = proveData(l, {ms: 600_000, patience: 3})
    if (!v.proven || !v.checked || !v.proof?.proven || !v.program || v.node === undefined) throw new Error(`${id}: not proven (${v.goal}: ${v.stuck})`)
    return {id: `term${id.toLowerCase()}`, cyclic: v.proof.proof, data: true, after: dataLean(`term${id.toLowerCase()}`, l, v.program, v.proof.proof, v.node, id)}
  })
  const file = toLean(items as Parameters<typeof toLean>[0], {title: 'well-founded definitions'})
  const out = process.argv[2]
  if (!out) throw new Error('usage: bun research/termination/lean-termination.ts <empty folder>')
  mkdirSync(out, {recursive: true})
  for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
  console.log(`${items.length} items, ${[...file.matchAll(/^theorem /gm)].length} theorems in ${out}`)
}
