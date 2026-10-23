// The abstract sorts, unknown functions and closures of examples/abstract.ts checked again in Lean: each law's cyclic
// proof exported as lean-kernel/package-check.ts exports its datatype items (lean-kernel/data.ts's dataLean, emit.ts's
// toLean and leanProject), nothing of the Lean side changed. `[ONLY=id,..] bun research/edges/lean-edges.ts <empty
// folder>`, then `lean <folder>/Proofs.lean` with the library on LEAN_PATH (research/edges/lean-edges.sh does both).
// Checked (the suite's lean-edges job, runs/edges/lean2): an abstract sort's lists appended and counted (catAssoc,
// countCat), an unknown constant (firstCons), an unknown function into a list (bindReturn), a map by an unknown function
// (mapLength). Not checked, for two shapes the export's tactics don't close, neither of them new here (PROBE=1 shows
// each with no abstract sort, no unknown and no closure): a datatype of two constructors with fields (`twoCtors`:
// `(2·x + 1) / 2 = x` left after simp, so every `closures` datatype of two closures with captures: runJoin, incIsAdd),
// and two constructor values compared inside a disjunction (`wrapEq`: `h : a = b ∨ ..` against `¬a = b → ..`, so a
// membership by equality: memCons, memCat). Both are in lean-kernel/data.ts, which this track doesn't change; the
// kernel's proofs of them stand.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Bool, type DataLaw, type Nat, type Val, data, define, law, natural, boolean, proveData, self} from '../../core/data.ts'
import {dataLean} from '../../lean-kernel/data.ts'
import {leanProject, toLean} from '../../lean-kernel/emit.ts'
import {laws} from '../../examples/abstract.ts'

// PROBE=1: shapes of the Lean export alone, no abstract sort in them (a datatype of two constructors with fields; a
// datatype of one constructor of one natural compared in a disjunction).
const probes: Record<string, () => DataLaw> = {}
if (process.env.PROBE) {
  const L = (v: unknown) => v as Val, N = (v: unknown) => v as Nat, B = (v: unknown) => v as Bool
  const Two = data('ProbeTwo', {a: {x: natural}, b: {y: natural}})
  const val = define('probeVal', {t: Two}, natural, ({t}) => L(t).match({a: ({x}) => N(x), b: ({y}) => N(y).plus(1)}))
  probes.twoCtors = () => law('val (b y) = y + 1', {y: natural}, ({y}) => N(val(Two.b(y))).eq(N(y).plus(1)))
  const Wrap = data('ProbeWrap', {w: {n: natural}}), Ws = data('ProbeWs', {nil: {}, cons: {head: Wrap, tail: self}})
  const has: ReturnType<typeof define> = define('probeHas', {x: Wrap, xs: Ws}, boolean, ({x, xs}) => L(xs).match({nil: () => L(x).ne(L(x)), cons: ({head, tail}) => L(head).eq(L(x)).or(B(has(x, tail)))}))
  probes.wrapEq = () => law('has x (x :: xs)', {x: Wrap, xs: Ws}, ({x, xs}) => B(has(x, Ws.cons(x, xs))))
}
const only = process.env.ONLY?.split(',')
const items = Object.entries({...laws, ...probes}).filter(([id]) => !only || only.includes(id)).map(([id, mk]) => {
  const l = mk(), v = proveData(l, {ms: 600_000, patience: 3})
  if (!v.proven || !v.checked || !v.proof?.proven || !v.program || v.node === undefined) throw new Error(`${id}: not proven (${v.goal}: ${v.stuck})`)
  return {id: `edges${id.toLowerCase()}`, cyclic: v.proof.proof, data: true, after: dataLean(`edges${id.toLowerCase()}`, l, v.program, v.proof.proof, v.node, id)}
})
const file = toLean(items as Parameters<typeof toLean>[0], {title: 'abstract sorts, unknown functions, closures'})
const out = process.argv[2]
if (!out) throw new Error('usage: bun research/edges/lean-edges.ts <empty folder>')
mkdirSync(out, {recursive: true})
for (const [name, text] of Object.entries(leanProject(file))) writeFileSync(join(out, name), text)
console.log(`${items.length} items, ${[...file.matchAll(/^theorem /gm)].length} theorems in ${out}`)
