// A checker for dag.ts's certificates, outside the trusted base (a prototype of what the kernel would check).
// A DAG refutes a goal when every node, in order, gives a clause (a set of decisions that can't all hold, each decision
// an atom lin <= 0 decided true or false, over the integers) and the root's clause is empty:
//   - a leaf {leaf: [[lin, holds], ...], steps, products?, squares?}: its decisions as a path, and `steps` a refutation
//     (core/check.ts's checkRefutation) of the rows the kernel reads off the goal at that path (kernel.ts's
//     leafConstraints, with withProducts' products and squares): exactly a kernel tree's leaf check at that path. Its
//     clause: those decisions.
//   - a resolution {res: [a, b], on: lin}: a and b earlier nodes, a's clause deciding lin <= 0 true, b's deciding it
//     false; its clause is the union of the two less that atom (no other atom decided both ways in the union).
// An atom and its flip are one: lin <= 0 false is 1 − lin <= 0 true (kernel.ts's canonFlip), so a decision is read as
// the smaller of the two canonical texts with the sign it gives that one.
// Sound because a leaf's rows hold in every model of the hypotheses where its path holds (what the kernel's leaf
// check already relies on), so its clause is a consequence of the hypotheses; resolution keeps consequences; the empty
// clause says no model exists.
import {checkRefutation} from '../../core/check.ts'
import type {Lin, Step} from '../../core/solver.ts'
import {type Goal, type Path, canon, canonFlip, leafConstraints, withProducts} from '../../kernel/kernel.ts'

type Node = {leaf: [Lin, boolean][], steps: Step[], products?: [number, number][], squares?: Lin[]} | {res: [number, number], on: Lin}
const constant = (lin: Lin) => Object.keys(lin).every(key => key === '1' || lin[key] === 0)
const decision = (lin: Lin, holds: boolean): [string, boolean] => { const a = canon(lin), b = canonFlip(lin); return a <= b ? [a, holds] : [b, !holds] }

export function checkDag(goal: Goal, dag: {nodes: Node[], root: number}): {ok: true} | {ok: false, why: string} {
  const clauses: Map<string, boolean>[] = []
  for (const [i, n] of dag.nodes.entries()) {
    const c = new Map<string, boolean>()
    if ('leaf' in n) {
      const path: Path = new Map()
      for (const [lin, holds] of n.leaf) {
        if (constant(lin)) return {ok: false, why: `node ${i}: a constant atom`}
        const id = canon(lin)
        if (path.has(id) || path.has(canonFlip(lin))) return {ok: false, why: `node ${i}: an atom decided twice`}
        path.set(id, {lin, holds})
        const [v, pos] = decision(lin, holds)
        c.set(v, pos)
      }
      if (!checkRefutation(withProducts(leafConstraints(goal, path), n.products ?? [], n.squares), n.steps)) return {ok: false, why: `node ${i}: the derivation doesn't refute the rows at its path`}
    } else {
      const [a, b] = n.res
      if (!(Number.isInteger(a) && Number.isInteger(b) && a >= 0 && b >= 0 && a < i && b < i)) return {ok: false, why: `node ${i}: a parent not before it`}
      if (constant(n.on)) return {ok: false, why: `node ${i}: a constant atom`}
      const [v, pos] = decision(n.on, true)
      if (clauses[a]!.get(v) !== pos || clauses[b]!.get(v) !== !pos) return {ok: false, why: `node ${i}: the parents don't decide the atom true and false`}
      for (const parent of [clauses[a]!, clauses[b]!]) for (const [w, p] of parent) {
        if (w === v) continue
        if (c.has(w) && c.get(w) !== p) return {ok: false, why: `node ${i}: an atom decided both ways`}
        c.set(w, p)
      }
    }
    clauses.push(c)
  }
  const root = clauses[dag.root]
  if (!(Number.isInteger(dag.root) && root)) return {ok: false, why: 'no root'}
  if (root.size) return {ok: false, why: 'the root clause is not empty'}
  return {ok: true}
}
