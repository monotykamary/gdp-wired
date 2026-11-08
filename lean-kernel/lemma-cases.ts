// Shared no-search certificates for the TypeScript tests and Lean conformance exporter.
import type {C} from '../core/machine.ts'
import {type Lin, type Step, add, k, scale, sub, v} from '../core/solver.ts'
import {type Goal, type LemmaCut, type Path, type Tree, canon, leafConstraints, lemmaPath} from '../kernel/kernel.ts'

export function lemmaCutFixture() {
  const flip = (r: Lin): Lin => add(k(1), scale(r, -1))
  const a = v('a'), b = v('b'), c = v('c'), ab = sub(a, b)
  const hyps: C[] = [
    {op: '<=', a: {op: 'var', name: 'a'}, b: {op: 'var', name: 'b'}},
    {op: '<=', a: {op: 'var', name: 'b'}, b: {op: 'const', value: 0}},
    {op: '<', a: {op: 'const', value: 0}, b: {op: 'var', name: 'a'}},
    {op: '<=', a: {op: 'var', name: 'c'}, b: {op: 'const', value: 0}},
  ]
  const goal: Goal = {name: 'conditional cut', hyps}
  const decide = (r: Lin, holds: boolean): Path => new Map([[canon(r), {lin: r, holds}]])
  function leaf(g: Goal, path: Path, wanted: Lin[]): Tree {
    const rows = leafConstraints(g, path)
    const steps: Step[] = wanted.map(lin => {
      const index = rows.findIndex(r => canon(r.lin) === canon(lin))
      if (index < 0) throw Error('test input row missing: ' + canon(lin))
      return {kind: 'input', index}
    })
    steps.push({kind: 'combine', a: 0, b: 1, ma: 1, mb: 1})
    if (wanted.length === 3) steps.push({kind: 'combine', a: 3, b: 2, ma: 1, mb: 1})
    return {leaf: steps}
  }
  const proofPath = decide(a, false)
  proofPath.set(canon(c), {lin: c, holds: true})
  const entry: LemmaCut = {when: [c], cut: a, slice: [0, 1], tree: leaf({...goal, hyps: hyps.slice(0, 2)}, proofPath, [ab, b, flip(a)])}
  const yes = decide(c, true), no = decide(c, false)
  const tree: Tree = {split: c, yes: leaf(goal, lemmaPath([entry], yes), [a, flip(a)]), no: leaf(goal, no, [c, flip(c)])}
  const legacy = leaf(goal, new Map(), [ab, b, flip(a)])
  
  return {a, b, c, ab, hyps, goal, entry, tree, legacy, flip, leaf, yes, no}
}
