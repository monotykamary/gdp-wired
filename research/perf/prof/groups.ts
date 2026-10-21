// The size of each groups law's proof (examples/groups.ts), as the Lean export checks it: nodes, leaves, the steps of
// every leaf's refutation, products, and the goal's hypotheses: `bun research/perf/prof/groups.ts`.
import {groupLaws, groups} from '../../../examples/groups.ts'
import {proveStepLaws} from '../../../kernel/prove.ts'
import type {Tree} from '../../../kernel/kernel.ts'

const r = groups(), m = r.machine
const size = (t: Tree): {nodes: number, leaves: number, steps: number, products: number, maxSteps: number} => {
  if ('leaf' in t) return {nodes: 1, leaves: 1, steps: t.leaf.length, products: t.products?.length ?? 0, maxSteps: t.leaf.length}
  const a = size(t.yes), b = size(t.no)
  return {nodes: 1 + a.nodes + b.nodes, leaves: a.leaves + b.leaves, steps: a.steps + b.steps, products: a.products + b.products, maxSteps: Math.max(a.maxSteps, b.maxSteps)}
}
for (const [i, sl] of groupLaws().entries()) {
  const t = performance.now(), out = proveStepLaws(m, [], [sl]), ms = Math.round(performance.now() - t)
  const trees = out.proof?.trees ?? {}
  for (const [name, tree] of Object.entries(trees)) console.log(JSON.stringify({law: i, name, ms, ...size(tree), json: JSON.stringify(tree).length}))
  const lawTrees = out.proof?.laws?.trees ?? {}
  console.log(JSON.stringify({law: i, lawsTrees: Object.keys(lawTrees).length, lawsJson: JSON.stringify(lawTrees).length}))
}
