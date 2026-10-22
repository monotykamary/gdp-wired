// The DAG against the tree on the library's own items: `bun research/dag/items.ts <examples/x.ts> [--max 200] [--ms 5000]`.
// Runs the example (its proofs, through kernel/prove.ts) with setProveDump keeping each root goal the prover grows
// (distinct by their hypotheses' text, the first --max), then grows each again, on its own, with tree.ts (kernel/
// prove.ts's search, copied) and with dag.ts's search (learned clauses), --ms each. On the goals both prove: the tree's
// leaves, derivation steps and JSON bytes against the DAG's (its live nodes, leaves, steps, bytes, and the tree it
// unfolds to), every DAG checked by check-dag.ts and every tree by kernel.ts's check. Prints one JSON line.
import {resolve} from 'node:path'
import {setProveDump} from '../../kernel/prove.ts'
import {type Goal, type Tree, check} from '../../kernel/kernel.ts'
import {grow} from './tree.ts'
import {type Dag, dagSearch, sizes} from './dag.ts'
import {checkDag} from './check-dag.ts'

const file = process.argv[2]!
const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const max = Number(arg('--max') ?? 200), ms = Number(arg('--ms') ?? 5000)
const goals: Goal[] = [], seen = new Set<string>()
setProveDump(g => { if (goals.length >= max) return; const key = JSON.stringify(g.hyps); if (key.length > 2_000_000 || seen.has(key)) return; seen.add(key); goals.push(g) })
const log = console.log
console.log = () => {}
const t0 = performance.now()
try { await import(resolve(file)) } catch (e) { log(JSON.stringify({example: file, importError: String(e).slice(0, 200)})) }
console.log = log
setProveDump(undefined)
const runMs = performance.now() - t0
const treeSize = (t: Tree): {leaves: number, steps: number} => ('leaf' in t ? {leaves: 1, steps: t.leaf.length} : (() => { const a = treeSize(t.yes), b = treeSize(t.no); return {leaves: a.leaves + b.leaves, steps: a.steps + b.steps} })())
const rows: {name: string, tree?: {leaves: number, steps: number, bytes: number, ok: boolean}, dag?: ReturnType<typeof sizes> & {ok: boolean}}[] = []
for (const g of goals) {
  const out = grow(g, new Map(), {nodes: 0, until: performance.now() + ms})
  const tree = 'tree' in out ? {...treeSize(out.tree), bytes: JSON.stringify(out.tree).length, ok: check(g, out.tree)} : undefined
  const r = dagSearch(g, {until: performance.now() + ms})
  const root = 'clause' in r.out && r.out.clause.lits.size === 0 ? r.out.clause.node : undefined
  const dag: Dag | undefined = root !== undefined ? {goal: g.name, nodes: r.nodes, root} : undefined
  rows.push({name: g.name, ...(tree ? {tree} : {}), ...(dag ? {dag: {...sizes(dag), ok: checkDag(g, dag).ok}} : {})})
}
const both = rows.filter(x => x.tree && x.dag)
const sum = (f: (x: typeof rows[number]) => number) => both.reduce((s, x) => s + f(x), 0)
log(JSON.stringify({example: file, runMs: Math.round(runMs), goals: goals.length, treeProven: rows.filter(x => x.tree).length, treeChecked: rows.filter(x => x.tree?.ok).length,
  dagProven: rows.filter(x => x.dag).length, dagChecked: rows.filter(x => x.dag?.ok).length, both: both.length,
  tree: {leaves: sum(x => x.tree!.leaves), steps: sum(x => x.tree!.steps), bytes: sum(x => x.tree!.bytes)},
  dag: {nodes: sum(x => x.dag!.nodes), leaves: sum(x => x.dag!.leaves), steps: sum(x => x.dag!.steps), bytes: sum(x => x.dag!.bytes), unfoldedLeaves: sum(x => x.dag!.unfoldedLeaves)},
  dagSmallerSteps: both.filter(x => x.dag!.steps < x.tree!.steps).length, dagLargerSteps: both.filter(x => x.dag!.steps > x.tree!.steps).length,
  multiLeaf: both.filter(x => x.tree!.leaves > 1).length}))
process.exit(0)
