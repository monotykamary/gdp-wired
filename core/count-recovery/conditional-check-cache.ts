// Untrusted pre-check accelerators over immutable proof objects. No cached
// answer replaces checkMC/checkCountedLaws on the final emitted certificate.
import {type Goal, type LemmaCut, type Path, type Tree, canon, check, leafConstraintsReusing as rowsAt} from '../../kernel/kernel.ts'

const stats = {leafChecks: 0, leafHits: 0, leafFallbacks: 0, fullHyps: 0, sliceHyps: 0, independentChecks: 0, independentHits: 0, retargetChecks: 0, retargetHits: 0}
export const conditionalProofStats = (): Readonly<typeof stats> => ({...stats})
const pathKey = (path: Path): string => JSON.stringify([...path].map(([key, a]) => [key, a.holds, canon(a.lin)]))
const leaves = new WeakMap<Goal, WeakMap<Tree, Map<string, boolean>>>()

/** Keep exactly the hypotheses cited by base/product inputs, then relocate all
 * inputs including square/product offsets. The unchanged kernel checks the
 * sliced literal certificate; malformed and unused products are not dropped. */
export function slicedCheck(goal: Goal, tree: Tree, path: Path): boolean {
  if (!('leaf' in tree)) return check(goal, tree, path)
  let trees = leaves.get(goal)
  if (!trees) leaves.set(goal, trees = new WeakMap())
  let paths = trees.get(tree)
  if (!paths) trees.set(tree, paths = new Map())
  const key = pathKey(path), old = paths.get(key)
  if (old !== undefined) { stats.leafHits++; return old }
  stats.leafChecks++; stats.fullHyps += goal.hyps.length
  let ok = false
  try {
    const rows = rowsAt(goal, path), needed = new Set<number>(), visited = new Set<number>(), squares = tree.squares?.length ?? 0
    const mark = (i: number): void => {
      if (!Number.isSafeInteger(i) || i < 0) throw new Error('invalid input')
      if (visited.has(i)) return
      visited.add(i)
      if (i < rows.length) { const src = rows[i]!.src; if (src && 'fact' in src) needed.add(src.fact) }
      else if (i >= rows.length + squares) {
        const product = tree.products?.[i - rows.length - squares]
        if (!product) throw new Error('invalid product')
        mark(product[0]); mark(product[1])
      }
    }
    for (const step of tree.leaf) if (step.kind === 'input') mark(step.index)
    for (const [a, b] of tree.products ?? []) { mark(a); mark(b) }
    const small = {...goal, hyps: [...needed].sort((a, b) => a - b).map(i => goal.hyps[i]!)}, target = rowsAt(small, path), at = new Map<string, number>()
    stats.sliceHyps += small.hyps.length
    target.forEach((row, i) => { const id = canon(row.lin); if (!at.has(id)) at.set(id, i) })
    const index = (i: number): number => {
      if (i >= rows.length) return i - rows.length + target.length
      const moved = at.get(canon(rows[i]!.lin))
      if (moved === undefined) throw new Error('missing row')
      return moved
    }
    const moved: Tree = {...tree, leaf: tree.leaf.map(s => s.kind === 'input' ? {...s, index: index(s.index)} : s), ...(tree.products ? {products: tree.products.map(([a, b]) => [index(a), index(b)] as [number, number])} : {})}
    ok = check(small, moved, path)
  } catch { ok = false }
  // Slicing is an optimization, never a new rejection rule. In particular a
  // naturality row may be supported by a hypothesis not otherwise cited.
  if (!ok) { stats.leafFallbacks++; ok = check(goal, tree, path) }
  paths.set(key, ok)
  return ok
}

const independent = new WeakMap<Goal, WeakSet<LemmaCut>>()
export function independentHit(goal: Goal, lemma: LemmaCut): boolean {
  stats.independentChecks++
  if (!independent.get(goal)?.has(lemma)) return false
  stats.independentHits++
  return true
}
export function rememberIndependent(goal: Goal, lemma: LemmaCut): void {
  let set = independent.get(goal)
  if (!set) independent.set(goal, set = new WeakSet())
  set.add(lemma)
}

// The key includes target slice and matched hypothesis text, never target goal
// identity or unrelated scope atoms. Only fully mapped transports use this map.
const retargets = new WeakMap<LemmaCut, Map<string, LemmaCut>>()
export function retargetHit(lemma: LemmaCut, key: string): LemmaCut | undefined {
  stats.retargetChecks++
  const old = retargets.get(lemma)?.get(key)
  if (old) stats.retargetHits++
  return old
}
export function rememberRetarget(lemma: LemmaCut, key: string, result: LemmaCut): void {
  let map = retargets.get(lemma)
  if (!map) retargets.set(lemma, map = new Map())
  map.set(key, result)
}
const indices = new WeakMap<Goal, Map<string, number>>()
export function targetIndex(goal: Goal, until: number): Map<string, number> | undefined {
  if (!(performance.now() < until)) return undefined
  let at = indices.get(goal)
  if (!at) {
    at = new Map()
    for (const [i, h] of goal.hyps.entries()) {
      if (!(performance.now() < until)) return undefined
      const key = JSON.stringify(h)
      if (!at.has(key)) at.set(key, i)
    }
    indices.set(goal, at)
  }
  return at
}
