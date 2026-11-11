// Reindex a plain proof into a counted tree whose conditional cuts become
// active at different descendant paths. Root-only rebasing is insufficient:
// a newly active cut changes the leaf's input-row numbers.
import {type Goal, type Path, type Tree, canon, check} from '../../kernel/kernel.ts'
import {late} from '../../kernel/prove.ts'
import {rebasePath} from './rebase-path.ts'
export function reframeCountTree(goal: Goal, tree: Tree, from: Path, to: Path, frame: (path: Path) => Path, until: number): Tree | undefined {
  const visit = (node: Tree, source: Path, target: Path): Tree | undefined => {
    if (late(until)) return
    if ('leaf' in node) {
      const at = frame(target), leaf = rebasePath(goal, node, source, at, until)
      return leaf && check(goal, leaf, at) ? leaf : undefined
    }
    const id = canon(node.split)
    if (target.has(id) || Object.keys(node.split).every(name => name === '1')) return
    const next = (path: Path, holds: boolean) => new Map(path).set(id, {lin: node.split, holds})
    const yes = visit(node.yes, next(source, true), next(target, true))
    const no = yes && visit(node.no, next(source, false), next(target, false))
    return yes && no ? {split: node.split, yes, no} : undefined
  }
  return visit(tree, from, to)
}
