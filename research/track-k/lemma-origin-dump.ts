// Research-only portable provenance capture, copied into the read-only replay snapshot.
import {type E} from '../../core/machine.ts'
import {type Lin} from '../../core/solver.ts'
import {type Goal, type Tree, columnTerm} from '../../kernel/kernel.ts'
import {proofOrigin, proofOrigins} from '../../core/lemma-cuts.ts'
proofOrigins.enabled = process.env.LAB_LIVE_CUTS !== '0'
export function lemmaPack(base: {goal: Goal, tree: Tree, path: [string, {lin: Lin, holds: boolean}][], raw: unknown, decls: unknown, cert: unknown}) {
  const origins: {at: string, goal: Goal, tree: Tree, path: [string, {lin: Lin, holds: boolean}][]}[] = []
  const sizes = new WeakMap<Tree, number>()
  const size = (t: Tree): number => { const old = sizes.get(t); if (old !== undefined) return old; const n = 'leaf' in t ? 1 : 1 + size(t.yes) + size(t.no); sizes.set(t, n); return n }
  size(base.tree)
  const visit = (t: Tree, at: string): void => {
    if ('leaf' in t) return
    const no = proofOrigin(t.no), n = sizes.get(t.no)!
    if (no && n >= 3 && n <= 128) origins.push({at: at + 'n', goal: no.goal, tree: no.tree, path: [...no.path]})
    visit(t.yes, at + 'y'); visit(t.no, at + 'n')
  }
  visit(base.tree, '')
  const pack = {...base, origins}
  const columns = Object.fromEntries([...new Set(JSON.stringify(pack).match(/⟦[0-9]+⟧/g) ?? [])].map(c => [c, columnTerm(c) as E]))
  return {...pack, columns}
}
