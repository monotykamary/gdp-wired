// Experimental, untrusted row-symmetry proposals. No goal is weakened: all
// input rows are matched exactly after renaming and the result is checked.
import {type CountCert, type CountInst, type Goal, type Path, type Tree, canon, check, leafConstraints} from '../kernel/kernel.ts'
import {late} from '../kernel/prove.ts'
import {countCertificateRenamer} from './count-cert-rename.ts'
import {countRowReindexer} from './count-row-reindex.ts'
import {traceCountStage, type CountStageObserver} from './count-stage-trace.ts'

export function rowSymmetryNames(request: Pick<CountCert, 'reads' | 'insts'>, a: string, b: string, until: number): Map<string, string> | undefined {
  if (a === b || late(until)) return
  const names = new Map([[a, b], [b, a]]), variables = countCertificateRenamer(names, until)
  const add = (before: string, after: string) => {
    if (names.has(before) && names.get(before) !== after) return false
    names.set(before, after); return true
  }
  for (const [id, map, key] of request.reads) {
    const target = JSON.stringify(variables.expression(key)), matches = request.reads.filter(([, m, k]) => m === map && JSON.stringify(k) === target)
    if (matches.length !== 1 || !add(id, matches[0]![0])) return
  }
  const reads = countCertificateRenamer(names, until)
  const signature = (i: CountInst, rename: boolean) => {
    const terms = new Map<string, number>()
    for (const [k, id] of i.terms) {const target = rename ? names.get(id) ?? id : id; terms.set(target, (terms.get(target) ?? 0) + k)}
    return JSON.stringify([i.unit, rename ? reads.expression(i.below) : i.below, [...terms].filter(([, k]) => k !== 0).sort(([a], [b]) => a.localeCompare(b))])
  }
  for (const i of request.insts) {
    const target = signature(i, true), matches = request.insts.filter(other => signature(other, false) === target)
    if (matches.length !== 1 || !add(i.wit, matches[0]!.wit)) return
  }
  for (const [before, after] of names) if (names.get(after) !== before) return
  return names
}

export function rowSymmetryCache(goal: Goal, request: Pick<CountCert, 'reads' | 'insts'>, a: string, b: string, until: number, observe?: CountStageObserver, deferCheck = false) {
  const names = rowSymmetryNames(request, a, b, until)
  if (!names) return
  const rename = countCertificateRenamer(names, until), reindex = countRowReindexer(goal)
  const saved = new Map<string, {path: Path, tree: Tree}>()
  const key = (path: Path) => JSON.stringify([...path.values()].map(({lin, holds}) => [canon(lin), holds]).sort(([a], [b]) => String(a).localeCompare(String(b))))
  const extend = (path: Path, lin: Parameters<typeof rename.row>[0], holds: boolean): Path => new Map([...path, [canon(lin), {lin, holds}]])
  const transport = (source: Tree, before: Path, after: Path): Tree | undefined => {
    if (late(until)) return
    if ('split' in source) {
      const split = rename.row(source.split), yes = transport(source.yes, extend(before, source.split, true), extend(after, split, true))
      if (!yes) return
      const no = transport(source.no, extend(before, source.split, false), extend(after, split, false))
      return no ? {split, yes, no} : undefined
    }
    const old = leafConstraints(goal, before).map(row => ({...row, lin: rename.row(row.lin)})), target = leafConstraints(goal, after), index = reindex(goal, old, target)
    const leaf: typeof source.leaf = [], products: [number, number][] = []
    for (const step of source.leaf) {
      if (step.kind !== 'input') leaf.push({...step})
      else {const next = index(step.index); if (next === undefined) return; leaf.push({...step, index: next})}
    }
    for (const [a, b] of source.products ?? []) {
      const left = index(a), right = index(b)
      if (left === undefined || right === undefined) return
      products.push([left, right])
    }
    return {leaf, ...(source.products ? {products} : {}), ...(source.squares ? {squares: source.squares.map(rename.row)} : {})}
  }
  return {
    // Default get rechecks. Deferred trees are UNCHECKED construction inputs;
    // only the enclosing original-goal check and family gate can accept them.
    put(path: Path, tree: Tree) {if (saved.size >= 32) saved.delete(saved.keys().next().value!); saved.set(key(path), {path: new Map(path), tree})},
    get(path: Path): Tree | undefined {
      if (late(until)) return
      try {
        const swapped: Path = new Map([...path.values()].map(({lin, holds}) => {const row = rename.row(lin); return [canon(row), {lin: row, holds}]})), source = saved.get(key(swapped))
        if (!source) return
        const tree = traceCountStage(observe, 'row-symmetry-transport', 'untrusted-assembly', () => transport(source.tree, source.path, path))
        return tree && (deferCheck || traceCountStage(observe, 'row-symmetry-check', 'trusted-check', () => check(goal, tree, path))) ? tree : undefined
      } catch {return undefined}
    }
  }
}
