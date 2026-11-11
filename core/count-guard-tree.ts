// Exhaustive ordinary scalar splits. Unsupported syntax only declines a hint.
import {type C, walkOnce} from './machine.ts'
import {type Lin, add, k, scale, sub} from './solver.ts'
import {type Path, type Tree, canon, linear, truth} from '../kernel/kernel.ts'
import {clock, pastWall} from '../kernel/prove.ts'
type Branch = (path: Path) => Tree | undefined
export type HoistRow = {row: Lin, reject: Branch, name?: string}
// Only exact two-sided equalities identify variables. Opaque linear columns
// remain opaque; a missed alias merely leaves a row at its original position.
function rowAliases(path: Path): (name: string) => string {
  const parent = new Map<string, string>()
  const root = (name: string): string => {const next = parent.get(name); return next === undefined ? name : root(next)}
  for (const atom of path.values()) {
    if (!atom.holds || (atom.lin['1'] ?? 0) !== 0) continue
    const keys = Object.keys(atom.lin).filter(name => name !== '1' && atom.lin[name] !== 0)
    if (keys.length !== 2 || atom.lin[keys[0]!] !== 1 || atom.lin[keys[1]!] !== -1 || path.get(canon(scale(atom.lin, -1)))?.holds !== true) continue
    const a = root(keys[0]!), b = root(keys[1]!)
    if (a !== b) parent.set(a < b ? b : a, a < b ? a : b)
  }
  return root
}
export function countGuardTree(until: number) {
  const rows = (conditions: Lin[], path: Path, yes: Branch, no: Branch): Tree | undefined => {
    if (clock() >= until || pastWall()) return
    if (!conditions.length) return yes(path)
    const [row, ...rest] = conditions, id = canon(row!), known = Object.keys(row!).every(k => k === '1') ? (row!['1'] ?? 0) <= 0 : path.get(id)?.holds
    if (known !== undefined) return known ? rows(rest, path, yes, no) : no(path)
    const rejected = no(new Map(path).set(id, {lin: row!, holds: false}))
    if (!rejected) return
    const accepted = rows(rest, new Map(path).set(id, {lin: row!, holds: true}), yes, no)
    return accepted ? {split: row!, yes: accepted, no: rejected} : undefined
  }
  const condition = (c: C, path: Path, yes: Branch, no: Branch): Tree | undefined => {
    if (clock() >= until || pastWall()) return
    let unsupported = false
    walkOnce(c, (node: any) => {if (node.op === 'flag' || node.op === 'all') unsupported = true})
    if (unsupported) return
    const known = truth(c, path)
    if (known !== undefined) return known ? yes(path) : no(path)
    if (c.op === 'not') return condition(c.x, path, no, yes)
    if (c.op === 'and' || c.op === 'or') {
      const [head, ...tail] = c.xs
      if (!head) return c.op === 'and' ? yes(path) : no(path)
      const rest: C = {op: c.op, xs: tail}
      return c.op === 'and' ? condition(head, path, p => condition(rest, p, yes, no), no) : condition(head, path, yes, p => condition(rest, p, yes, no))
    }
    if (c.op !== '<' && c.op !== '<=' && c.op !== '=') return
    const a = linear(c.a, path), b = linear(c.b, path)
    if (!a || !b) return
    const d = sub(a, b)
    return rows(c.op === '=' ? [d, scale(d, -1)] : [c.op === '<' ? add(d, k(1)) : d], path, yes, no)
  }
  const hoist = (queries: readonly HoistRow[], cases: readonly C[], path: Path, yes: Branch, trace?: (event: Record<string, unknown>) => void): Tree | undefined => {
    if (clock() >= until || pastWall()) return
    const alias = rowAliases(path), variables = (row: Lin) => new Set(Object.keys(row).filter(name => name !== '1' && row[name] !== 0).map(alias)), caseVariables = new Set<string>()
    let supported = true
    for (const c of cases) walkOnce(c, (node: any) => {
      if (node.op === 'flag' || node.op === 'all') supported = false
      if (!['=', '<', '<='].includes(node.op)) return
      const a = linear(node.a, path), b = linear(node.b, path)
      if (!a || !b) {supported = false; return}
      for (const name of variables(sub(a, b))) caseVariables.add(name)
    })
    let at = path
    const cuts: {row: Lin, no: Tree}[] = [], wrap = (tree: Tree): Tree => {for (const cut of [...cuts].reverse()) tree = {split: cut.row, yes: tree, no: cut.no}; return tree}
    for (const query of queries) {
      if (clock() >= until || pastWall()) return
      const vars = variables(query.row), independent = supported && [...vars].every(name => !caseVariables.has(name)), id = canon(query.row)
      trace?.({kind: 'hoist-row', name: query.name, row: query.row, variables: [...vars].sort(), caseVariables: [...caseVariables].sort(), independent})
      if (!independent || at.get(id)?.holds === true) continue
      if (at.get(id)?.holds === false) {const tree = query.reject(at); if (tree) return wrap(tree); continue}
      // Failure to close the complement is not permission to assume the row.
      // Leave it for the original, more-specific branch instead.
      const no = query.reject(new Map(at).set(id, {lin: query.row, holds: false}))
      if (!no) {trace?.({kind: 'hoist-row', name: query.name, outcome: 'deferred'}); continue}
      cuts.push({row: query.row, no}); at = new Map(at).set(id, {lin: query.row, holds: true})
      trace?.({kind: 'hoist-row', name: query.name, outcome: 'hoisted'})
    }
    const tree = yes(at)
    return tree ? wrap(tree) : undefined
  }
  return {rows, condition, hoist}
}
