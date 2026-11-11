// Alpha-renaming proposals for counted certificates. This is not a checker:
// the caller must reindex and check the complete resulting certificate.
import {type C, type E, x} from './machine.ts'
import {type Lin} from './solver.ts'
import {type CountCert, type Tree, canon, cellParts, columnTerm, factorsOf, isCell, substC, substE, termColumn} from '../kernel/kernel.ts'
import {late} from '../kernel/prove.ts'
export function countCertificateRenamer(names: ReadonlyMap<string, string>, until: number) {
  const vars = Object.fromEntries([...names].map(([before, after]) => [before, x(after)])), sub = {vars, maps: {}, flags: {}}
  const alive = () => {if (late(until)) throw Error('count certificate rename deadline')}
  const expression = (e: E): E => {alive(); return substE(e, sub)}
  const condition = (c: C): C => {alive(); return substC(c, sub)}
  const columns = new Map<string, string>()
  const column = (name: string): string => {
    alive()
    const cached = columns.get(name); if (cached !== undefined) return cached
    const factors = factorsOf(name)
    let out: string
    if (factors.length > 1) out = factors.map(column).sort().join('*')
    else if (isCell(name)) {
      const parts = cellParts(name)
      out = parts.keys ? `${parts.map}[⟨${parts.keys.map(key => canon(row(key))).join('|')}⟩]` : `${parts.map}[${canon(row(parts.key!))}]`
    } else if (name.startsWith('⟦')) {
      const term = columnTerm(name)
      if (!term) throw Error('unknown term column')
      out = termColumn(expression(term))
    } else out = names.get(name) ?? name
    columns.set(name, out); return out
  }
  const row = (source: Lin): Lin => {
    alive()
    const out: Lin = Object.create(null)
    for (const [name, coefficient] of Object.entries(source)) {
      const key = name === '1' ? name : column(name), value = (out[key] ?? 0) + coefficient
      if (!Number.isSafeInteger(value)) throw Error('inexact renamed row')
      // Existing zero coefficients are part of the source path identity and
      // hence its proof-row layout. Do not canonicalize them while renaming.
      if (value || coefficient === 0) out[key] = value; else delete out[key]
    }
    return out
  }
  const tree = (source: Tree): Tree => {
    alive()
    return 'split' in source ? {split: row(source.split), yes: tree(source.yes), no: tree(source.no)} : {leaf: source.leaf.map(step => ({...step})), ...(source.products ? {products: source.products.map(([a, b]) => [a, b] as [number, number])} : {}), ...(source.squares ? {squares: source.squares.map(row)} : {})}
  }
  const name = (id: string) => names.get(id) ?? id
  const certificate = (source: CountCert): CountCert => ({
    reads: source.reads.map(([id, map, key]) => [name(id), map, expression(key)]),
    insts: source.insts.map(i => ({...i, wit: name(i.wit), below: expression(i.below), terms: i.terms.map(([k, id]) => [k, name(id)])})),
    tree: tree(source.tree),
    ...(source.picks ? {picks: source.picks.map(([id, keys]) => [name(id), keys.map(expression)] as [string, E[]])} : {}),
    ...(source.frames ? {frames: source.frames.map(f => ({post: name(f.post), pre: name(f.pre), when: f.when.map(row)}))} : {}),
    ...(source.monos ? {monos: source.monos.map(m => ({...m, post: name(m.post), pre: name(m.pre), when: m.when.map(condition), tree: tree(m.tree)}))} : {}),
    ...(source.lins ? {lins: source.lins.map(l => ({when: l.when.map(condition), pos: l.pos.map(([k, id]) => [k, name(id)]), neg: l.neg.map(([k, id]) => [k, name(id)]), tree: tree(l.tree)}))} : {}),
    ...(source.lemmas ? {lemmas: source.lemmas.map(l => ({...l, when: l.when.map(row), cut: row(l.cut), tree: tree(l.tree)}))} : {})
  })
  return {expression, condition, row, tree, certificate}
}
