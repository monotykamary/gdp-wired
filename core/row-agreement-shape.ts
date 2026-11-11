// A proposal selector only. Matching syntax proves no invariant and adds no premise.
import {type C, type E, type Law, type Machine, walkOnce} from './machine.ts'
export type RowAgreementShape = {map: string, width: number, left: string, right: string, column: string, fields: string[], markers: {map: string, value: number}[], guard: C}
const atoms = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(atoms) : [c]
const variable = (e: E, name: string) => e.op === 'var' && e.name === name
function packed(e: E, row: string, column: string): number | undefined {
  if (e.op !== 'add') return
  const [a, b] = e.a.op === 'mul' ? [e.a, e.b] : [e.b, e.a]
  if (a.op === 'mul' && variable(a.a, row) && variable(b, column) && Number.isSafeInteger(a.k) && a.k > 0) return a.k
  return
}
export function discoverRowAgreement(m: Machine, law: Law): RowAgreementShape | undefined {
  if (!law.forall || law.keys?.length !== 2 || law.holds.op !== 'or' || law.holds.xs.length !== 2) return
  const [left, right, column] = [law.forall, law.keys[0]!, law.keys[1]!]
  if (new Set([left, right, column]).size !== 3) return
  const negated = law.holds.xs.find(c => c.op === 'not'), conclusion = law.holds.xs.find(c => c.op === '=')
  if (negated?.op !== 'not' || conclusion?.op !== '=' || conclusion.a.op !== 'get' || conclusion.b.op !== 'get') return
  const a = conclusion.a, b = conclusion.b, width = packed(a.key, left, column)
  if (!width || packed(b.key, right, column) !== width || a.map !== b.map || !(a.map in (m.maps ?? {})) || m.counts?.[a.map]) return
  const fields = new Set<string>(), marked = new Map<string, Map<string, number>>()
  for (const c of atoms(negated.x)) {
    if (c.op !== '=') continue
    const [x, y] = c.a.op === 'get' ? [c.a, c.b] : [c.b, c.a]
    if (x.op !== 'get') continue
    if (y.op === 'get' && x.map === y.map && (variable(x.key, left) && variable(y.key, right) || variable(x.key, right) && variable(y.key, left))) fields.add(x.map)
    if (y.op === 'const' && Number.isSafeInteger(y.value) && (variable(x.key, left) || variable(x.key, right))) {
      const byRow = marked.get(x.map) ?? new Map<string, number>(); byRow.set(x.key.op === 'var' ? x.key.name : '', y.value); marked.set(x.map, byRow)
    }
  }
  if (!fields.size || [...fields].some(f => m.counts?.[f] || !(f in (m.maps ?? {})))) return
  const markers = [...marked].flatMap(([map, rows]) => rows.has(left) && rows.get(left) === rows.get(right) ? [{map, value: rows.get(left)!}] : [])
  let supported = true
  walkOnce(negated.x, (node: any) => {if (node.op === 'get' && !fields.has(node.map) && !markers.some(marker => marker.map === node.map)) supported = false})
  if (!supported) return
  // A versioned row's fields move with a row copy. This deliberately excludes
  // lookalike pairs containing a field updated only by an unrelated action.
  const rowFlags = new Set<string>()
  walkOnce(m.step.maps?.[a.map], (node: any) => {if (node.op === 'flag') rowFlags.add(node.name)})
  let shared = rowFlags
  for (const field of fields) {
    const copied = new Set<string>()
    walkOnce(m.step.maps?.[field], (node: any) => {
      if (node.op !== 'if' || node.then.op !== 'get' || node.then.map !== field || node.then.key.op !== 'var' || !m.inputs.includes(node.then.key.name)) return
      for (const c of atoms(node.c)) if (c.op === 'flag') copied.add(c.name)
    })
    shared = new Set([...shared].filter(flag => copied.has(flag)))
  }
  if (!shared.size) return
  return {map: a.map, width, left, right, column, fields: [...fields].sort(), markers: markers.sort((a, b) => a.map.localeCompare(b.map)), guard: negated.x}
}
