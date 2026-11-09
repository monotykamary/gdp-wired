// Width-two zero/nonzero cubes over fresh lifted one-key counts. These are
// proposals only: the normal reachable filter and checked induction still apply.
import {type E, type Law, type Machine, type State, all, any, atMost, carriedView, compileE, evalE, get, less, n, not, same, walk, x} from './machine.ts'
import {checkWall} from './wall.ts'
type Samples = {p: Record<string, number>, sts: State[]}[]
export function liftedOneKeyCounts(source: Machine, m: Machine): string[] {
  return Object.entries(m.counts ?? {}).filter(([name, d]) => {
    if (name in (source.counts ?? {}) || d.lo || d.body.op !== 'if') return false
    const c = d.body.c
    // A stored row's cardinality is one membership read. Filtered quorum
    // bodies are already separate candidate families, not extra row fields.
    return (c.op === '=' && c.a.op === 'get' && c.b.op === 'const' && c.b.value === 1) || (c.op === '<=' && c.a.op === 'const' && c.a.value === 1 && c.b.op === 'get')
  }).map(([name]) => name)
}
export function countCubes(source: Machine, m: Machine, samples: Samples, only?: Set<string>): Law[] {
  const fresh = liftedOneKeyCounts(source, m).filter(name => !only || only.has(name))
  if (!fresh.length) return []
  const taken = new Set<string>([...m.params, ...m.inputs, ...Object.keys(m.state)])
  walk(m, o => { if (o.op === 'var') taken.add(o.name as string) })
  let key = 'x$countCube'; while (taken.has(key)) key += '$'
  const direct = new Set<string>()
  walk([m.assume, m.step], o => { if (o.op === 'get' && (o.map as string) in (m.maps ?? {}) && (o.key as E).op === 'var') direct.add(o.map as string) })
  const groups = new Map<string, string[]>()
  for (const name of fresh) { const id = JSON.stringify(m.counts![name]!.below); groups.set(id, [...groups.get(id) ?? [], name]) }
  const out: Law[] = []
  for (const names of groups.values()) {
    const below = m.counts![names[0]!]!.below
    const terms = [...Object.keys(m.state).map(name => ({name, term: x(name), lifted: false})), ...[...direct].sort().map(name => ({name: `${name}[x]`, term: get(name, x(key)), lifted: false})), ...names.map(name => ({name: `${name}[x]`, term: get(name, x(key)), lifted: true}))]
    const compiled = terms.map(t => compileE(t.term, m)), rows: boolean[][] = []
    for (const {p, sts} of samples) for (const st of sts) {
      checkWall('count cubes')
      const bound = evalE(below, {...p, ...st.scalars}, st, m)
      const view = carriedView(m, st, Object.fromEntries((m.inputMaps ?? []).map(k => [k, new Map()])), undefined, p)
      for (let k = 0; k < bound; k++) {
        if ((k & 255) === 0) checkWall('count cube rows')
        rows.push(compiled.flatMap(f => { const value = f({...p, ...st.scalars, [key]: k}, view); return [value === 0, value >= 1] }))
      }
    }
    if (!rows.length) continue
    const lits = terms.flatMap((t, i) => [{name: `${t.name} is 0`, c: same(t.term, n(0)), atom: i, lifted: t.lifted}, {name: `1 <= ${t.name}`, c: atMost(n(1), t.term), atom: i, lifted: t.lifted}])
    const seen = lits.map((_, i) => rows.some(r => r[i]))
    const add = (indices: number[]) => out.push({name: `count cubes: every x with x < ${JSON.stringify(below)}: never ${indices.map(i => lits[i]!.name).join(' and ')}`, forall: key, holds: any(not(less(x(key), below)), not(all(...indices.map(i => lits[i]!.c))))})
    for (let i = 0; i < lits.length; i++) {
      checkWall('count cube enumeration')
      if (!seen[i] && lits[i]!.lifted) add([i])
      if (!seen[i]) continue
      for (let j = i + 1; j < lits.length; j++) {
        if (!seen[j] || lits[i]!.atom === lits[j]!.atom || !(lits[i]!.lifted || lits[j]!.lifted)) continue
        if (!rows.some(r => r[i] && r[j])) add([i, j])
      }
    }
  }
  return out
}
