// Untrusted finite-state proposals from the laws' own syntax. No proposal is
// evidence: finiteHoudini still checks the entire family and the actual step.
import {type C, type E, type Law, type Machine, type State, carriedView, compileC, evalE} from './machine.ts'
import {checkWall, WallExpired} from './wall.ts'
type Env = Record<string, number>
const flatten = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(flatten) : [c]
export function lawFrontiers(law: Law): C[][] {
  const disjuncts = law.holds.op === 'or' ? law.holds.xs : [law.holds]
  const guards = disjuncts.flatMap(c => c.op === 'not' ? [c.x] : [])
  const out: C[][] = guards.length ? [guards.flatMap(flatten)] : []
  for (const guard of guards) {
    const atoms = flatten(guard), others = guards.filter(c => c !== guard).flatMap(flatten)
    if (atoms.length === 2) for (let i = 0; i < 2; i++) out.push([...others, atoms[i]!, {op: 'not', x: atoms[1 - i]!}])
  }
  for (const c of disjuncts) for (const atom of flatten(c)) if (atom.op === '<=') out.push([...guards.flatMap(flatten), {op: '=', a: atom.a, b: atom.b}])
  return [...new Map(out.map(xs => [JSON.stringify(xs), xs])).values()]
}
export function boundaryState(source: Machine, m: Machine, conditions: C[], p: Env, old: State, keys: Env): State | undefined {
  if (source.history || source.leasts) return undefined
  const st: State = {...old, scalars: {...old.scalars}, maps: {...old.maps}}, env = {...p, ...st.scalars, ...keys}
  let cached: State | undefined
  const view = () => cached ??= carriedView(m, st, Object.fromEntries((m.inputMaps ?? []).map(k => [k, new Map()])), undefined, p)
  const value = (e: E) => evalE(e, env, view(), m)
  const natural = (n: number) => Number.isSafeInteger(n) && n >= 0
  const write = (e: E, n: number, depth: number): boolean => {
    checkWall('finite boundary write')
    if (!natural(n) || depth > 16) return false
    if (value(e) === n) return true
    if (e.op === 'var' && e.name in source.state && !(e.name in keys)) { st.scalars[e.name] = env[e.name] = n; cached = undefined; return true }
    if (e.op === 'get') {
      const key = value(e.key)
      if (!natural(key)) return false
      if (e.map in (source.maps ?? {})) { st.maps[e.map] = new Map(st.maps[e.map]); st.maps[e.map]!.set(key, n); cached = undefined; return true }
      const count = m.counts?.[e.map]
      if (!count) return false
      const prior = {...env}
      env[count.j] = count.base ? Math.floor(key / count.base) : key
      if (count.lo && count.base) env[count.lo] = key % count.base
      const bound = value(count.below)
      if (!natural(bound) || bound > 64 || n > bound) { Object.assign(env, prior); return false }
      let ok = true
      for (let i = 0; i < bound && ok; i++) { env[count.key] = i; ok = write(count.body, Number(i < n), depth + 1) }
      for (const k of Object.keys(env)) if (!(k in prior)) delete env[k]
      Object.assign(env, prior, st.scalars)
      return ok
    }
    if (e.op === 'if') {
      if (e.then.op === 'const' && e.then.value === n) return force(e.c, true, depth + 1)
      if (e.else.op === 'const' && e.else.value === n) return force(e.c, false, depth + 1)
    }
    if (e.op === 'add') return write(e.a, n - value(e.b), depth + 1) || write(e.b, n - value(e.a), depth + 1)
    if (e.op === 'sub') return write(e.a, n + value(e.b), depth + 1)
    if (e.op === 'mul' && e.k > 0 && n % e.k === 0) return write(e.a, n / e.k, depth + 1)
    return false
  }
  const force = (c: C, wanted: boolean, depth = 0): boolean => {
    if (depth > 16) return false
    if (compileC(c, m)(env, view()) === wanted) return true
    if (c.op === 'not') return force(c.x, !wanted, depth + 1)
    if (c.op === 'and') return wanted ? c.xs.every(x => force(x, true, depth + 1)) : c.xs.some(x => force(x, false, depth + 1))
    if (c.op === 'or') return wanted ? c.xs.some(x => force(x, true, depth + 1)) : c.xs.every(x => force(x, false, depth + 1))
    if (c.op === 'flag' || c.op === 'all') return false
    const a = value(c.a), b = value(c.b)
    if (c.op === '=') return wanted ? write(c.a, b, depth + 1) || write(c.b, a, depth + 1) : write(c.a, b + 1, depth + 1) || write(c.b, a + 1, depth + 1)
    if (c.op === '<=') return wanted ? write(c.a, b, depth + 1) || write(c.b, a, depth + 1) : write(c.a, b + 1, depth + 1) || write(c.b, a - 1, depth + 1)
    return wanted ? write(c.a, b - 1, depth + 1) || write(c.b, a + 1, depth + 1) : write(c.a, b, depth + 1) || write(c.b, a, depth + 1)
  }
  try {
    return conditions.every(c => force(c, true)) && conditions.every(c => compileC(c, m)(env, view())) ? st : undefined
  } catch (error) { if (error instanceof WallExpired) throw error; return undefined }
}
