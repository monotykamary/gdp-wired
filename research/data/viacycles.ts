// Experiment: a datatype law through core/cycles.ts's findCycles (facts from core/data.ts, the maps' values on the
// canonical codes Lean's twin defines, and an order fact so a rank linear in the codes exists).
import {laws} from '../../examples/data.ts'
import {type Data, type DataLaw, encY, evalX, factsOf, fieldMap, programOf, sizeMap, tagMap, ctorMap, unkey, type Value} from '../../core/data.ts'
import {findCycles} from '../../core/cycles.ts'
import type {Fact} from '../../kernel/cyclic.ts'
import type {C, E} from '../../core/machine.ts'

const tri = (s: number) => (s * (s + 1)) / 2
const cun = (n: number): [number, number] => { let s = Math.floor((Math.sqrt(8 * n + 1) - 1) / 2); while (tri(s) > n) s--; while (tri(s + 1) <= n) s++; const b = n - tri(s); return [s - b, b] }
const cpair = (a: number, b: number) => tri(a + b) + b
const tup = (q: number, k: number, i: number): number => (k <= 1 ? q : i === 0 ? cun(q)[0] : tup(cun(q)[1], k - 1, i - 1))
const tupk = (xs: number[]): number => (xs.length === 1 ? xs[0]! : cpair(xs[0]!, tupk(xs.slice(1))))
function dec(d: Data, n: number): Value {
  const z = d.nullary, m = d.ctors.length - z
  if (n < z) return {c: n, f: []}
  const q = Math.floor((n - z) / m), j = z + ((n - z) % m), c = d.ctors[j]!
  return {c: j, f: c.fields.map((f, i) => { const x = tup(q, c.fields.length, i); return f.sort === 'nat' ? x : dec(d, x) })}
}
function enc(d: Data, v: Value): number {
  const o = v as {c: number, f: Value[]}, z = d.nullary, m = d.ctors.length - z
  if (o.c < z) return o.c
  const c = d.ctors[o.c]!
  return z + m * tupk(c.fields.map((f, i) => (f.sort === 'nat' ? o.f[i] as number : enc(d, o.f[i]!)))) + (o.c - z)
}
const l = (laws as Record<string, () => DataLaw>)[process.argv[2] ?? 'lengthAppend']!()
const p = programOf([l]), fs = factsOf(p)
const values: Record<string, (...xs: number[]) => number> = {}
const big = (x: number) => { if (!Number.isSafeInteger(x)) throw new Error('big'); return x }
for (const d of p.datas) {
  values[tagMap(d.name)] = n => (dec(d, n) as {c: number}).c
  values[sizeMap(d.name)] = n => { const sz = (v: Value): number => { const o = v as {c: number, f: Value[]}; return 1 + d.ctors[o.c]!.fields.reduce((s, f, i) => s + ((typeof f.sort === 'object' && f.sort.data === d.name) ? sz(o.f[i]!) : 0), 0) }; return sz(dec(d, n)) }
  d.ctors.forEach((c, j) => {
    c.fields.forEach((f, i) => { values[fieldMap(d, j, i)] = n => { const v = dec(d, n) as {c: number, f: Value[]}; return v.c === j ? (f.sort === 'nat' ? v.f[i] as number : enc(d, v.f[i]!)) : 0 } })
    if (c.fields.length) values[ctorMap(d, j)] = (...xs) => big(enc(d, {c: j, f: c.fields.map((f, i) => (f.sort === 'nat' ? xs[i]! : dec(d, xs[i]!)))}))
  })
}
for (const f of p.fns) values[f.name] = (...xs) => { const out = evalX(f.body(), new Map(f.params.map((q, i) => [`${f.name}.${q.name}`, typeof q.sort === 'object' ? dec(q.sort as Data, xs[i]!) : xs[i]!])), {}); return big(typeof f.ret === 'object' ? enc(f.ret as Data, out) : out as number) }
// The order: a field of the datatype has a smaller code (Lean's bijection: z + m·q + r, each field at most q).
const order: Fact[] = p.datas.map(d => ({name: `order ${d.name}`, keys: ['x$'], holds: {op: 'and', xs: d.ctors.flatMap((c, j) => c.fields.flatMap((f, i): C[] => ((typeof f.sort === 'object' && f.sort.data === d.name) ? [{op: 'or', xs: [{op: 'not', x: {op: '=', a: {op: 'get', map: tagMap(d.name), key: {op: 'var', name: 'x$'}} as E, b: {op: 'const', value: j}}}, {op: '<', a: {op: 'get', map: fieldMap(d, j, i), key: {op: 'var', name: 'x$'}}, b: {op: 'var', name: 'x$'}}]}] : [])))}} as Fact))
void unkey
const t = performance.now()
const out = findCycles([...fs.facts, ...order], [{name: l.name, concl: encY(p, l.holds, new Map())}], {values, ms: Number(process.argv[3] ?? 30000)})
console.log(JSON.stringify({law: l.name, proven: out.proven, checked: out.checked, ms: Math.round(performance.now() - t), goal: out.goal, stuck: out.stuck, why: out.why, found: out.found}))
