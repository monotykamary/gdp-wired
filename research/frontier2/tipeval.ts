// TIP's own evaluator (compare/tip/tip.ts, no gdp-wired code) on a problem's goal at random values of its variables:
// `bun research/frontier2/tipeval.ts <problem.smt2> [--n 3000] [--seed 1]`. The goal's sort variables are taken at the
// naturals (as the translation takes them), an Int in [−200, 300] (a quarter of them in [90, 110]), a datatype value drawn constructor by constructor
// within a size of 0 to 7. Prints one JSON line: how many samples held, the first that doesn't (a counterexample: the
// goal is false there), and how many ran out of the evaluator's fuel.
import {readFileSync} from 'node:fs'
import {OutOfFuel, type Sx, type Ty, type V, evaluate, parseTip, prenex, showV, substTy, tyOf} from '../../compare/tip/tip.ts'

const args = process.argv.slice(2), file = args[0]!
const opt = (k: string, d: number) => { const i = args.indexOf(k); return i < 0 ? d : Number(args[i + 1]) }
const n = opt('--n', 3000)
let seed = opt('--seed', 1)
const rand = (k: number) => { seed = (seed * 1103515245 + 12345) % 2 ** 31; return Math.floor(seed / 2 ** 31 * k) }
const tip = parseTip(readFileSync(file, 'utf8'))
const {vars, body} = prenex(tip.goal.body)
const tvars = new Set(tip.goal.params)

const NAT: Ty = {k: 'con', name: '$Nat', args: []}
function value(ty: Ty, size: number): V {
  if (ty.k === 'var' || (ty.k === 'con' && ty.name === '$Nat')) return BigInt(rand(size + 3))
  if (ty.k === 'fun') throw new Error('a function variable')
  if (ty.name === 'Int') return BigInt(rand(4) === 0 ? 90 + rand(21) : rand(501) - 200)
  if (ty.name === 'Bool') return rand(2) === 1
  const d = tip.datas.get(ty.name)
  if (!d) throw new Error(`no datatype ${ty.name}`)
  const m = new Map(d.params.map((p, i) => [p, ty.args[i]!]))
  const rec = (c: (typeof d.ctors)[number]) => c.fields.some(f => f.ty.k === 'con' && f.ty.name === d.name)
  const base = d.ctors.filter(c => !rec(c)), pick = size <= 0 && base.length ? base : d.ctors
  const c = pick[rand(pick.length)]!
  const parts = c.fields.length ? Math.max(0, size - 1) : 0
  return {c: c.name, a: c.fields.map(f => value(substTy(f.ty, m), rand(parts + 1)))}
}
const tys = vars.map(v => { const t = tyOf(v.ty, tvars); return t.k === 'var' ? NAT : t })
let held = 0, fuel = 0, drawn = 0, broken: Record<string, string> | undefined
for (let i = 0; i < n && !broken; i++) {
  drawn++
  const env = new Map<string, V>(vars.map((v, j) => [v.name, value(tys[j]!, rand(8))]))
  let ok: V
  try { ok = evaluate(tip, body as Sx, env) } catch (e) { if (e instanceof OutOfFuel || e instanceof RangeError) { fuel++; continue } throw e }
  if (ok === true) held++
  else broken = Object.fromEntries([...env].map(([k, v]) => [k, showV(v)]))
}
console.log(JSON.stringify({file, drawn, held, outOfFuel: fuel, ...(broken ? {counterexample: broken} : {})}))
