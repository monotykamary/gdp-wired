// compare/chc/prof/given.ts with the step goal kept: `bun research/dag/given-dump.ts <task.smt2> <models.json> --out <dir>
// [--key <smt2 path in models.json>] [--ms 55000] [--abort <goal name>]`. The same laws from Spacer's model, the same
// proveRule (no search) under the same deadline; every root goal the prover grows is seen through kernel/prove.ts's
// setProveDump, and the last one (the goal it stopped on, when it stops) is written as <dir>/goal.json (goalio.ts's
// hash-consed form) and <dir>/goal.smt2. With --abort, the run stops at the first root goal of that name (a smoke test:
// no prover time). Prints one JSON line, given.ts's, with the goals seen.
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {Unsupported, parseChc, parseSx, type Sx} from '../../compare/chc/chc.ts'
import {build} from '../../compare/chc/translate.ts'
import {type Choice, Cond, Int, all, any, choose, no, proveRule, when, yes} from '../../core/dsl.ts'
import type {Law} from '../../core/machine.ts'
import {setProveDump, withDeadline} from '../../kernel/prove.ts'
import type {Goal} from '../../kernel/kernel.ts'
import {dumpGoal, toSmt} from './goalio.ts'

const [file, modelsFile] = process.argv.slice(2) as [string, string]
const msArg = process.argv.indexOf('--ms'), ms = msArg < 0 ? 55000 : Number(process.argv[msArg + 1])
const t0 = performance.now()
const say = (o: object) => { console.log(JSON.stringify({stage: 'answer', answer: 'given', ms: Math.round(performance.now() - t0), ...o})); process.exit(0) }
const models = JSON.parse(readFileSync(modelsFile, 'utf8')) as Record<string, string>
const arg = (f: string) => { const i = process.argv.indexOf(f); return i < 0 ? undefined : process.argv[i + 1] }
const outDir = arg('--out')!, abortAt = arg('--abort')
const text = models[arg('--key') ?? file.replace(/^\/bench\//, '')]
if (!text) say({why: 'no model'})
const chc = parseChc(readFileSync(file, 'utf8')), b = build(chc), r = b.rule
const sx = parseSx(text!)
const defs = (sx.find(x => Array.isArray(x) && x.some(d => Array.isArray(d) && d[0] === 'define-fun')) as Sx[] | undefined ?? []).filter((d): d is Sx[] => Array.isArray(d) && d[0] === 'define-fun')

type V = Int | Cond
const asInt = (v: V): Int => { if (v instanceof Int) return v; throw new Unsupported('an Int expected') }
const asCond = (v: V): Cond => { if (v instanceof Cond) return v; throw new Unsupported('a Bool expected') }
const tr = (s: Sx, scope: Map<string, V>): V => {
  if (typeof s === 'string') {
    if (s === 'true') return yes
    if (s === 'false') return no
    if (/^\d+$/.test(s)) { const v = Number(s); if (!Number.isSafeInteger(v)) throw new Unsupported(`the numeral ${s}`); return Int.of(v) }
    const v = scope.get(s)
    if (!v) throw new Unsupported(`an unbound symbol ${s}`)
    return v
  }
  const [op, ...xs] = s as [string, ...Sx[]]
  if (op === '!') return tr(xs[0]!, scope)
  if (op === 'let') {
    const inner = new Map(scope)
    for (const bd of xs[0] as Sx[][]) inner.set(bd[0] as string, tr(bd[1]!, scope))
    return tr(xs[1]!, inner)
  }
  const I = (k: number) => asInt(tr(xs[k]!, scope)), B = (k: number) => asCond(tr(xs[k]!, scope))
  const pairs = (f: (a: Int, c: Int) => Cond) => all(...xs.slice(1).map((_, k) => f(I(k), I(k + 1))))
  switch (op) {
    case '+': return xs.slice(1).reduce<Int>((a, _, k) => a.plus(I(k + 1)), I(0))
    case '-': return xs.length === 1 ? I(0).negate() : xs.slice(1).reduce<Int>((a, _, k) => a.minus(I(k + 1)), I(0))
    case '*': {
      // A constant factor is a numeral or (- numeral), as Spacer writes them.
      const num = (x: Sx) => Number(typeof x === 'string' ? x : x[0] === '-' && x.length === 2 && typeof x[1] === 'string' ? `-${x[1]}` : NaN)
      const vs = xs.map(x => tr(x, scope)), ks = xs.map(x => (Number.isSafeInteger(num(x)) ? num(x) : undefined))
      const k = ks.reduce<number>((a, c) => a * (c ?? 1), 1), vars = vs.filter((_, j) => ks[j] === undefined)
      if (vars.length > 1) throw new Unsupported('a product')
      return vars.length ? asInt(vars[0]!).times(k) : Int.of(k)
    }
    case 'mod': case 'div': throw new Unsupported(op)
    case 'exists': case 'forall': throw new Unsupported('a quantifier')
    case '<=': return pairs((a, c) => a.atMost(c))
    case '<': return pairs((a, c) => a.lt(c))
    case '>=': return pairs((a, c) => a.atLeast(c))
    case '>': return pairs((a, c) => a.gt(c))
    case '=': case 'distinct': {
      const vs = xs.map(x => tr(x, scope))
      const eq = (a: V, c: V): Cond => (a instanceof Int ? a.eq(asInt(c)) : choose(a, asCond(c), asCond(c).not()))
      return op === '=' ? all(...vs.slice(1).map(v => eq(vs[0]!, v))) : all(...vs.flatMap((a, k) => vs.slice(k + 1).map(c => eq(a, c).not())))
    }
    case 'and': return all(...xs.map((_, k) => B(k)))
    case 'or': return any(...xs.map((_, k) => B(k)))
    case 'not': return B(0).not()
    case '=>': return any(B(0).not(), B(1))
    case 'xor': return choose(B(0), B(1).not(), B(1))
    case 'ite': { const c = B(0), a = tr(xs[1]!, scope), e = tr(xs[2]!, scope); return a instanceof Int ? when(c, a, asInt(e)) : choose(c, a, asCond(e)) }
    default: throw new Unsupported(`the operator ${op}`)
  }
}
// The top-level conjuncts, through lets (letsAround puts each back under its lets).
const conjuncts = (s: Sx, out: Sx[] = []): Sx[] => {
  if (Array.isArray(s) && s[0] === 'let') return conjuncts(s[2]!, out)
  if (Array.isArray(s) && (s[0] === 'and' || s[0] === '!')) { for (const x of s[0] === '!' ? [s[1]!] : s.slice(1)) conjuncts(x, out); return out }
  if (s !== 'true') out.push(s)
  return out
}

const laws: Law[] = [], unstated: string[] = [], leftOut: string[] = []
for (const d of defs) {
  const name = d[1] as string, params = d[2] as Sx[][], body = d[4]!
  const j = b.predNames.indexOf(name)
  if (j < 0) continue
  const loc = b.loc[j]!
  // A predicate of no arguments: Spacer's interpretation is closed (true, false, a formula, or an existential). One a
  // query reads with no constraint (p → false) is false in every model (the system is sat), whatever Spacer wrote.
  if (!params.length) {
    const query = chc.clauses.some(c => !c.head && !c.constraint.length && c.body.length === 1 && c.body[0]!.pred === name)
    const closed = JSON.stringify(body).includes('"exists"') ? undefined : body
    if (body === 'true') continue
    if (body === 'false' || query) { laws.push(r.law(`${name} never`, env => (env.loc as Choice<string>).is(loc).not())); continue }
    if (closed === undefined) { leftOut.push(name); continue }
  }
  let k = 0
  // Each conjunct its own law; one that can't be stated is left out (and counted).
  for (const c of conjuncts(body)) {
    try {
      const law = r.law(`${name} #${k++}`, env => {
        const scope = new Map<string, V>(), n = {Int: 0, Bool: 0}
        for (const [pn, sort] of params as [string, string][]) scope.set(pn, (env as Record<string, V>)[`${sort === 'Int' ? 'i' : 'b'}${n[sort as 'Int' | 'Bool']++}`]!)
        // The conjunct under the lets it sits in, translated over this env's values.
        return (env.loc as Choice<string>).is(loc).implies(asCond(tr(letsAround(body, c), scope)))
      })
      laws.push(law)
    } catch (e) {
      if (e instanceof Unsupported) unstated.push(`${name}: ${e.message}`); else throw e
    }
  }
}
// A conjunct as a formula of its own: the lets it sits under wrapped around it again (their bindings in order).
function letsAround(body: Sx, c: Sx): Sx {
  const path: Sx[][] = []
  const find = (s: Sx): boolean => {
    if (s === c) return true
    if (Array.isArray(s) && s[0] === 'let') { path.push(s[1] as Sx[]); if (find(s[2]!)) return true; path.pop(); return false }
    if (Array.isArray(s) && s[0] === 'and') return s.slice(1).some(find)
    if (Array.isArray(s) && s[0] === '!') return find(s[1]!)
    return false
  }
  find(body)
  return path.reduceRight<Sx>((acc, bs) => ['let', bs, acc], c)
}

const seen: {name: string, hyps: number}[] = []
let last: Goal | undefined
class Abort extends Error {}
setProveDump(g => { seen.push({name: g.name, hyps: g.hyps.length}); last = g; if (abortAt && g.name === abortAt) throw new Abort() })
const t1 = performance.now()
let v: ReturnType<typeof proveRule> | undefined
try { v = withDeadline(performance.now() + ms, () => proveRule(r, [b.law, ...laws], {search: false})) } catch (e) { if (!(e instanceof Abort)) throw e }
const proveMs = Math.round(performance.now() - t1)
mkdirSync(outDir, {recursive: true})
let smtChars = 0
if (last) { writeFileSync(`${outDir}/goal.json`, dumpGoal(last)); const smt = toSmt(last); smtChars = smt.length; writeFileSync(`${outDir}/goal.smt2`, smt) }
say({laws: laws.length, unstated: unstated.length, nullaryLeftOut: leftOut.length, ...(v ? {proven: v.proven, checked: v.checked, ...(v.goal ? {goal: v.goal.slice(0, 160), stuck: v.stuck} : {}), ...(v.why ? {why: v.why.slice(0, 120)} : {})} : {aborted: abortAt}), proveMs,
  rootGoals: seen.length, lastGoal: last ? {name: last.name, hyps: last.hyps.length, sameAsStuck: !!v?.goal && last.name === v.goal} : undefined, smtChars})
