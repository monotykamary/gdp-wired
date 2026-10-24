// Rules read from the code that ships (`gdp-wired/extract`): `extract(code, {entry})` reads a TypeScript or JavaScript
// step function (a reducer `(state, action) => state`, `useReducer`'s, functions over one record), a class whose
// methods write its fields (a rate limiter's `tryRemove(n)`, a wallet's `debit(x)`), with the classes it extends, or
// the object of functions a factory returns (its state what they close over), and returns the rule that steps the
// same way, as a builder value and as the source that makes it (`toSource`), for a user to read and keep:
//
//   const x = extract(readFileSync('bucket.ts', 'utf8'), {file: 'bucket.ts', entry: 'TokenBucket'})
//   if (!x.ok) console.log(x.refusals)     // where and why
//   proveRule(x.rule, [x.rule.law('within capacity', ({tokens, capacity}) => tokens.atMost(capacity))])
//   writeFileSync('bucket.rule.ts', toSource(x))
//
// The extractor is untrusted. The rule is checked against the original code by running both (core/extract-check.ts):
// requests from the start, steps from drawn states, and steps from the prover's counterexamples, every state, map cell,
// list, result and refusal compared, and the code's branches counted. Any difference refuses the extraction with the
// difference; nothing is adopted that the check didn't run. What the subset doesn't read is refused where it is, with
// the reason, never approximated. XState machines go through `fromXState` (core/xstate.ts), their guards and actions
// read the same way (`extractXState`, a machine or a function that makes one, its actors, timers and eventless
// transitions included).
//
// The subset: numbers (integers: a literal that isn't one is refused; division only as Math.floor or Math.ceil of
// x / k for a constant k, a fraction being a binary float the code rounds; % by a constant of a natural), booleans,
// string-literal unions, strings (set, compared, truthy where not empty), null and undefined where a value may be
// missing, records and nested records (spreads, shorthand), Map and Record state keyed by numbers or strings (get,
// set, has, delete, [k], ?? a default; a Map given to a constructor starts empty), arrays of numbers, booleans and
// string unions as lists (length, [i], push, pop, [i] = x within the array, [...xs], [...xs, x]), Dates as their time
// (new Date(), getTime(), setTime() where the Date is held), conditionals, ternaries, && || ?? (their right side's
// effects on its own path), early returns, switch on a tag (fall-through, default), Math.min, Math.max, Math.abs,
// Boolean(x), Date.now() (an input; once a step), throws (the rule's refusals: its assumption, or its precondition
// for a constructor), helper functions and methods of the same files (inlined), getters, single inheritance (each
// member resolved statically: this.m() the nearest the object has, super.m() the nearest above the class it is in),
// results kept (a value, a record of values, a value that may be missing). Refused: loops, strings beyond keys and
// literals, floats, async, try/catch, writes to the state a reducer is given, a throw after a method wrote a field, two
// keys of one map or two writes of one list in one step, a map or a list replaced whole, a reference into a map held
// across a set, one object (an array, a Map, a Date) in two places, aliasing that depends on the path, mixins, other
// modules' code.
import * as dsl from './dsl.ts'
import {compileFunction} from './machine.ts'
import type {Rule} from './dsl.ts'
import type {Law} from './machine.ts'
import * as I from './extract-ir.ts'
import type {B, N} from './extract-ir.ts'
import {type MapDecl, type Model, Refusal, type Term, type Var} from './extract-read.ts'
import {type ReadOptions, isFactory, isSlice, readClass, readFactory, readFunctions, readSlice} from './extract-shapes.ts'
import {type Ctx, type Printer, type Sorts, kindOf, mapEmpty, mapKind, natOK, pb, pidx, pk, pterm, sortsOf} from './extract-print.ts'
import {type CheckOptions, type Evidence, check} from './extract-check.ts'

export type ExtractOptions = ReadOptions & {
  // The file's name (for locations, and to read it as JavaScript when it ends in .js).
  file?: string,
  // 'class' or 'functions' (a reducer is functions of one); by default, a class if the entry names one.
  shape?: 'class' | 'functions',
  // Numbers given as naturals or integers (by the rule's variable name, or `map.field` for a map's numbers).
  domains?: Record<string, 'nat' | 'int'>,
  // The check's budget (runs, depth, states, probes, seed).
  check?: CheckOptions,
}
export type Extraction = {
  ok: boolean,
  // The rule (when ok), and its source, also printed when the check refused it (to read why).
  rule?: Rule,
  // What every state of the code is in the rule's terms (a map's key the code doesn't hold holds the defaults): the
  // rule has states no object of the code is in, and a law about every state is about the code's with these beside it
  // (proveRule(rule, [...invariants, law])). Each is inductive: proveRule(rule, invariants) proves them.
  invariants?: Law[],
  source?: string,
  model?: Model,
  sorts?: Sorts,
  refusals: {where: string, what: string}[],
  evidence?: Evidence,
  // How the code's values sit in the rule, what each number's sort is and why, what was left out.
  notes: string[],
}

export function extract(code: string, opts: ExtractOptions): Extraction {
  const file = opts.file ?? 'input.ts', notes: string[] = []
  let model: Model
  try {
    const isClass = opts.shape ? opts.shape === 'class' : new RegExp(`\\bclass\\s+${opts.entry}\\b|\\b${opts.entry}\\s*=\\s*class\\b`).test(code)
    // The file sits in the working directory, so its imports (xstate, say) resolve as the project's do.
    const cwd = (globalThis as {process?: {cwd?: () => string}}).process?.cwd?.() ?? '.', at = `${cwd}/${file}`
    model = isClass ? readClass(code, at, opts) : isSlice(code, opts.entry) ? readSlice(code, at, opts) : isFactory(code, file, opts.entry) ? readFactory(code, at, opts) : readFunctions(code, at, opts)
    model.file = file
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  let source: string, body: string, sorts: Sorts
  try {
    const s = sortsOf(model, opts.domains)
    sorts = s.sorts
    datesInRange(model, sorts)
    notes.push(...model.notes, ...s.notes)
    body = builderOf(model, sorts)
    source = moduleOf(model, body, file)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes, model}
    throw e
  }
  let rule: Rule, invariants: Law[]
  try { rule = evaluate(body); invariants = evaluateLaws(rule, invariantsOf(model, sorts)) } catch (e) { return {ok: false, source, model, sorts, refusals: [{where: file, what: `the rule printed doesn't build: ${(e as Error).message}`}], notes} }
  if (invariants.length) source = `${source}\n// What every state of the code is: a law about every state is about the code's with these beside it.\nexport const ${identOf(model)}Invariants = [${invariantsOf(model, sorts).map(x => x.replace(/^r\./, `${identOf(model)}Rule.`)).join(', ')}]\n`
  const evidence = check(code, file, model, rule, sorts, {...opts.check, ...(opts.files ? {files: opts.files} : {}), ...(opts.domains ? {given: opts.domains} : {})})
  if (evidence.mismatch) return {ok: false, source, model, sorts, evidence, refusals: [{where: file, what: `the rule and the code differ: ${evidence.mismatch}`}], notes}
  return {ok: true, rule, ...(invariants.length ? {invariants} : {}), source, model, sorts, evidence, refusals: [], notes}
}
// A Date holds a time within ±8.64e15 ms; past it the code's Date is invalid (NaN). The rule refuses a step that would
// set one there (as it refuses a sum past 2^53), and a start there: its claim stops at the Date's range.
const DATE_MAX = 8_640_000_000_000_000
function datesInRange(m: Model, sorts: Sorts) {
  const out = (e: N, at: string) => (sorts.get(at) === 'nat' ? I.cmp('<', I.num(DATE_MAX), e) : I.or(I.cmp('<', I.num(DATE_MAX), e), I.cmp('<', e, I.num(-DATE_MAX))))
  const dated = m.state.filter(v => v.sort.k === 'num' && v.sort.date)
  const over: B[] = []
  for (const v of dated) { const w = m.writes[v.name]; if (w?.s === 'num') over.push(out(w.e, v.name)) }
  for (const d of m.maps) for (const f of d.fields) if (f.sort.k === 'num' && f.sort.date) { const w = m.mapWrites[d.name]; const t = w?.vals[f.name]; if (t?.s === 'num') over.push(I.and(w!.has, out(t.e, `${d.name}.${f.name}`))) }
  if (over.length) m.refuse = I.or(m.refuse, ...over)
  const starts = dated.filter(v => m.init[v.name]?.s === 'num').map(v => I.not(out((m.init[v.name] as Term & {s: 'num'}).e, v.name)))
  if (starts.length) m.pre = I.and(m.pre, ...starts)
  if (over.length || starts.length) m.notes.push('a Date holds a time within ±8.64e15 ms: a step that would set one past it is refused (the code\'s Date would be invalid)')
}
// The module a user keeps: the rule, with what it was read from and how it was checked.
export const toSource = (x: Extraction): string => x.source ?? ''

// The source is the rule: it is evaluated with the builders, so what is checked is what is printed.
const NAMES = ['rule', 'nat', 'int', 'bool', 'oneOf', 'str', 'record', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'intern', 'Int'] as const
function evaluate(body: string): Rule {
  const f = compileFunction<(...xs: unknown[]) => Rule>([...NAMES], `return ${body}`)
  const r = f(...NAMES.map(n => (dsl as Record<string, unknown>)[n]))
  void r.machine
  return r
}
// A map's representation: each key it doesn't hold holds the defaults (as no object of the code holds a value there).
function invariantsOf(m: Model, sorts: Sorts): string[] {
  const empty = (d: MapDecl, f: Var) => (f.sort.k === 'num' ? `.eq(0)` : f.sort.k === 'bool' ? `.not()` : f.sort.k === 'choice' ? `.is(${JSON.stringify(f.sort.values[0])})` : `.eq('')`)
  void sorts
  return [...m.maps.map(d => `r.law(${JSON.stringify(`${d.name}: a key it doesn't hold holds the defaults`)}, ({${d.name}}) => forall(k => any(${d.name}.at(k).has, all(${d.fields.map(f => `${d.name}.at(k).${f.name}${empty(d, f)}`).join(', ')}))))`),
    ...(m.lists ?? []).map(d => `r.law(${JSON.stringify(`${d.name}: nothing past its end`)}, ({${d.name}}) => ${d.name}.within())`)]
}
function evaluateLaws(r: Rule, xs: string[]): Law[] {
  if (!xs.length) return []
  const f = compileFunction<(...xs: unknown[]) => Law[]>(['r', 'forall', 'any', 'all'], `return [${xs.join(', ')}]`)
  return f(r, dsl.forall, dsl.any, dsl.all)
}
const identOf = (m: Model) => (/^[A-Za-z_$][\w$]*$/.test(m.name) ? m.name.charAt(0).toLowerCase() + m.name.slice(1) : 'extracted')
function moduleOf(m: Model, body: string, file: string): string {
  const used = NAMES.filter(n => new RegExp(`(^|[^.\\w$])${n}\\(|(^|[^.\\w$])${n}\\b(?!\\s*:)`).test(body.replace(/'[^']*'/g, "''")) || (n === 'rule'))
  const ident = identOf(m)
  return [
    `// Extracted by gdp-wired/extract from ${file} (${m.entry}, ${m.factory ? 'a factory of an object of functions' : m.shape === 'class' ? 'a class' : m.shape === 'reducer' ? 'a step function' : 'functions over one record'}).`,
    `// Checked against the code it was read from; read again with extract() after the code changes.`,
    `import {${[...new Set([...used, ...(m.maps.length ? ['all', 'any', 'forall'] : [])])].sort((a, b) => a.localeCompare(b)).join(', ')}} from 'gdp-wired'`,
    '',
    `export const ${ident}Rule = ${body}`,
    '',
  ].join('\n')
}

// --- the builder calls ----------------------------------------------------------------------------------------------
function builderOf(m: Model, sorts: Sorts): string {
  const P: Printer = {sorts, m, hoisted: new Map(), choiceVars: new Map()}
  for (const v of [...m.state, ...m.inputs, ...m.params]) if (v.sort.k === 'choice' && !P.choiceVars.has(v.sort.values.join('\u0000'))) P.choiceVars.set(v.sort.values.join('\u0000'), v.name)
  const ctx = (): Ctx => ({m, sorts, atoms: []})
  const lines = [`rule(${JSON.stringify(m.name)})`]
  const kinds = (vs: Var[]) => vs.map(v => `${v.name}: ${kindOf(v, sorts)}`).join(', ')
  if (m.params.length) lines.push(`  .params({${kinds(m.params)}})`)
  if (m.inputs.length) lines.push(`  .inputs({${kinds(m.inputs)}})`)
  // The state: each variable from its start (a term over the params where the constructor makes it one).
  const params = (t: object) => [...I.varsOf(t as N).vars].filter(n => m.params.some(p => p.name === n))
  const start = (v: Var) => {
    const t = m.init[v.name]!, ps = params(t.e), fn = (x: string) => (ps.length ? `({${ps.join(', ')}}) => ${x}` : x)
    const at = pterm(t, P, ctx(), v.name)
    if (v.sort.k === 'num') return sorts.get(v.name) === 'nat' ? (ps.length ? fn(at) : at) : `int.from(${ps.length ? fn(at) : at})`
    if (v.sort.k === 'bool') return `bool.from(${ps.length ? fn(at) : at === 'yes' ? 'true' : at === 'no' ? 'false' : at})`
    if (v.sort.k === 'str') return `str().from(${ps.length ? fn(at) : at})`
    return `${kindOf(v, sorts)}.from(${ps.length ? fn(at) : at})`
  }
  if (m.state.length) lines.push(`  .state({${m.state.map(v => `${v.name}: ${start(v)}`).join(', ')}})`)
  if (m.maps.length) lines.push(`  .maps({${m.maps.map((d: MapDecl) => `${d.name}: ${mapKind(d, sorts)}.from(${mapEmpty(d)})`).join(', ')}})`)
  if (m.lists?.length) lines.push(`  .items({${m.lists.map(d => `${d.name}: ${kindOf(d.fields[0]!, sorts, `${d.name}.$item`)}`).join(', ')}})`)
  const envOf = (...xs: object[]) => {
    const vars = new Set<string>(), maps = new Set<string>()
    for (const x of xs) I.varsOf(x as N, vars, maps)
    return `{${[...vars, ...maps].join(', ')}}`
  }
  if (!(m.pre.op === 'const' && m.pre.v)) lines.push(`  .pre((${envOf(m.pre)}) => ${pb(m.pre, P, ctx())})`)
  const allowed = I.not(m.refuse)
  if (!(allowed.op === 'const' && allowed.v)) {
    // The choices a printed literal is named by are read in the callback too.
    const text = pb(allowed, P, ctx())
    lines.push(`  .assume((${withChoices(envOf(allowed), text, P)}) => ${text})`)
  }
  // The step: a const for each term written more than once (by the code's own local's name where it has one).
  const outs: [string, string][] = []
  const writes = Object.entries(m.writes), mw = Object.entries(m.mapWrites)
  hoist(m, P, [...writes.map(([, t]) => t.e), ...mw.flatMap(([, w]) => [w.has, ...Object.values(w.vals).map(t => t.e), w.key])])
  const consts = [...P.hoisted.entries()]
  P.hoisted = new Map()
  const defs: string[] = []
  for (const [key, name] of consts) {
    const node = hoistNodes.get(key)!
    defs.push(`const ${name} = ${'rel' in node || isBool(node) ? pb(node as B, P, ctx()) : pterm({s: 'num', e: node as N}, P, ctx())}`)
    P.hoisted.set(key, name)
  }
  for (const [n, t] of writes) outs.push([n, pterm(t, P, ctx(), n)])
  for (const [n, w] of mw) {
    const d = m.maps.find(x => x.name === n)!
    const vals = d.fields.map(f => `${f.name}: ${pterm(w.vals[f.name]!, P, {m, sorts, atoms: [w.has]}, `${n}.${f.name}`)}`)
    outs.push([n, `${n}.set(${pk(w.key, P, ctx())}, {has: ${pb(w.has, P, ctx())}, ${vals.join(', ')}})`])
  }
  // A list's write: its apply over the operations by cases (each under its condition).
  const lw = Object.entries(m.listWrites ?? {})
  for (const [n, ops] of lw) {
    const one = (o: (typeof ops)[number]) => {
      const at = {m, sorts, atoms: [o.when]}, when = pb(o.when, P, ctx())
      return o.op === 'push' ? `${n}.push(${pterm(o.x, P, at, `${n}.$item`)}, ${when})` : o.op === 'pop' ? `${n}.pop(${when})` : `${n}.set(when(${when}, ${pidx(o.i, P, at)}, 0), ${pterm(o.x, P, at, `${n}.$item`)}, ${when})`
    }
    outs.push([`...${n}`, `${n}.apply(${ops.map(one).join(', ')})`])
  }
  const all = [...defs, ...outs.map(([, x]) => x)].join('\n')
  const lterms = lw.flatMap(([, ops]) => ops.flatMap(o => [o.when, ...(o.op === 'pop' ? [] : [o.x.e]), ...(o.op === 'set' ? [o.i] : [])]))
  const env = withChoices(envOf(...writes.map(([, t]) => t.e), ...mw.flatMap(([, w]) => [w.has, w.key, ...Object.values(w.vals).map(t => t.e)]), ...lterms), all, P, [...mw.map(([n]) => n), ...lw.map(([n]) => n)])
  const ret = `{${outs.map(([n, x]) => (n.startsWith('...') ? `...${x}` : `${n}: ${x}`)).join(', ')}}`
  lines.push(defs.length ? `  .step((${env}) => {\n${defs.map(d => `    ${d}`).join('\n')}\n    return ${ret}\n  })` : `  .step((${env}) => (${ret}))`)
  return lines.join('\n')
}
const isBool = (x: object) => ['cmp', 'and', 'or', 'not', 'is', 'leq', 'keq'].includes((x as {op: string}).op) || ((x as {op: string}).op === 'const' && typeof (x as {v: unknown}).v === 'boolean')
// The env's names: those the terms read, the choices a literal is printed through, and the maps written.
function withChoices(env: string, text: string, P: Printer, extra: string[] = []): string {
  const names = new Set(env.slice(1, -1).split(', ').filter(Boolean))
  for (const w of P.choiceVars.values()) if (new RegExp(`\\b${w}\\.of\\(`).test(text)) names.add(w)
  for (const n of P.hoisted.values()) names.delete(n)
  for (const n of extra) names.add(n)
  return `{${[...names].join(', ')}}`
}
// Terms written more than once, hoisted as consts (inner ones first). A number is hoisted only where its printing
// doesn't depend on the branch it is read under (a natural everywhere, or an integer everywhere).
const hoistNodes = new Map<string, object>()
function hoist(m: Model, P: Printer, roots: object[]) {
  const count = new Map<string, number>(), order: string[] = []
  const visit = (x: unknown): void => {
    if (!x || typeof x !== 'object') return
    const o = x as {op?: string}
    if (o.op && !['var', 'const', 'lit', 'svar', 'slit', 'num'].includes(o.op)) {
      const k = I.keyOf(o)
      count.set(k, (count.get(k) ?? 0) + 1)
      if (!hoistNodes.has(k)) hoistNodes.set(k, o)
      if ((count.get(k) ?? 0) > 1) return
      Object.values(o).forEach(visit)
      if (!order.includes(k)) order.push(k)
      return
    }
    if (Array.isArray(x)) x.forEach(visit)
    else Object.values(o).forEach(visit)
  }
  roots.forEach(visit)
  let i = 0
  const names = new Set([...m.params, ...m.inputs, ...m.state].map(v => v.name).concat(m.maps.map(d => d.name)))
  for (const k of order) {
    const node = hoistNodes.get(k)!, size = k.length
    if ((count.get(k) ?? 0) < 2 || size < 60) continue
    if (!isBool(node)) {
      const ctx: Ctx = {m, sorts: P.sorts, atoms: []}, free = natOK(node as N, ctx)
      const cells: string[] = []
      const walk = (x: unknown): void => { if (x && typeof x === 'object') { const o = x as {op?: string, map?: string, field?: string}; if (o.op === 'cell') cells.push(`${o.map}.${o.field}`); Object.values(o).forEach(walk) } }
      walk(node)
      const hasInt = [...I.varsOf(node as N).vars].some(n => P.sorts.get(n) === 'int') || cells.some(c => P.sorts.get(c) === 'int')
      if (!free && !hasInt) continue
    }
    let name = m.hints.get(node) ?? `t${++i}`
    while (names.has(name)) name = `${name}_`
    names.add(name)
    P.hoisted.set(k, name)
  }
}
export type {Evidence, Model, Term}
export {Refusal}
export {extractXState, type XStateExtraction, type XStateOptions} from './extract-xstate.ts'
