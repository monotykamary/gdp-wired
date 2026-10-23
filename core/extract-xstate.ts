// XState machines read from the code (core/extract.ts's `extractXState`): the machine as XState builds it (the file
// loaded in the check's VM, with the real xstate), its states and transitions read by `fromXState` (core/xstate.ts), and
// each guard and action `setup({guards, actions})` names read from its source by the extractor's executor, printed as
// the bridge fromXState takes: a guard as its condition, an `assign` as the context it writes. The chart is then run
// beside XState's own actor (`conforms`) on random events with payloads, every state and context compared, the code's
// branches counted; any difference refuses it. Refused besides what fromXState refuses: v4 `cond` (the machines read are
// v5's, and XState v5 ignores a `cond`, taking the transition unguarded), a machine made by a function, guards and actions with params, actions that
// raise, send or spawn.
import ts from 'typescript'
import * as dsl from './dsl.ts'
import {compileFunction, seeded} from './machine.ts'
import * as I from './extract-ir.ts'
import type {B} from './extract-ir.ts'
import {Exec, type Model, type Path, Refusal, type Setup, type Term, type V, type Var, program} from './extract-read.ts'
import {type Printer, kindOf, pb, pterm, sortsOf} from './extract-print.ts'
import {type Coverage, sandbox} from './extract-check.ts'
import {conforms, fromXState} from './xstate.ts'

export type XStateOptions = {file?: string, entry: string, xstate: {createActor: (m: never) => {start: () => unknown}} & Record<string, unknown>, check?: {runs?: number, depth?: number, seed?: number}}
export type XStateExtraction = {
  ok: boolean, source?: string, chart?: ReturnType<typeof fromXState>, refusals: {where: string, what: string}[], notes: string[],
  evidence?: {runs: number, events: number, coverage: Coverage, ms: number, mismatch?: string},
}
const where = (n: ts.Node) => { const sf = n.getSourceFile(), {line, character} = sf.getLineAndCharacterOfPosition(n.getStart()); return `${sf.fileName.split('/').pop()}:${line + 1}:${character + 1}` }
const refuse = (n: ts.Node, what: string): never => { throw new Refusal(where(n), what) }
const strip = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) ? strip(e.expression) : e)

export function extractXState(code: string, opts: XStateOptions): XStateExtraction {
  const file = opts.file ?? 'machine.ts', t0 = performance.now(), notes: string[] = []
  try {
    const cwd = (globalThis as {process?: {cwd?: () => string}}).process?.cwd?.() ?? '.'
    const {sf, checker} = program(code, `${cwd}/${file}`)
    // The machine's expression: setup({...}).createMachine({...}) or createMachine({...}), bound to the entry.
    let init: ts.Expression | undefined
    for (const st of sf.statements) if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === opts.entry) init = d.initializer
    if (!init) {
      const fn = sf.statements.find((st): st is ts.FunctionDeclaration => ts.isFunctionDeclaration(st) && st.name?.text === opts.entry)
      if (fn) refuse(fn, `${opts.entry} makes the machine when called (a machine made by a function: export the machine itself)`)
      return {ok: false, refusals: [{where: file, what: `no machine ${opts.entry} in the file`}], notes}
    }
    const call = strip(init)
    if (!ts.isCallExpression(call) || !ts.isPropertyAccessExpression(call.expression) && !ts.isIdentifier(call.expression)) refuse(init, 'a machine not made by setup(...).createMachine or createMachine')
    const c = call as ts.CallExpression
    const callee = c.expression, made = ts.isPropertyAccessExpression(callee) ? callee.name.text : (callee as ts.Identifier).text
    if (made !== 'createMachine') refuse(c, 'a machine not made by createMachine')
    const setupArg = ts.isPropertyAccessExpression(callee) && ts.isCallExpression(callee.expression) && ts.isIdentifier(callee.expression.expression) && callee.expression.expression.text === 'setup' ? callee.expression.arguments[0] : undefined
    const props = (o: ts.Expression | undefined, name: string): ts.ObjectLiteralExpression | undefined => {
      if (!o || !ts.isObjectLiteralExpression(o)) return undefined
      const p = o.properties.find(x => ts.isPropertyAssignment(x) && x.name.getText() === name) as ts.PropertyAssignment | undefined
      if (!p) return undefined
      const v = strip(p.initializer)
      return ts.isObjectLiteralExpression(v) ? v : refuse(v, `setup's ${name} as other than an object of them`)
    }
    // v4's `cond` (XState v5 ignores it): refused where it is, not dropped.
    const config = c.arguments[0]
    const visit = (n: ts.Node) => { if (ts.isPropertyAssignment(n) && n.name.getText() === 'cond') refuse(n, 'a v4 `cond` (XState v5 reads `guard` and takes this transition unguarded: name the guard in `guard`)'); ts.forEachChild(n, visit) }
    if (config) visit(config)
    // The machine as XState builds it, from the code loaded with the real xstate.
    const box = sandbox(code, file, [opts.entry], {xstate: opts.xstate})
    const machine = box.get(opts.entry) as {config: {context?: Record<string, unknown>}}
    const ctx0 = machine.config.context
    if (ctx0 !== undefined && (typeof ctx0 !== 'object' || ctx0 === null)) refuse(config ?? c, 'a context computed by a function')
    // The context's variables and the payload's inputs, in one setup the guards and actions are read with.
    const s: Setup = {ours: f => f === sf, checker, sf, names: new Set(), vars: new Map(), maps: new Map(), lazySorts: new Map(), nowRole: 'input', hints: new WeakMap(), notes: new Set(), lazy: new Map()}
    const ex = new Exec(s), ctxVars = new Map<string, Var>(), init0: Record<string, Term> = {}
    for (const [k, v] of Object.entries(ctx0 ?? {})) {
      if (typeof v === 'number' && Number.isSafeInteger(v)) { const x = ex.newVar(k, {k: 'num'}, 'state'); ctxVars.set(k, x); init0[x.name] = {s: 'num', e: I.num(v)} }
      else if (typeof v === 'boolean') { const x = ex.newVar(k, {k: 'bool'}, 'state'); ctxVars.set(k, x); init0[x.name] = {s: 'bool', e: v ? I.T : I.F} }
      else refuse(config ?? c, `the context's ${k} (${JSON.stringify(v)}): numbers and booleans are the context the subset reads`)
      if (ctxVars.get(k)!.name !== k) refuse(config ?? c, `the context's ${k} shares a name with the builders'`)
    }
    // One function of ({context, event}) at a time, with the context as variables and the event's fields as inputs.
    const run = (f: ts.Expression, what: string): {v: V, p: Path} => {
      const fn = strip(f)
      if (!ts.isArrowFunction(fn) && !ts.isFunctionExpression(fn)) return refuse(f, `${what}: a reference to a function defined elsewhere`)
      if (fn.parameters.length > 1) refuse(fn, `${what} reads its params (named guards and actions with params are not in the subset)`)
      const heap = new Map<string, Parameters<typeof Map.prototype.set>[1]>()
      heap.set('xs.context', {k: 'rec', fields: new Map([...ctxVars].map(([k, x]) => [k, Exec.valueOf(x)])), origin: 'input'})
      heap.set('xs.event', {k: 'rec', fields: new Map(), origin: 'input', lazy: {prefix: ''}})
      heap.set('xs.arg', {k: 'rec', fields: new Map<string, V>([['context', {t: 'ref', id: 'xs.context'}], ['event', {t: 'ref', id: 'xs.event'}]]), origin: 'input'})
      let p: Path = {pc: [], locals: new Map(), heap: heap as never, wrote: [], nows: 0}
      if (fn.parameters[0]) p = ex.bind(fn.parameters[0].name, {t: 'ref', id: 'xs.arg'}, p)
      if (!ts.isBlock(fn.body)) { const [v, q] = ex.ev(fn.body, p); return {v, p: q} }
      const flow = ex.block(fn.body.statements, p)
      if (flow.live || flow.rets.length !== 1 || ex.throws.length) refuse(fn, `${what}: one return, no throw (a function by cases is written with ?: in the subset)`)
      return {v: flow.rets[0]![1], p: flow.rets[0]![0]}
    }
    // A guard: a condition of ({context, event}), or stateIn.
    const guardOf = (v: ts.Expression, name: string): B | {in: string} => {
      v = strip(v)
      // stateIn({a: 'b'}) or stateIn('#id.a.b'): whether the machine is in that state.
      if (ts.isCallExpression(v) && ts.isIdentifier(v.expression) && v.expression.text === 'stateIn') {
        const a = v.arguments[0] && strip(v.arguments[0])
        const path = (o: ts.Expression): string => (ts.isStringLiteral(o) ? o.text : ts.isObjectLiteralExpression(o) && o.properties.length === 1 && ts.isPropertyAssignment(o.properties[0]!) ? `${o.properties[0].name.getText()}.${path(strip(o.properties[0].initializer))}` : refuse(o, 'a stateIn of other than one state'))
        return {in: a ? path(a).replace(/^#[^.]*\./, '') : refuse(v, 'stateIn()')}
      }
      const {v: out} = run(v, `the guard ${name}`)
      if (out.t !== 'bool') refuse(v, `the guard ${name} returns other than a boolean`)
      return (out as {e: B}).e
    }
    // An action: the context an assign writes, null for one that writes none; refused for one that sends or spawns.
    const actionOf = (v: ts.Expression, name: string): Record<string, Term> | null => {
      v = strip(v)
      if (ts.isCallExpression(v) && ts.isIdentifier(v.expression) && v.expression.text === 'assign') {
        const arg = v.arguments[0] ? strip(v.arguments[0]) : refuse(v, 'assign()')
        const writes: Record<string, Term> = {}
        const put = (k: string, x: V, at: ts.Node) => {
          const cv = ctxVars.get(k) ?? refuse(at, `assigns ${k}, not in the context`)
          if (cv.sort.k === 'num' && x.t === 'num') writes[k] = {s: 'num', e: x.e}
          else if (cv.sort.k === 'bool' && x.t === 'bool') writes[k] = {s: 'bool', e: x.e}
          else refuse(at, `assigns ${k} a ${x.t}`)
        }
        if (ts.isObjectLiteralExpression(arg)) {
          for (const p of arg.properties) {
            if (!ts.isPropertyAssignment(p)) { refuse(p, 'an assign entry other than key: value'); continue }
            const k = p.name.getText(), init1 = strip(p.initializer)
            if (ts.isArrowFunction(init1) || ts.isFunctionExpression(init1)) put(k, run(init1, `the action ${name}'s ${k}`).v, p)
            else { const [x] = ex.ev(init1, {pc: [], locals: new Map(), heap: new Map(), wrote: [], nows: 0}); put(k, x, p) }
          }
        } else {
          const {v: out, p} = run(arg, `the action ${name}`)
          const o = out.t === 'ref' ? p.heap.get(out.id) : undefined
          if (o?.k !== 'rec') refuse(arg, `the action ${name} returns other than an object of context fields`)
          for (const [k, x] of (o as {fields: Map<string, V>}).fields) put(k, x, arg)
        }
        return writes
      }
      if (ts.isCallExpression(v) && ts.isIdentifier(v.expression) && ['raise', 'sendTo', 'sendParent', 'emit', 'enqueueActions', 'spawnChild', 'stopChild', 'forwardTo', 'cancel'].includes(v.expression.text)) return refuse(v, `the action ${name}: ${v.expression.text} (an action that sends or spawns is not in the subset)`)
      if (ts.isCallExpression(v) && ts.isIdentifier(v.expression) && v.expression.text === 'log') return null
      // A plain function: it writes no context (XState's actions write it through assign only); its effects are
      // outside the machine, left out.
      if (ts.isArrowFunction(v) || ts.isFunctionExpression(v)) { notes.push(`the action ${name} writes no context (its effects outside the machine are left out)`); return null }
      return refuse(v, `the action ${name}: an action the subset doesn't read`)
    }
    const guards: [string, B | {in: string}][] = []
    for (const g of props(setupArg, 'guards')?.properties ?? []) {
      if (!ts.isPropertyAssignment(g)) refuse(g, 'a guard written other than name: function')
      guards.push([(g as ts.PropertyAssignment).name.getText(), guardOf((g as ts.PropertyAssignment).initializer, (g as ts.PropertyAssignment).name.getText())])
    }
    const actions: [string, Record<string, Term> | null][] = []
    for (const a of props(setupArg, 'actions')?.properties ?? []) {
      if (!ts.isPropertyAssignment(a)) refuse(a, 'an action written other than name: action')
      actions.push([(a as ts.PropertyAssignment).name.getText(), actionOf((a as ts.PropertyAssignment).initializer, (a as ts.PropertyAssignment).name.getText())])
    }
    // Inline guards and actions: the config's source and the machine's own config walked together, each function the
    // config holds named by its path in it (what fromXState's `inline` takes).
    const inlineGuards: [string, B | {in: string}][] = [], inlineActions: [string, Record<string, Term> | null][] = []
    const key = (k: string) => (/^[A-Za-z_$][\w$]*$/.test(k) ? `.${k}` : `[${JSON.stringify(k)}]`)
    // Each transition's actions with its guard (an action runs only where the guard holds: a write's sign is proven there).
    const uses: {action: string, guard?: string}[] = []
    const keyOf = (e: ts.Expression, path: string) => (ts.isStringLiteral(strip(e)) ? `named:${(strip(e) as ts.StringLiteral).text}` : path)
    const walk = (ast: ts.Expression, rt: unknown, path: string, role?: 'actions' | 'guard'): void => {
      ast = strip(ast)
      if (!role && ts.isObjectLiteralExpression(ast)) {
        const get = (k: string) => ast.properties.find((x): x is ts.PropertyAssignment => ts.isPropertyAssignment(x) && x.name.getText() === k)
        const a = get('actions'), g = get('guard')
        if (a) {
          const gk = g ? keyOf(g.initializer, `${path}.guard`) : undefined, av = strip(a.initializer)
          const aks = ts.isArrayLiteralExpression(av) ? av.elements.map((el, i) => keyOf(el, `${path}.actions[${i}]`)) : [keyOf(av, `${path}.actions`)]
          for (const ak of aks) uses.push({action: ak, ...(gk ? {guard: gk} : {})})
        }
      }
      if (role === 'actions' && !ts.isArrayLiteralExpression(ast)) { if (typeof rt === 'function' && !ts.isStringLiteral(ast)) inlineActions.push([path, actionOf(ast, path)]); return }
      if (role === 'guard') { if (typeof rt === 'function') inlineGuards.push([path, guardOf(ast, path)]); return }
      if (ts.isObjectLiteralExpression(ast) && rt && typeof rt === 'object') {
        for (const p of ast.properties) {
          if (!ts.isPropertyAssignment(p)) continue
          const k = ts.isIdentifier(p.name) || ts.isStringLiteral(p.name) ? p.name.text : p.name.getText(), sub = (rt as Record<string, unknown>)[k]
          if (sub === undefined || k === 'context' || k === 'types') continue
          walk(p.initializer, sub, `${path}${key(k)}`, k === 'actions' || k === 'entry' || k === 'exit' ? 'actions' : k === 'guard' ? 'guard' : undefined)
        }
      } else if (ts.isArrayLiteralExpression(ast) && Array.isArray(rt)) ast.elements.forEach((el, i) => walk(el, rt[i], `${path}[${i}]`, role))
    }
    if (config) walk(config, machine.config, `${opts.entry}.config`)
    if (inlineActions.length || inlineGuards.length) notes.push(`${inlineActions.length} inline actions and ${inlineGuards.length} inline guards, each given by its place in the config`)
    for (const [p, ws] of inlineActions) actions.push([`(inline)${p}`, ws])
    // Which context numbers are naturals: as a rule's state, each written by every use of an action that writes it,
    // under its transition's guard (an action no transition names, or one named elsewhere, without one).
    const writesOf = new Map<string, Record<string, Term> | null>(actions.map(([n, ws]) => [n.startsWith('(inline)') ? n.slice(8) : `named:${n}`, ws]))
    const guardOfKey = new Map<string, B | {in: string}>([...guards.map(([n, g]) => [`named:${n}`, g] as const), ...inlineGuards])
    const used = new Set(uses.map(u => u.action))
    const all: {action: string, guard?: string}[] = [...uses, ...[...writesOf.keys()].filter(k => !used.has(k)).map(action => ({action}))]
    const writes: Record<string, Term> = {}
    for (const [k, x] of ctxVars) {
      let w: Term | undefined
      all.forEach((u, i) => {
        const t = writesOf.get(u.action)?.[k], g = u.guard ? guardOfKey.get(u.guard) : undefined
        if (!t || t.s !== 'num') return
        const under = g && !('in' in g) ? I.nite(g, t.e, I.nvar(x.name)) : t.e
        w = {s: 'num', e: I.nite(I.bvar(`$use${i}`), under, w && w.s === 'num' ? w.e : I.nvar(x.name))}
      })
      if (w) writes[x.name] = w
    }
    const vars = [...s.vars.values()]
    const model: Model = {name: opts.entry, shape: 'reducer', file, entry: opts.entry, params: [], inputs: vars.filter(x => x.role === 'input'), state: vars.filter(x => x.role === 'state'), maps: [],
      init: init0, writes, mapWrites: {}, outputs: [], refuse: I.F, pre: I.T, layout: {k: 'rec', fields: []}, events: [], notes: [], hints: s.hints}
    const {sorts, notes: sn} = sortsOf(model)
    notes.push(...sn)
    const P: Printer = {sorts, m: model, hoisted: new Map(), choiceVars: new Map()}
    const cx = () => ({m: model, sorts, atoms: [] as B[]})
    const envOf = (...xs: object[]) => { const vs = new Set<string>(); for (const x of xs) I.varsOf(x as never, vs); return `{${[...vs].join(', ')}}` }
    const parts: string[] = []
    if (model.inputs.length) parts.push(`inputs: {${model.inputs.map(x => `${x.name}: ${kindOf(x, sorts)}`).join(', ')}}`)
    const ints = model.state.filter(x => x.sort.k === 'num' && sorts.get(x.name) === 'int')
    if (ints.length) parts.push(`context: {${ints.map(x => `${x.name}: int.from(${(init0[x.name]!.e as {v: number}).v})`).join(', ')}}`)
    if (guards.length) parts.push(`guards: {${guards.map(([n, g]) => `${JSON.stringify(n)}: ${'in' in g ? `env => env.in(${JSON.stringify(g.in)})` : `(${envOf(g)}) => ${pb(g, P, cx())}`}`).join(', ')}}`)
    const namedActions = actions.filter(([n]) => !n.startsWith('(inline)'))
    if (namedActions.length) parts.push(`actions: {${namedActions.map(([n, ws]) => `${JSON.stringify(n)}: ${ws ? `(${envOf(...Object.values(ws).map(t => t.e))}) => ({${Object.entries(ws).map(([k, t]) => `${k}: ${pterm(t, P, cx(), k)}`).join(', ')}})` : 'null'}`).join(', ')}}`)
    const named = actions.filter(([n]) => !n.startsWith('(inline)'))
    const guardSrc = (g: B | {in: string}) => ('in' in g ? `env => env.in(${JSON.stringify(g.in)})` : `(${envOf(g)}) => ${pb(g, P, cx())}`)
    const actionSrc = (ws: Record<string, Term> | null) => (ws ? `(${envOf(...Object.values(ws).map(t => t.e))}) => ({${Object.entries(ws).map(([k, t]) => `${k}: ${pterm(t, P, cx(), k)}`).join(', ')}})` : 'null')
    if (inlineGuards.length || inlineActions.length) parts.push(`inline: {${[inlineGuards.length ? `guards: new Map([${inlineGuards.map(([p, g]) => `[${p}, ${guardSrc(g)}]`).join(', ')}])` : '', inlineActions.length ? `actions: new Map([${inlineActions.map(([p, ws]) => `[${p}, ${actionSrc(ws)}]`).join(', ')}])` : ''].filter(Boolean).join(', ')}}`)
    const bridge = `{${parts.join(', ')}}`
    const source = [
      `// Extracted by gdp-wired/extract from ${file} (${opts.entry}, an XState machine): its guards and actions read from setup().`,
      `// Checked against XState's own actor; read again with extractXState() after the code changes.`,
      `import {fromXState} from 'gdp-wired/xstate'`,
      ...(/\b(int|nat|bool|oneOf|str)\b/.test(bridge) ? [`import {${['bool', 'int', 'nat', 'oneOf', 'str', 'when', 'all', 'any', 'not', 'min', 'max', 'lit', 'Int', 'yes', 'no'].filter(n => new RegExp(`\\b${n}\\b`).test(bridge.replace(/'[^']*'|"[^"]*"/g, ''))).join(', ')}} from 'gdp-wired'`] : []),
      `import {${opts.entry}} from './${file.replace(/\.(ts|js)$/, '')}'`,
      '',
      `export const ${opts.entry}Chart = fromXState(${opts.entry}, ${bridge})`,
      '',
    ].join('\n')
    const NAMES = ['nat', 'int', 'bool', 'oneOf', 'str', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'Int'] as const
    void named
    const chart = compileFunction<(...xs: unknown[]) => ReturnType<typeof fromXState>>([...NAMES, 'fromXState', opts.entry], `return fromXState(${opts.entry}, ${bridge})`)(...NAMES.map(n => (dsl as Record<string, unknown>)[n]), fromXState, machine)
    // The check: XState's actor and the chart's compiled rule on the same events, payloads drawn for every input read.
    const rand = seeded(opts.check?.seed ?? 3)
    const draw = (v: Var): unknown => (v.sort.k === 'bool' ? rand(2) === 1 : v.sort.k === 'choice' ? v.sort.values[rand(v.sort.values.length)] : v.sort.k === 'str' ? ['a', 'b', ''][rand(3)] : sorts.get(v.name) === 'nat' ? rand(12) : rand(25) - 12)
    const runs = opts.check?.runs ?? 200, depth = opts.check?.depth ?? 16
    let result: {checked: number, failure?: string}
    try { result = conforms(chart as never, machine as never, opts.xstate.createActor as never, {runs, depth, seed: opts.check?.seed ?? 3, payload: () => Object.fromEntries(model.inputs.map(v => [v.name, draw(v)]))}) }
    catch (e) { result = {checked: 0, failure: `the chart's run throws: ${(e as Error).message}`} }
    const coverage: Coverage = {arms: box.arms.length, hit: box.counts.filter(n => n > 0).length, missed: box.arms.filter((_, i) => box.counts[i] === 0).map(a => `${a.label} at ${a.where}`)}
    const evidence = {runs, events: result.checked, coverage, ms: Math.round(performance.now() - t0), ...(result.failure ? {mismatch: result.failure} : {})}
    if (result.failure) return {ok: false, source, evidence, notes, refusals: [{where: file, what: `the chart and XState differ: ${result.failure}`}]}
    return {ok: true, source, chart, evidence, notes, refusals: []}
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    // fromXState's own refusals (`always`, `after`, `invoke`, ...), with its reason.
    const msg = (e as Error).message
    if (/has no chart counterpart|refus|inline|give its|a parallel state|several targets|wildcard|shallow history|both write|forbidden event|entry actions|exit actions|no state/.test(msg)) return {ok: false, refusals: [{where: file, what: `fromXState: ${msg}`}], notes}
    throw e
  }
}
