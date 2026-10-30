// XState machines read from the code (core/extract.ts's `extractXState`): the machine as XState builds it (the file
// loaded in the check's VM, with the real xstate), its states and transitions read by `fromXState` (core/xstate.ts), and
// each guard and action read from its source by the extractor's executor (named in `setup({guards, actions})`, in v4's
// options, or inline in the config), printed as the bridge fromXState takes: a guard as its condition, an `assign` as
// the context it writes. The chart is then run beside XState's own actor (`conforms`) on random events with payloads,
// every state and kept context field compared, the code's branches counted; any difference refuses it.
//
// - A machine made by a function (a factory): read with its arguments as the world gives them. An argument that is an
//   object of functions (the effects a machine is given, its services) is outside: each answer a guard or an action
//   reads of it is an input of the step (any value of its type, read once), a call that answers nothing an effect
//   outside, a promise an actor's (invoked). The argument a config takes as its context makes the initial context: each
//   field a param of the chart.
// - Invoked actors, timers and eventless transitions are fromXState's: an actor's done and error and a timer firing are
//   events from outside; the actors are replaced by inert ones in the check (their answers are the events it sends).
// - The context: its fields of the subset's types (numbers, booleans, string unions, strings, each also as `T | null`
//   or optional, a maybe); a field of another type (an object, a function) is left out where no guard or kept write
//   reads it (it reaches only the actors and effects outside), else refused where it is read.
// - Actions: `assign`; `emit`, `sendParent`, v4's `sendUpdate`, `spawnChild` and `log` write no context (what they
//   send goes outside: an emitted event to listeners, a spawned actor's answers come back as events from outside);
//   `raise`, `sendTo`, `enqueueActions`, `forwardTo`, `cancel`, `stopChild` and v4's `choose` and `pure` are refused.
// - v4 machines (`createMachine(config, options)`): `cond`, `(context, event)` guards and actions, `services`. The check
//   runs them on the XState v4 given (opts.xstate).
import ts from 'typescript'
import * as dsl from './dsl.ts'
import {compileFunction, seeded} from './machine.ts'
import * as I from './extract-ir.ts'
import type {B} from './extract-ir.ts'
import {Exec, type Model, type Path, Refusal, type Setup, type Shape, type Sort, type Source, type Term, type V, type Var, beside, memberName, normalize, placed, program, refuse, scriptKind, shapeOf, sourceOf, where} from './extract-read.ts'
import type {Law} from './machine.ts'
import type {Name} from './extract.ts'
import type {Rule} from './dsl.ts'
import {type Printer, kindOf, pb, pterm, sortsOf} from './extract-print.ts'
import {type Coverage, sandbox} from './extract-check.ts'
import {conforms, eventsOf, fromXState} from './xstate.ts'

export type XStateOptions = {
  // The file's name, for code given as a string; the machine (or the function that makes one), by default the file's one.
  file?: string, entry?: string,
  // The XState the code is written for (v5's module, or v4's: the check runs the machine on it); by default the one the
  // file imports (its project's node_modules).
  xstate?: {createActor?: (m: never) => {start: () => unknown}, interpret?: (m: never) => {start: () => unknown}} & Record<string, unknown>,
  // Other files of the repository the entry's relative imports name (by their path beside the entry's).
  files?: Record<string, string>,
  check?: {runs?: number, depth?: number, seed?: number},
}
export type XStateExtraction = {
  ok: boolean, source?: string, chart?: ReturnType<typeof fromXState>, refusals: {where: string, what: string}[], notes: string[],
  // The rule the chart compiles to, what it keeps true by its construction, and its names in the code's terms
  // (`value` the state, the context's fields, `event` and `event.<field>`), as every front end's.
  rule?: Rule, invariants?: Law[], names?: Name[],
  evidence?: {runs: number, events: number, coverage: Coverage, ms: number, mismatch?: string},
}
const strip = (e: ts.Expression): ts.Expression => (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isSatisfiesExpression(e) ? strip(e.expression) : e)
const isFn = (e: ts.Node): e is ts.ArrowFunction | ts.FunctionExpression => ts.isArrowFunction(e) || ts.isFunctionExpression(e)
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Obj = Record<string, any>
// A context field: a variable of the rule (a maybe: whether it is there, and its value), or left out.
type Field = {k: string, var?: Var, maybe?: {has: Var, inner: Var, null: boolean}, dropped?: string, kind?: string}

export function extractXState(at: Source, opts: XStateOptions = {}): XStateExtraction {
  let code: string, file: string, entry: string, xstate: XStateOptions['xstate']
  try {
    ;({code, file} = sourceOf(at, opts.file, 'machine.ts'))
    xstate = opts.xstate ?? beside(file, 'xstate') ?? none(file, 'no xstate package resolves from the file (install it in its project, or give it: {xstate: await import(\'xstate\')})')
    entry = opts.entry ?? machineOf(code, file)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const x = readXState(code, {...opts, file, entry, xstate})
  if (!opts.entry) x.notes.unshift(`the entry inferred: ${entry}, the file's one machine`)
  return x
}
const none = (where: string, what: string): never => { throw new Refusal(where, what) }
// The machine a file makes: a createMachine (setup(...)'s too) or a function returning one, the only one.
function machineOf(code: string, file: string): string {
  const sf = ts.createSourceFile(file, code, ts.ScriptTarget.ES2022, true, scriptKind(file))
  const makes = (e: ts.Node | undefined): boolean => {
    if (!e) return false
    if (isFn(e) || ts.isFunctionDeclaration(e)) { const b = e.body, st = b && ts.isBlock(b) ? b.statements.at(-1) : undefined; return b && ts.isBlock(b) ? !!st && ts.isReturnStatement(st) && makes(st.expression) : makes(b) }
    const c = strip(e as ts.Expression)
    if (isFn(c)) return makes(c)
    return ts.isCallExpression(c) && (ts.isIdentifier(c.expression) ? c.expression.text : ts.isPropertyAccessExpression(c.expression) ? c.expression.name.text : '') === 'createMachine'
  }
  const found = sf.statements.flatMap(st => (ts.isVariableStatement(st) ? st.declarationList.declarations.filter(d => ts.isIdentifier(d.name) && makes(d.initializer)).map(d => (d.name as ts.Identifier).text) : ts.isFunctionDeclaration(st) && st.name && makes(st) ? [st.name.text] : []))
  return found.length === 1 ? found[0]! : none(file, found.length ? `several machines in the file (${found.join(', ')}): name one (entry)` : 'no machine in the file (createMachine, setup(...).createMachine, or a function returning one): name the entry')
}
function readXState(code: string, opts: XStateOptions & {file: string, entry: string}): XStateExtraction {
  const file = opts.file, t0 = performance.now(), notes: string[] = []
  try {
    const at = placed(file), root = at.slice(0, at.length - file.split('/').pop()!.length)
    const extra = Object.fromEntries(Object.entries(opts.files ?? {}).map(([p, c]) => [normalize(`${root}${p}`), c]))
    const {sf, checker} = program(code, at, extra)
    // The entry: a machine (setup(...).createMachine(...), createMachine(...)) or a function that returns one.
    let init: ts.Expression | undefined, factory: ts.FunctionLikeDeclaration | undefined
    for (const st of sf.statements) {
      if (ts.isVariableStatement(st)) for (const d of st.declarationList.declarations) if (ts.isIdentifier(d.name) && d.name.text === opts.entry && d.initializer) {
        const x = strip(d.initializer)
        if (isFn(x)) factory = x; else init = d.initializer
      }
      if (ts.isFunctionDeclaration(st) && st.name?.text === opts.entry) factory = st
    }
    if (factory) {
      const body = factory.body ?? refuse(factory, `${opts.entry} has no body`)
      if (!ts.isBlock(body)) init = body as ts.Expression
      else {
        const stmts = body.statements.filter(s => !ts.isTypeAliasDeclaration(s) && !ts.isInterfaceDeclaration(s))
        const ret = stmts.at(-1)
        if (stmts.length !== 1 || !ret || !ts.isReturnStatement(ret) || !ret.expression) refuse(body, `${opts.entry} does more than return the machine (a factory read here is one return)`)
        init = (ret as ts.ReturnStatement).expression
      }
      if (factory.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) refuse(factory, 'an async factory')
    }
    if (!init) return {ok: false, refusals: [{where: file, what: `no machine ${opts.entry} in the file`}], notes}
    const call = strip(init)
    if (!ts.isCallExpression(call) || (!ts.isPropertyAccessExpression(call.expression) && !ts.isIdentifier(call.expression))) return refuse(init, 'a machine not made by setup(...).createMachine or createMachine')
    const callee = call.expression, made = ts.isPropertyAccessExpression(callee) ? callee.name.text : (callee as ts.Identifier).text
    if (made !== 'createMachine') refuse(call, 'a machine not made by createMachine')
    const setupArg = ts.isPropertyAccessExpression(callee) && ts.isCallExpression(callee.expression) && ts.isIdentifier(callee.expression.expression) && callee.expression.expression.text === 'setup' ? callee.expression.arguments[0] : undefined
    const config = call.arguments[0] && strip(call.arguments[0]), options = call.arguments[1] && strip(call.arguments[1])
    if (!config || !ts.isObjectLiteralExpression(config)) return refuse(call, 'a machine whose config is not an object literal')
    if (call.arguments.length > 2) refuse(call, 'createMachine with more than a config and its options')
    const propRaw = (o: ts.Expression | undefined, name: string): ts.Expression | undefined => {
      if (!o || !ts.isObjectLiteralExpression(o)) return undefined
      const p = o.properties.find(x => (ts.isPropertyAssignment(x) || ts.isShorthandPropertyAssignment(x)) && memberName(x.name) === name)
      return p && (ts.isPropertyAssignment(p) ? p.initializer : ts.isShorthandPropertyAssignment(p) ? p.name : undefined)
    }
    const prop = (o: ts.Expression | undefined, name: string) => { const x = propRaw(o, name); return x && strip(x) }
    // What a name stands for, through the program: a const's value or a function declared, in the files read (an import,
    // `export default X`, a const of a const), as TypeScript resolves the name; anything else as it is.
    const valueOf = (e: ts.Expression, depth = 0): ts.Expression | ts.FunctionDeclaration => {
      e = strip(e)
      if (!ts.isIdentifier(e) || depth > 8) return e
      let sym = ts.isShorthandPropertyAssignment(e.parent) && e.parent.name === e ? checker.getShorthandAssignmentValueSymbol(e.parent) : checker.getSymbolAtLocation(e)
      if (sym && sym.flags & ts.SymbolFlags.Alias) sym = checker.getAliasedSymbol(sym)
      const d = sym?.valueDeclaration
      if (d && ts.isFunctionDeclaration(d) && d.body) return d
      if (d && ts.isVariableDeclaration(d) && d.initializer && d.parent.flags & ts.NodeFlags.Const && !d.getSourceFile().isDeclarationFile) return valueOf(d.initializer, depth + 1)
      return e
    }
    const objOf = (o: ts.Expression | undefined, name: string): ts.ObjectLiteralExpression | undefined => {
      const v0 = prop(o, name)
      if (v0 === undefined) return undefined
      const v = valueOf(v0)
      return ts.isObjectLiteralExpression(v) ? v : refuse(v0, `the ${name} given as other than an object of them`)
    }

    // The factory's arguments: an object of functions (outside), or the context it starts with (the chart's params).
    type Arg = {name: string, kind: 'outside' | 'context', node: ts.Node, type: ts.Type, fields?: [string, ts.Type][]}
    const args: {param: ts.ParameterDeclaration, parts: Arg[]}[] = []
    const ctxExpr = prop(config, 'context')
    for (const param of factory?.parameters ?? []) {
      if (param.dotDotDotToken) refuse(param, 'a rest argument')
      const parts: Arg[] = []
      const classify = (name: string, node: ts.Node, t: ts.Type): Arg => {
        if (ctxExpr && ts.isIdentifier(ctxExpr) && ctxExpr.text === name) return {name, kind: 'context', node, type: t}
        const nn = checker.getNonNullableType(t), props = checker.getPropertiesOfType(nn)
        // A function's member, or one of type any (untyped code's): the machine's own guards and actions reading it are
        // refused where they call it (its answer has no type the subset reads); an actor's body calling it is outside.
        const untyped = (p: ts.Symbol) => (checker.getTypeOfSymbolAtLocation(p, node).flags & ts.TypeFlags.Any) !== 0
        const fnTyped = (p: ts.Symbol) => untyped(p) || checker.getSignaturesOfType(checker.getNonNullableType(checker.getTypeOfSymbolAtLocation(p, node)), ts.SignatureKind.Call).length > 0
        if (props.length && props.every(fnTyped)) {
          const anys = props.filter(untyped).map(p => p.getName())
          if (anys.length) notes.push(`${name}: ${anys.join(', ')} of type any, called only where an actor runs (outside the machine): a guard or an action that calls one is refused`)
          return {name, kind: 'outside', node, type: nn, fields: props.map(p => [p.getName(), checker.getNonNullableType(checker.getTypeOfSymbolAtLocation(p, node))])}
        }
        const bad = props.find(p => !fnTyped(p))
        return refuse(node, `${name}: a factory argument that is neither the machine's context nor an object of functions (${props.length ? `${bad!.getName()} is of type ${checker.typeToString(checker.getTypeOfSymbolAtLocation(bad!, node))}` : `of type ${checker.typeToString(t)}`})`)
      }
      if (ts.isIdentifier(param.name)) parts.push(classify(param.name.text, param, checker.getTypeAtLocation(param)))
      else if (ts.isObjectBindingPattern(param.name)) for (const el of param.name.elements) {
        if (el.dotDotDotToken || el.propertyName || !ts.isIdentifier(el.name)) refuse(el, 'a destructured factory argument other than {a, b}')
        parts.push(classify((el.name as ts.Identifier).text, el, checker.getTypeAtLocation(el)))
      } else refuse(param, 'an array-destructured argument')
      args.push({param, parts})
    }
    const ctxArg = args.flatMap(a => a.parts).find(p => p.kind === 'context')

    // The machine as XState builds it: the factory called with stubs (each answer read from the step's payload, a promise
    // that never settles, nothing), and with the initial context drawn per run.
    const box = sandbox(code, file, [opts.entry], {xstate: opts.xstate}, undefined, opts.files ?? {})
    const answers: Obj = {}
    const stubOf = (a: Arg): unknown => {
      const out: Obj = {}
      for (const [f, t] of a.fields ?? []) {
        const sig = checker.getSignaturesOfType(t, ts.SignatureKind.Call)[0]
        // An untyped one: called while the machine is made, it throws (and the factory is refused).
        if (!sig) { out[f] = () => { throw new Error(`${a.name}.${f}, of type any, called`) }; continue }
        const rt = checker.getReturnTypeOfSignature(sig)
        const promise = rt.getSymbol()?.getName() === 'Promise', path = `${a.name}.${f}`
        out[f] = promise ? () => new Promise(() => {}) : () => answers[path]
      }
      return out
    }
    const instance = (ctx: Obj | undefined): Obj => {
      if (!factory) return box.get(opts.entry) as Obj
      const values = args.map(({param, parts}) => {
        const one = (p: Arg) => (p.kind === 'outside' ? stubOf(p) : ctx)
        return ts.isIdentifier(param.name) ? one(parts[0]!) : Object.fromEntries(parts.map(p => [p.name, one(p)]))
      })
      const r = box.call(opts.entry, undefined, values)
      if (!r.ok) throw new Refusal(where(factory), `${opts.entry}(...) throws when called: ${r.error}`)
      return r.value as Obj
    }
    const version = (m: Obj): 4 | 5 => (typeof m.getInitialSnapshot === 'function' ? 5 : typeof m.withConfig === 'function' ? 4 : refuse(call, 'createMachine made no machine of XState 4 or 5'))

    // The context's fields, by their type (setup's types, v4's createMachine<Context>, the factory's argument) or else
    // by the values the config starts them at.
    const s: Setup = {ours: f => f === sf || f.fileName in extra, checker, sf, names: new Set(), vars: new Map(), maps: new Map(), lazySorts: new Map(), nowRole: 'input', hints: new WeakMap(), notes: new Set(), lazy: new Map(), xstate: {outside: new Map()}}
    const ex = new Exec(s)
    const ctxType = ((): ts.Type | undefined => {
      if (ctxArg) return ctxArg.type
      const types = propRaw(setupArg, 'types')
      if (types) { const t = checker.getTypeAtLocation(types), c = t.getProperty('context'); if (c) return checker.getTypeOfSymbolAtLocation(c, types) }
      const ta = call.typeArguments?.[0]
      if (ta) return checker.getTypeFromTypeNode(ta)
      const schema = propRaw(prop(config, 'schema'), 'context')
      if (schema) return checker.getTypeAtLocation(schema)
      return undefined
    })()
    const m0 = instance(ctxArg ? {} : undefined), v = version(m0)
    const raw0 = (m0.config?.context ?? (v === 4 ? m0.context : undefined)) as unknown
    if (!ctxArg && raw0 !== undefined && (typeof raw0 !== 'object' || raw0 === null)) refuse(ctxExpr ?? config, 'a context computed by a function')
    const fields: Field[] = []
    const sortOf = (sh: Shape): Sort | undefined => (sh.k === 'num' || sh.k === 'bool' || sh.k === 'choice' || sh.k === 'str' ? sh : undefined)
    const keys = ctxType ? checker.getPropertiesOfType(ctxType).map(p => p.getName()) : Object.keys((raw0 ?? {}) as Obj)
    for (const k of keys) {
      if (s.names.has(k) || ['event', 'in', 'last'].includes(k)) refuse(config, `the context's ${k} shares a name with the chart's own`)
      const value = (raw0 as Obj | undefined)?.[k]
      let sort: Sort | undefined, maybe: 'null' | 'undefined' | undefined, why: string | undefined
      if (ctxType) {
        const p = ctxType.getProperty(k)!, t = checker.getTypeOfSymbolAtLocation(p, config)
        const parts = t.isUnion() ? t.types : [t], missing = parts.filter(x => x.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined))
        const rest = parts.filter(x => !(x.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)))
        if (missing.some(x => x.flags & ts.TypeFlags.Null) && (missing.some(x => x.flags & ts.TypeFlags.Undefined) || p.flags & ts.SymbolFlags.Optional)) why = 'null or undefined (two ways missing)'
        else {
          maybe = missing.length ? (missing[0]!.flags & ts.TypeFlags.Null ? 'null' : 'undefined') : p.flags & ts.SymbolFlags.Optional ? 'undefined' : undefined
          try {
            const rt = rest.length === 1 ? rest[0]! : rest.every(x => x.flags & ts.TypeFlags.BooleanLiteral) ? checker.getBooleanType() : undefined
            const sh = rt ? shapeOf(rt, checker, config) : rest.every(x => x.flags & ts.TypeFlags.StringLiteral) ? {k: 'choice' as const, values: rest.map(x => (x as ts.StringLiteralType).value)} : undefined
            sort = sh && sortOf(sh)
            if (!sort) why = `of type ${checker.typeToString(t)}`
          } catch (e) { if (!(e instanceof Refusal)) throw e; why = e.what }
        }
      } else {
        if (typeof value === 'number' && Number.isSafeInteger(value)) sort = {k: 'num'}
        else if (typeof value === 'boolean') sort = {k: 'bool'}
        else if (typeof value === 'string') sort = {k: 'str'}
        else why = `starting at ${JSON.stringify(value)} with no type given`
      }
      if (!sort) { fields.push({k, dropped: why!}); continue }
      if (maybe) {
        const has = {name: `${k}.isSome`, sort: {k: 'bool'} as Sort, role: 'state' as const}, inner = {name: `${k}.inner`, sort, role: 'state' as const}
        s.names.add(k); s.vars.set(has.name, has); s.vars.set(inner.name, inner)
        fields.push({k, maybe: {has, inner, null: maybe === 'null'}})
      } else {
        const x = ex.newVar(k, sort, 'state')
        if (x.name !== k) refuse(config, `the context's ${k} shares a name with the builders'`)
        fields.push({k, var: x})
      }
    }
    // The chart's events: those the machine reacts to, and those its type declares that no state takes (each a step
    // that changes nothing, as XState ignores it). event.type in a guard or an action is which event it is.
    const declared = ((): string[] => {
      const et = ((): ts.Type | undefined => {
        const types = propRaw(setupArg, 'types')
        if (types) { const t = checker.getTypeAtLocation(types), e = t.getProperty('events'); if (e) return checker.getTypeOfSymbolAtLocation(e, types) }
        const ta = call.typeArguments?.[1]
        if (ta) return checker.getTypeFromTypeNode(ta)
        const schema = propRaw(prop(config, 'schema'), 'events')
        return schema && checker.getTypeAtLocation(schema)
      })()
      if (!et) return []
      const out: string[] = []
      for (const m of et.isUnion() ? et.types : [et]) { const tp = m.getProperty('type'), tt = tp && checker.getTypeOfSymbolAtLocation(tp, config); for (const x of tt ? (tt.isUnion() ? tt.types : [tt]) : []) if (x.flags & ts.TypeFlags.StringLiteral && !out.includes((x as ts.StringLiteralType).value)) out.push((x as ts.StringLiteralType).value) }
      return out
    })()
    const handled = eventsOf(m0), events = [...handled, ...declared.filter(e => !handled.includes(e))]
    if (events.length > handled.length) notes.push(`events its type declares that no state takes, each a step that changes nothing: ${events.slice(handled.length).join(', ')}`)
    const eventVar: Var = {name: 'event', sort: {k: 'choice', values: events}, role: 'input'}
    s.vars.set('event', eventVar); s.names.add('event')
    const ctxValue = (): V => ({t: 'ref', id: 'xs.context'})
    const ctxHeap = (): Map<string, unknown> => {
      const heap = new Map<string, unknown>()
      heap.set('xs.context', {k: 'rec', origin: 'input', fields: new Map<string, V>(fields.map(f => [f.k, f.var ? Exec.valueOf(f.var) : f.maybe ? {t: 'opt', has: I.bvar(f.maybe.has.name), v: Exec.valueOf(f.maybe.inner), ...(f.maybe.null ? {null: true as const} : {})} : {t: 'opaque', what: `the context's ${f.k} is ${f.dropped}`}]))})
      heap.set('xs.event', {k: 'rec', fields: new Map<string, V>([['type', Exec.valueOf(eventVar)]]), origin: 'input', lazy: {prefix: ''}})
      heap.set('xs.arg', {k: 'rec', fields: new Map<string, V>([['context', ctxValue()], ['event', {t: 'ref', id: 'xs.event'}]]), origin: 'input'})
      return heap
    }
    // The factory's arguments, in scope: those of functions as outside, the context's start as unreadable (it is the
    // start, not the context as it is).
    const scope = new Map<string, V>(args.flatMap(a => a.parts).filter(p => p.kind === 'outside').map(p => [p.name, {t: 'outside', path: p.name} as V]))
    // One function of ({context, event}) (v4: (context, event)) at a time, with the context as variables and the event's
    // fields as inputs.
    const run = (f: ts.Expression, what: string): {v: V, p: Path} => {
      const fn = valueOf(f)
      if (!isFn(fn) && !ts.isFunctionDeclaration(fn)) return refuse(f, `${what}: a reference to a function defined elsewhere`)
      if (fn.parameters.length > (v === 4 ? 2 : 1)) refuse(fn, `${what} reads its params (guards and actions with params are not in the subset)`)
      if (fn.getSourceFile() === sf) (s.spans ??= []).push([fn.getStart(), fn.end])
      let p: Path = {pc: [], locals: new Map(scope), heap: ctxHeap() as never, wrote: [], nows: 0}
      if (v === 5 && fn.parameters[0]) p = ex.bind(fn.parameters[0].name, {t: 'ref', id: 'xs.arg'}, p)
      if (v === 4 && fn.parameters[0]) p = ex.bind(fn.parameters[0].name, ctxValue(), p)
      if (v === 4 && fn.parameters[1]) p = ex.bind(fn.parameters[1].name, {t: 'ref', id: 'xs.event'}, p)
      if (!ts.isBlock(fn.body!)) { const [x, q] = ex.ev(fn.body as ts.Expression, p); return {v: x, p: q} }
      const flow = ex.block(fn.body.statements, p)
      if (flow.live || flow.rets.length !== 1 || ex.throws.length) refuse(fn, `${what}: one return, no throw (a function by cases is written with ?: in the subset)`)
      return {v: flow.rets[0]![1], p: flow.rets[0]![0]}
    }
    // A guard: a condition of ({context, event}), or stateIn.
    const guardOf = (g: ts.Expression, name: string): B | {in: string} => {
      const gv = valueOf(g)
      if (ts.isFunctionDeclaration(gv)) { const {v: out} = run(g, `the guard ${name}`); if (out.t !== 'bool') refuse(g, `the guard ${name} returns other than a boolean`); return (out as {e: B}).e }
      g = gv
      if (ts.isCallExpression(g) && ts.isIdentifier(g.expression) && g.expression.text === 'stateIn') {
        const a = g.arguments[0] && strip(g.arguments[0])
        const path = (o: ts.Expression): string => (ts.isStringLiteral(o) ? o.text : ts.isObjectLiteralExpression(o) && o.properties.length === 1 && ts.isPropertyAssignment(o.properties[0]!) ? `${o.properties[0].name.getText()}.${path(strip(o.properties[0].initializer))}` : refuse(o, 'a stateIn of other than one state'))
        return {in: a ? path(a).replace(/^#[^.]*\./, '') : refuse(g, 'stateIn()')}
      }
      const {v: out} = run(g, `the guard ${name}`)
      if (out.t !== 'bool') refuse(g, `the guard ${name} returns other than a boolean`)
      return (out as {e: B}).e
    }
    // What an action writes of the context: a write per kept field (left out fields take anything), null for none.
    // A write that can't be read (from a payload the subset doesn't read, of another type than the field's) is kept as
    // why: the field it writes is left out where nothing else reads it, else refused there.
    type Write = {k: string, x?: V, failed?: string}
    const failing = <T>(f: () => T): T | {failed: string} => { try { return f() } catch (e) { if (e instanceof Refusal) return {failed: `${e.where}: ${e.what}`}; throw e } }
    const actionOf = (a: ts.Expression, name: string): Write[] | null => {
      const av = valueOf(a)
      if (ts.isFunctionDeclaration(av)) { notes.push(`the action ${name} writes no context (its effects outside the machine are left out)`); return null }
      a = av
      const fname = ts.isCallExpression(a) && ts.isIdentifier(a.expression) ? a.expression.text : undefined
      if (fname === 'assign' && ts.isCallExpression(a)) {
        const arg = a.arguments[0] ? strip(a.arguments[0]) : refuse(a, 'assign()')
        const writes: Write[] = []
        if (ts.isObjectLiteralExpression(arg)) {
          for (const p of arg.properties) {
            if (!ts.isPropertyAssignment(p)) { refuse(p, 'an assign entry other than key: value'); continue }
            const k = memberName(p.name), v1 = strip(p.initializer)
            const x = failing(() => (isFn(v1) ? run(v1, `the action ${name}'s ${k}`).v : ex.ev(v1, {pc: [], locals: new Map(scope), heap: ctxHeap() as never, wrote: [], nows: 0})[0]))
            writes.push('failed' in x ? {k, failed: x.failed} : {k, x})
          }
        } else {
          const r = failing(() => run(arg, `the action ${name}`))
          if ('failed' in r) {
            // Unread as a whole: the fields it returns (an object literal's) each written by it, unread.
            const body = isFn(arg) ? (ts.isBlock(arg.body) ? (arg.body.statements.at(-1) && ts.isReturnStatement(arg.body.statements.at(-1)!) ? (arg.body.statements.at(-1) as ts.ReturnStatement).expression : undefined) : arg.body) : undefined
            const lit = body && strip(body)
            if (!lit || !ts.isObjectLiteralExpression(lit)) refuse(arg, r.failed)
            for (const p of (lit as ts.ObjectLiteralExpression).properties) if (ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) writes.push({k: memberName(p.name), failed: r.failed})
          } else {
            const {v: out, p} = r
            const o = out.t === 'ref' ? p.heap.get(out.id) : undefined
            if (o?.k !== 'rec') refuse(arg, `the action ${name} returns other than an object of context fields`)
            for (const [k, x] of (o as {fields: Map<string, V>}).fields) writes.push({k, x})
          }
        }
        for (const w of writes) if (!fields.some(f => f.k === w.k)) refuse(a, `the action ${name} assigns ${w.k}, not in the context`)
        return writes
      }
      if (fname && ['raise', 'sendTo', 'enqueueActions', 'forwardTo', 'cancel', 'stopChild', 'choose', 'pure', 'send', 'respond', 'escalate'].includes(fname)) return refuse(a, `the action ${name}: ${fname} (an action that sends to the machine itself, or picks its actions as it runs, is not in the subset)`)
      if (fname && ['emit', 'sendParent', 'sendUpdate', 'spawnChild', 'log'].includes(fname)) { notes.push(`the action ${name}: ${fname} writes no context (${fname === 'spawnChild' ? 'the actor it starts answers by events from outside' : 'what it sends goes outside the machine'})`); return null }
      // A plain function: it writes no context (XState's actions write it through assign only); its effects are
      // outside the machine, left out.
      if (isFn(a)) { notes.push(`the action ${name} writes no context (its effects outside the machine are left out)`); return null }
      return refuse(a, `the action ${name}: an action the subset doesn't read`)
    }
    // An object's entries by name: `name: value`, `name` (the value its name stands for), `...other` (another
    // object's entries, the later ones winning, as JavaScript spreads them).
    const named = (o: ts.ObjectLiteralExpression | undefined, out = new Map<string, ts.Expression>(), depth = 0): Map<string, ts.Expression> => {
      for (const x of o?.properties ?? []) {
        if (ts.isPropertyAssignment(x)) out.set(memberName(x.name), x.initializer)
        else if (ts.isShorthandPropertyAssignment(x)) out.set(x.name.text, x.name)
        else if (ts.isSpreadAssignment(x)) { const w = valueOf(x.expression); if (!ts.isObjectLiteralExpression(w) || depth > 4) refuse(x, 'an entry spread from other than an object of them'); named(w as ts.ObjectLiteralExpression, out, depth + 1) }
        else refuse(x, 'an entry written other than name: value')
      }
      return out
    }
    // Only the guards and actions the config names are read: XState runs no other (an object shared by several machines
    // holds others').
    const names = new Set<string>()
    const namesIn = (e: ts.Expression, role?: boolean): void => {
      e = strip(e)
      if (role && ts.isStringLiteral(e)) { names.add(e.text); return }
      if (ts.isArrayLiteralExpression(e)) { e.elements.forEach(el => namesIn(el, role)); return }
      if (ts.isCallExpression(e)) { e.arguments.forEach(el => namesIn(el, role)); return }
      if (!ts.isObjectLiteralExpression(e)) return
      for (const p of e.properties) if (ts.isPropertyAssignment(p)) {
        const k = ts.isIdentifier(p.name) || ts.isStringLiteral(p.name) ? p.name.text : ''
        namesIn(p.initializer, ['guard', 'cond', 'actions', 'entry', 'exit'].includes(k) || (role === true && k === 'type'))
      }
    }
    namesIn(config)
    const implementations = (o: ts.ObjectLiteralExpression | undefined, what: string) => {
      const all = [...named(o)], used = all.filter(([n]) => names.has(n))
      if (used.length < all.length) notes.push(`${all.length - used.length} ${what} of the object the config never names, not read (XState runs only those it names)`)
      return used
    }
    const guards: [string, B | {in: string}][] = [], actions: [string, Write[] | null][] = []
    const where0 = v === 5 ? setupArg : options
    for (const [n, g] of implementations(objOf(where0, 'guards'), 'guards')) guards.push([n, guardOf(g, n)])
    for (const [n, a] of implementations(objOf(where0, 'actions'), 'actions')) actions.push([n, actionOf(a, n)])
    if (v === 4 && setupArg) refuse(setupArg, 'setup() with XState v4')
    const unread = (where0 && ts.isObjectLiteralExpression(where0) ? where0.properties : []).map(x => (x.name ? memberName(x.name) : '')).filter(k => !['guards', 'actions', 'delays', 'actors', 'services', 'types', 'schemas'].includes(k))
    if (unread.length) refuse(where0!, `${unread.join(', ')} in ${v === 5 ? 'setup' : 'the options'}: not read`)
    // Inline guards and actions: the config's source and the machine's own config walked together, each function the
    // config holds named by its path in it (what fromXState's `inline` takes).
    const inlineGuards: [string, B | {in: string}][] = [], inlineActions: [string, Write[] | null][] = []
    const key = (k: string) => (/^[A-Za-z_$][\w$]*$/.test(k) ? `.${k}` : `[${JSON.stringify(k)}]`)
    const machineName = factory ? 'machine' : opts.entry
    // A computed key ([RECONNECT_DELAY_MS]): its value, a number or a string the module's consts make.
    const computed = (n: ts.ComputedPropertyName): string => {
      const [x] = ex.ev(n.expression, {pc: [], locals: new Map(), heap: new Map(), wrote: [], nows: 0})
      return x.t === 'num' && x.e.op === 'const' ? String(x.e.v) : x.t === 'str' && x.e.op === 'slit' ? x.e.value : refuse(n, 'a computed key that is not a constant')
    }
    // Each transition's actions with its guard (an action runs only where the guard holds: a write's sign is proven there).
    const uses: {action: string, guard?: string}[] = []
    const keyOf = (e: ts.Expression, path: string) => (ts.isStringLiteral(strip(e)) ? `named:${(strip(e) as ts.StringLiteral).text}` : ts.isObjectLiteralExpression(strip(e)) && prop(strip(e), 'type') && ts.isStringLiteral(prop(strip(e), 'type')!) ? `named:${(prop(strip(e), 'type') as ts.StringLiteral).text}` : path)
    const walk = (ast: ts.Expression, rt: unknown, path: string, role?: 'actions' | 'guard'): void => {
      ast = strip(ast)
      if (!role && ts.isObjectLiteralExpression(ast)) {
        const a = prop(ast, 'actions'), g = prop(ast, 'guard') ?? prop(ast, 'cond')
        if (a) {
          const gk = g ? keyOf(g, `${path}.${prop(ast, 'guard') ? 'guard' : 'cond'}`) : undefined
          const aks = ts.isArrayLiteralExpression(a) ? a.elements.map((el, i) => keyOf(el, `${path}.actions[${i}]`)) : [keyOf(a, `${path}.actions`)]
          for (const ak of aks) uses.push({action: ak, ...(gk ? {guard: gk} : {})})
        }
      }
      if (role === 'actions' && !ts.isArrayLiteralExpression(ast)) {
        // {type: name, params}: the named action (its params read by no write here, or refused where it is read).
        if (ts.isObjectLiteralExpression(ast)) return
        if (typeof rt === 'function' && !ts.isStringLiteral(ast)) inlineActions.push([path, actionOf(ast, path)])
        return
      }
      if (role === 'guard') { if (typeof rt === 'function') inlineGuards.push([path, guardOf(ast, path)]); return }
      if (ts.isObjectLiteralExpression(ast) && rt && typeof rt === 'object') {
        for (const p of ast.properties) {
          if (ts.isShorthandPropertyAssignment(p) || ts.isSpreadAssignment(p) || ts.isMethodDeclaration(p)) refuse(p, 'a config entry written other than key: value')
          if (!ts.isPropertyAssignment(p)) continue
          const k = ts.isIdentifier(p.name) || ts.isStringLiteral(p.name) || ts.isNumericLiteral(p.name) ? p.name.text : ts.isComputedPropertyName(p.name) ? computed(p.name) : p.name.getText()
          const sub = (rt as Record<string, unknown>)[k]
          if (sub === undefined || k === 'context' || k === 'types' || k === 'schema' || k === 'tsTypes' || k === 'input' || k === 'src') continue
          walk(p.initializer, sub, `${path}${key(k)}`, k === 'actions' || k === 'entry' || k === 'exit' ? 'actions' : k === 'guard' || k === 'cond' ? 'guard' : undefined)
        }
      } else if (ts.isArrayLiteralExpression(ast) && Array.isArray(rt)) ast.elements.forEach((el, i) => walk(el, rt[i], `${path}[${i}]`, role))
    }
    walk(config, m0.config, `${machineName}.config`)
    if (inlineActions.length || inlineGuards.length) notes.push(`${inlineActions.length} inline actions and ${inlineGuards.length} inline guards, each given by its place in the config`)
    // A write of another kind than its field's, or unread: as a failure.
    const fits = (f: Field, x: V): string | undefined => {
      const target = f.var ?? f.maybe!.inner, scalar = (y: V) => (target.sort.k === 'num' ? y.t === 'num' : target.sort.k === 'bool' ? y.t === 'bool' : y.t === 'choice' || y.t === 'str')
      if (x.t === 'opaque') return x.what
      if (!f.maybe) return x.t === 'undef' || x.t === 'opt' ? `a value that may be missing, written to ${f.k}` : scalar(x) ? undefined : `a ${x.t} written to ${f.k}`
      if (x.t === 'undef') return !!x.null === f.maybe.null ? undefined : `${x.null ? 'null' : 'undefined'} written to ${f.k}, where its type says ${f.maybe.null ? 'null' : 'undefined'}`
      if (x.t === 'opt') return !!x.null !== f.maybe.null && !(x.has.op === 'const' && x.has.v) ? `a value missing as ${x.null ? 'null' : 'undefined'} written to ${f.k}` : scalar(x.v) ? undefined : `a ${x.v.t} written to ${f.k}`
      return scalar(x) ? undefined : `a ${x.t} written to ${f.k}`
    }
    const everyWrite = [...actions, ...inlineActions].flatMap(([, ws]) => ws ?? [])
    for (const w of everyWrite) { const f = fields.find(x => x.k === w.k)!; if (!f.dropped && w.x && !w.failed) { const why = fits(f, w.x); if (why) { w.failed = why; delete w.x } } }
    // The names a term reads (a field by its own name, a maybe's by its parts').
    const namesOf = (x: V | B, out = new Set<string>()): Set<string> => {
      if ('op' in x) { I.varsOf(x as B, out); return out }
      if (x.t === 'num' || x.t === 'bool' || x.t === 'choice' || x.t === 'str') I.varsOf(x.e as never, out)
      else if (x.t === 'opt') { I.varsOf(x.has, out); namesOf(x.v, out) }
      return out
    }
    const reads = (k: string, ws: Write[]) => {
      const names = new Set<string>()
      for (const [, g] of [...guards, ...inlineGuards]) if (!('in' in g)) namesOf(g, names)
      for (const w of ws) if (w.x && w.k !== k) namesOf(w.x, names)
      return [...names].some(n => n === k || n.startsWith(`${k}.`))
    }
    for (const f of fields) {
      const bad = everyWrite.find(w => w.k === f.k && w.failed)
      if (!bad || f.dropped) continue
      if (reads(f.k, everyWrite.filter(w => !fields.find(g => g.k === w.k)!.dropped))) throw new Refusal(file, `the context's ${f.k} is read, and written from what the subset doesn't read (${bad.failed})`)
      f.dropped = `written from what the subset doesn't read (${bad.failed})`
    }
    // A field left out must be read by nothing kept: a guard, or a write to a field kept.
    for (const f of fields) if (f.dropped) notes.push(`the context's ${f.k} (${f.dropped}) is left out: no guard reads it, nor any write the chart keeps (it reaches only the actors and effects outside)`)
    const kept = (k: string) => !fields.find(f => f.k === k)!.dropped
    // Which context numbers are naturals: as a rule's state, each written by every use of an action that writes it,
    // under its transition's guard (an action no transition names, or an entry or exit action, without one).
    const writesOf = new Map<string, Write[] | null>([...actions.map(([n, ws]) => [`named:${n}`, ws] as const), ...inlineActions])
    const guardOfKey = new Map<string, B | {in: string}>([...guards.map(([n, g]) => [`named:${n}`, g] as const), ...inlineGuards])
    const used = new Set(uses.map(u => u.action))
    const all: {action: string, guard?: string}[] = [...uses, ...[...writesOf.keys()].filter(k => !used.has(k)).map(action => ({action}))]
    const num = (x: V): I.N | undefined => (x.t === 'num' ? x.e : x.t === 'opt' && x.v.t === 'num' ? x.v.e : undefined)
    const writes: Record<string, Term> = {}
    all.forEach((u, i) => {
      for (const w of writesOf.get(u.action) ?? []) {
        const f = fields.find(x => x.k === w.k)!, name = f.var?.name ?? f.maybe?.inner.name, t = w.x && !f.dropped ? num(w.x) : undefined
        if (!name || t === undefined) continue
        const g = u.guard ? guardOfKey.get(u.guard) : undefined, under = g && !('in' in g) ? I.nite(g, t, I.nvar(name)) : t
        const prev = writes[name]
        writes[name] = {s: 'num', e: I.nite(I.bvar(`$use${i}`), under, prev && prev.s === 'num' ? prev.e : I.nvar(name))}
      }
    })
    const init0: Record<string, Term> = {}
    for (const f of fields) {
      const x = f.var ?? f.maybe?.inner
      if (!x || x.sort.k !== 'num') continue
      const val = (raw0 as Obj | undefined)?.[f.k]
      if (ctxArg) continue
      init0[x.name] = {s: 'num', e: I.num(typeof val === 'number' ? val : 0)}
    }
    const vars = [...s.vars.values()]
    const params: Var[] = ctxArg ? fields.filter(f => !f.dropped).flatMap(f => (f.var ? [{...f.var, name: `${f.k}0`, role: 'param' as const}] : [{...f.maybe!.inner, name: `${f.k}0`, role: 'param' as const}])) : []
    const model: Model = {name: opts.entry, shape: 'reducer', file, entry: opts.entry, params, inputs: vars.filter(x => x.role === 'input' && x.name !== 'event'), state: vars.filter(x => x.role === 'state'), maps: [],
      init: init0, writes, mapWrites: {}, outputs: [], refuse: I.F, pre: I.T, layout: {k: 'rec', fields: []}, events: [], notes: [], hints: s.hints}
    const {sorts, notes: sn} = sortsOf(model)
    notes.push(...sn)
    if (ctxArg) for (const f of fields) { const x = f.var ?? f.maybe?.inner; if (x?.sort.k === 'num') { sorts.set(`${f.k}0`, sorts.get(x.name) === 'nat' ? 'nat' : 'int'); if (sorts.get(x.name) === 'int') sorts.set(x.name, 'int') } }
    const P: Printer = {sorts, m: model, hoisted: new Map(), choiceVars: new Map([[events.join('\u0000'), 'event']])}
    for (const f of fields) if (f.var?.sort.k === 'choice') P.choiceVars.set(f.var.sort.values.join('\u0000'), f.var.name)
    const cx = () => ({m: model, sorts, atoms: [] as B[]})
    const envOf = (...xs: object[]) => { const vs = new Set<string>(); for (const x of xs) I.varsOf(x as never, vs); const names = [...new Set([...vs].map(n => n.split('.')[0]!))]; return names.length ? `{${names.join(', ')}}` : '' }
    // A field's kind and a value written to it, as the chart's builders take them.
    const kindOfField = (f: Field): string => {
      const x = f.var ?? f.maybe!.inner, k = kindOf(x, sorts)
      return f.maybe ? `maybe(${k})` : k
    }
    const valueOfWrite = (f: Field, x: V, at: string): {text: string, terms: object[]} => {
      if (x.t === 'opaque') throw new Refusal(file, `${at}: ${x.what}`)
      const one = (y: V): {text: string, terms: object[]} => {
        const target = f.var ?? f.maybe!.inner
        const t: Term | undefined = y.t === 'num' ? {s: 'num', e: y.e} : y.t === 'bool' ? {s: 'bool', e: y.e} : y.t === 'choice' ? {s: 'choice', e: y.e} : y.t === 'str' ? {s: 'str', e: y.e} : undefined
        if (!t || (target.sort.k === 'num') !== (t.s === 'num') || (target.sort.k === 'bool') !== (t.s === 'bool')) throw new Refusal(file, `${at} writes ${f.k} a ${y.t}`)
        if (target.sort.k === 'choice' && t.s === 'str') { const e = ex.asChoice(y, target.sort.values, sf); return {text: pterm({s: 'choice', e}, P, cx(), target.name), terms: [e]} }
        return {text: pterm(t, P, cx(), target.name), terms: [t.e]}
      }
      if (!f.maybe) {
        if (x.t === 'undef' || x.t === 'opt') throw new Refusal(file, `${at} writes ${f.k} a value that may be missing`)
        return one(x)
      }
      // A maybe is written whole: optional(there, value); missing, with any value of its kind (its own, as it is).
      if (x.t === 'undef') { if (!!x.null !== f.maybe.null) throw new Refusal(file, `${at} writes ${f.k} ${x.null ? 'null' : 'undefined'}, where its type says ${f.maybe.null ? 'null' : 'undefined'}`); return {text: `optional(no, ${f.k}.inner)`, terms: [I.nvar(`${f.k}.inner`)]} }
      if (x.t === 'opt') {
        if (!!x.null !== f.maybe.null && !(x.has.op === 'const' && x.has.v)) throw new Refusal(file, `${at} writes ${f.k} a value missing as ${x.null ? 'null' : 'undefined'}, where its type says ${f.maybe.null ? 'null' : 'undefined'}`)
        const inner = one(x.v)
        return {text: `optional(${pb(x.has, P, cx())}, ${inner.text})`, terms: [x.has, ...inner.terms]}
      }
      const inner = one(x)
      return {text: `optional(yes, ${inner.text})`, terms: inner.terms}
    }
    const actionSrc = (ws: Write[] | null, name: string) => {
      if (!ws) return 'null'
      const out = ws.filter(w => kept(w.k)).map(w => {
        const f = fields.find(x => x.k === w.k)!
        if (!w.x) throw new Refusal(file, `the action ${name} writes ${w.k}: ${w.failed}`)
        // A write of a field to itself (a spread of the context): no write.
        if (f.var && (w.x.t === 'num' || w.x.t === 'bool' || w.x.t === 'choice' || w.x.t === 'str') && w.x.e.op === (f.var.sort.k === 'str' ? 'svar' : 'var') && (w.x.e as {name: string}).name === f.var.name) return undefined
        return [w.k, valueOfWrite(f, w.x, `the action ${name}`)] as const
      }).filter((x): x is readonly [string, {text: string, terms: object[]}] => !!x)
      return out.length ? `(${envOf(...out.flatMap(([, x]) => x.terms))}) => ({${out.map(([k, x]) => `${k}: ${x.text}`).join(', ')}})` : 'null'
    }
    const guardSrc = (g: B | {in: string}) => ('in' in g ? `env => env.in(${JSON.stringify(g.in)})` : `(${envOf(g)}) => ${pb(g, P, cx())}`)
    // The bridge fromXState takes.
    const parts: string[] = []
    if (params.length) parts.push(`params: {${params.map(x => `${x.name}: ${kindOfField(fields.find(f => `${f.k}0` === x.name)!)}`).join(', ')}}`)
    const inputsAt = parts.length
    const ctxParts = fields.filter(f => !f.dropped).flatMap(f => {
      const x = f.var ?? f.maybe!.inner
      if (ctxArg) return [`${f.k}: ${kindOfField(f)}.from(({${f.k}0}) => ${f.k}0)`]
      const val = (raw0 as Obj | undefined)?.[f.k]
      const plainNat = !f.maybe && x.sort.k === 'num' && sorts.get(x.name) === 'nat'
      if (plainNat || (!f.maybe && x.sort.k === 'bool')) return []
      return [`${f.k}: ${kindOfField(f)}.from(${val === undefined ? 'null' : JSON.stringify(val)})`]
    })
    if (ctxParts.length) parts.push(`context: {${ctxParts.join(', ')}}`)
    const dropped = fields.filter(f => f.dropped).map(f => f.k)
    if (dropped.length) parts.push(`ignore: ${JSON.stringify(dropped)}`)
    if (events.length > handled.length) parts.push(`events: ${JSON.stringify(events)}`)
    if (guards.length) parts.push(`guards: {${guards.map(([n, g]) => `${JSON.stringify(n)}: ${guardSrc(g)}`).join(', ')}}`)
    if (actions.length) parts.push(`actions: {${actions.map(([n, ws]) => `${JSON.stringify(n)}: ${actionSrc(ws, n)}`).join(', ')}}`)
    if (inlineGuards.length || inlineActions.length) parts.push(`inline: {${[inlineGuards.length ? `guards: new Map([${inlineGuards.map(([p, g]) => `[${p}, ${guardSrc(g)}]`).join(', ')}])` : '', inlineActions.length ? `actions: new Map([${inlineActions.map(([p, ws]) => `[${p}, ${actionSrc(ws, p)}]`).join(', ')}])` : ''].filter(Boolean).join(', ')}}`)
    // The inputs: those the guards and the writes kept read.
    const usedNames = new Set<string>()
    for (const [, g] of [...guards, ...inlineGuards]) if (!('in' in g)) namesOf(g, usedNames)
    for (const w of everyWrite) if (w.x && kept(w.k)) namesOf(w.x, usedNames)
    const inputs = model.inputs.filter(x => usedNames.has(x.name))
    if (inputs.length) parts.splice(inputsAt, 0, `inputs: {${inputs.map(x => `${x.name}: ${kindOf(x, sorts)}`).join(', ')}}`)
    const bridge = `{${parts.join(', ')}}`
    const builders = ['bool', 'int', 'nat', 'oneOf', 'str', 'maybe', 'optional', 'when', 'all', 'any', 'not', 'min', 'max', 'lit', 'Int', 'yes', 'no', 'intern'].filter(n => new RegExp(`\\b${n}\\b`).test(bridge.replace(/'[^']*'|"[^"]*"/g, '')))
    const makes = factory ? `${opts.entry}(${(factory.parameters).map(() => '{} as never').join(', ')})` : opts.entry
    const source = [
      `// Extracted by gdp-wired/extract from ${file} (${opts.entry}, ${factory ? 'a function that makes an XState machine' : 'an XState machine'}): its guards and actions read from the code.`,
      `// Checked against XState's own actor; read again with extractXState() after the code changes.`,
      `import {fromXState} from 'gdp-wired/xstate'`,
      ...(builders.length ? [`import {${builders.join(', ')}} from 'gdp-wired'`] : []),
      `import {${opts.entry}} from './${file.replace(/\.(ts|js|tsx|jsx)$/, '')}'`,
      '',
      ...(factory ? [`// The machine's states and transitions are the same whatever it is given (the functions are its inputs, the context its params).`, `const machine = ${makes}`] : []),
      `export const ${opts.entry}Chart = fromXState(${machineName}, ${bridge})`,
      '',
    ].join('\n')
    const NAMES = ['nat', 'int', 'bool', 'oneOf', 'str', 'maybe', 'optional', 'when', 'min', 'max', 'all', 'any', 'not', 'yes', 'no', 'lit', 'Int', 'intern'] as const
    // fromXState's own refusals (what a chart can't run the same way), with its reason.
    let chart: ReturnType<typeof fromXState>
    try {
      chart = compileFunction<(...xs: unknown[]) => ReturnType<typeof fromXState>>([...NAMES, 'fromXState', machineName], `return fromXState(${machineName}, ${bridge})`)(...NAMES.map(n => (dsl as Record<string, unknown>)[n]), fromXState, m0)
      void chart.rule.machine
    } catch (e) { if (e instanceof Refusal) throw e; return {ok: false, source, refusals: [{where: file, what: `fromXState: ${(e as Error).message}`}], notes} }

    // The check: XState's actor (its actors inert: their answers are events the run sends) and the chart's compiled
    // rule on the same events, payloads drawn for every input read; for a factory's context, a start drawn per batch.
    const rand = seeded(opts.check?.seed ?? 3)
    const draw = (x: Var, name = x.name): unknown => (x.sort.k === 'bool' ? rand(2) === 1 : x.sort.k === 'choice' ? x.sort.values[rand(x.sort.values.length)] : x.sort.k === 'str' ? ['a', 'b', ''][rand(3)] : sorts.get(name) === 'nat' ? rand(12) : rand(25) - 12)
    const xs = opts.xstate as Obj
    const inert = (m: Obj): Obj => (v === 5
      ? m.provide({actors: Object.fromEntries(Object.keys(m.implementations?.actors ?? {}).map(k => [k, xs.fromCallback(() => {})]))})
      : m.withConfig({services: Object.fromEntries(Object.keys(m.options?.services ?? {}).map(k => [k, () => () => {}]))}))
    const createActor = (m: never) => (v === 5 ? (xs.createActor as (m: never) => never)(m) : (xs.interpret as (m: never) => never)(m))
    const outside = s.xstate!.outside
    // The event XState is sent: the payload's fields by the names the code reads them by; a field the code reads only
    // into what the chart leaves out, an inert value (an object answering every read, a call, a conversion), so the
    // code runs as it would with whatever the world sends there.
    const anything: unknown = new Proxy(function inert() {}, {get: (_, k) => (k === Symbol.toPrimitive ? () => 0 : k === 'then' ? undefined : anything), apply: () => anything})
    const toEvent = (type: string, payload: Obj): Obj => {
      const e: Obj = {type}
      for (const [n, l] of s.lazy) if (l.prefix === '' && l.field !== 'type') e[l.field] = n in payload ? payload[n] : anything
      return e
    }
    const runs = opts.check?.runs ?? 200, depth = opts.check?.depth ?? 16, batches = ctxArg ? Math.min(runs, 50) : 1
    const keptKeys = fields.filter(f => !f.dropped).map(f => f.k)
    let result: {checked: number, failure?: string} = {checked: 0}
    for (let b = 0; b < batches && !result.failure; b++) {
      const ps: Obj = {}, ctx: Obj = {}
      if (ctxArg) for (const f of fields) {
        if (f.dropped) { ctx[f.k] = undefined; continue }
        const x = f.var ?? f.maybe!.inner, val = f.maybe && rand(3) === 0 ? null : draw(x)
        ps[`${f.k}0`] = val; ctx[f.k] = val === null && f.maybe && !f.maybe.null ? undefined : val
      }
      let machine: Obj
      try { machine = inert(instance(ctxArg ? ctx : undefined)) } catch (e) { if (e instanceof Refusal) throw e; result = {checked: 0, failure: `the machine can't be made: ${(e as Error).message}`}; break }
      try {
        const r = conforms(chart as never, machine as never, createActor as never, {runs: Math.ceil(runs / batches), depth, seed: (opts.check?.seed ?? 3) + b, params: ps, context: keptKeys,
          payload: () => Object.fromEntries(inputs.map(x => [x.name, draw(x)])),
          beforeSend: (_, payload) => { for (const [n, o] of outside) answers[o.path] = payload[n] },
          event: toEvent})
        result = {checked: result.checked + r.checked, ...(r.failure ? {failure: `${ctxArg ? `starting at ${JSON.stringify(ps)}: ` : ''}${r.failure}`} : {})}
      } catch (e) { result = {checked: result.checked, failure: `the chart's run throws: ${(e as Error).message}`} }
    }
    // The arms of the code the chart reads: its guards' and actions' (what the actors and effects outside run isn't).
    const counted = box.arms.map((a, i) => [a, i] as const).filter(([a]) => (s.spans ?? []).some(([s0, e0]) => a.pos >= s0 && a.pos < e0))
    const coverage: Coverage = {arms: counted.length, hit: counted.filter(([, i]) => box.counts[i]! > 0).length, missed: counted.filter(([, i]) => box.counts[i] === 0).map(([a]) => `${a.label} at ${a.where}`)}
    const evidence = {runs, events: result.checked, coverage, ms: Math.round(performance.now() - t0), ...(result.failure ? {mismatch: result.failure} : {})}
    notes.push(...s.notes)
    if (result.failure) return {ok: false, source, evidence, notes, refusals: [{where: file, what: `the chart and XState differ: ${result.failure}`}]}
    // (the names: the state as XState's snapshot.value, each region's as value.<region>, the context's fields, the
    // factory's context as <field>0, the event and its payload's fields, the answers of the functions it is given)
    const field = (n: string) => [...s.lazy].find(([k, l]) => k === n && l.prefix === '')?.[1].field ?? n
    const names0: Name[] = [...Object.keys(chart.rule.machine.state).filter(k => !k.includes('.last') && !keptKeys.some(c => k === c || k.startsWith(`${c}$`) || k.startsWith(`${c}.`))).map(k => ({code: k === 'state' ? 'value' : `value.${k}`, rule: k, role: 'state' as const})),
      ...fields.filter(f => !f.dropped && f.var).map(f => ({code: f.k, rule: f.k, role: 'state' as const})), ...params.map(x => ({code: x.name, rule: x.name, role: 'param' as const})),
      ...inputs.map(x => (outside.has(x.name) ? {code: outside.get(x.name)!.path, rule: x.name, role: 'answer' as const} : {code: `event.${field(x.name)}`, rule: x.name, role: 'input' as const})), {code: 'event', rule: 'event', role: 'method'}]
    return {ok: true, source, chart, rule: chart.rule as unknown as Rule, invariants: chart.chartLaws(), names: names0, evidence, notes, refusals: []}
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
}
