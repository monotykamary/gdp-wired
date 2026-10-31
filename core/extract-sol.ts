// The extractor's Solidity front end (`gdp-wired/extract-sol`): a contract read through solc's own AST (`solc
// --standard-json`, the compact JSON AST), lowered here into the shared step IR (core/extract-step.ts), executed by the
// shared step executor, printed, built and checked as every front end's rule is. The check deploys the contract's own
// bytecode, compiled by the same solc, on foundry's anvil and runs it through core/sol/harness.py (JSON-RPC, the
// standard library only): every state, cell, result and revert compared.
//
//   const x = extractSolidity('contracts/mocks/token/ERC20Mock.sol', {root: '.'})   // the contract inferred
//
// What the rule is of the contract (the boundary, printed in every extraction's notes):
// - A step is one external call: its function's body with the modifiers it names, the base contracts' functions it
//   calls inlined (virtual ones resolved along the linearization). A revert, require, assert or custom error is the
//   step's refusal (the transaction reverts: nothing it wrote stays). msg.sender is an input of every request,
//   msg.value of a payable one (0 elsewhere), block.timestamp the request's time.
// - Integers: uint256 is exact past the rule's 2^53 by a width variable (`W256$`, a state variable no step writes,
//   any value at least 2 above the code's constants): a value is below it, a checked operation past it reverts, an
//   unchecked one wraps by cases (a sum or a difference once; a product wrapped is refused). A law proven for every
//   such width is proven for 2^256. uintN and intN below 2^48 are exact; other widths are refused where read.
// - Addresses are naturals below 2^26 compared only by equality (the code is symmetric in them; address(0) is 0): the
//   claim is for runs among fewer than 2^26 accounts. A mapping is a map with Solidity's zero for a key never set (a
//   cell is held where it isn't zero); a mapping of mappings keyed by two addresses is one map keyed by a·2^26 + b.
// - The contract's ether is the state's `balance`: a payable call adds msg.value; a value call to an address
//   (`a.call{value: v}("")`, `send`, `transfer`) moves it where it is there. The address called is an account without
//   code (it accepts and calls nothing back): `reentrant: true` (core/extract-reenter.ts) makes it any code instead.
// - Left out, each where it is read with why: strings and bytes (their state too), loops, arrays, structs past a
//   mapping's value, calls of other contracts, inline assembly, try/catch, constants past 2^53, signed widths past 48.
import {type Extraction, type Name, fromModel} from './extract.ts'
import type {Rule} from './dsl.ts'
import {type Request, evalC, interpret, seeded} from './machine.ts'
import {allowed, watch} from './watch.ts'
import {kindOfVar} from './extract-check.ts'
import type {Sorts} from './extract-print.ts'
import type {Model} from './extract-read.ts'
import {Refusal, pathOf, type FileURL} from './extract-read.ts'
const refuse = (where: string, what: string): never => { throw new Refusal(where, what) }
import {type Harness, type SFunc, type SModule, type SParam, type SRec, type SS, type SType, type SX, type StepOptions, type StepRead, checkStep, node, readStep, stepNames} from './extract-step.ts'
export {proveRule, proveSteps} from './dsl.ts'

export type SolOptions = StepOptions & {
  // The project root solc resolves imports from (by default the file's directory), and remappings
  // (`@openzeppelin/=lib/openzeppelin-contracts/`).
  root?: string, remappings?: string[],
  // false: an address called is an account without code (the rule's steps are whole calls); by default it is any code,
  // which may call back before the call returns (core's re-entrancy: each such entry split at its call).
  reentrant?: boolean,
  // solc, anvil and python3 (by default on the PATH; $GDP_SOLC, $GDP_ANVIL).
  solc?: string, anvil?: string, python?: string,
}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
type FS = {readFileSync: (p: string, e: string) => string, existsSync: (p: string) => boolean}
type PathM = {resolve: (...p: string[]) => string, dirname: (p: string) => string, relative: (a: string, b: string) => string}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type Ast = {nodeType: string, id: number, src: string, [k: string]: any}

// (addresses: naturals below 2^19, a mapping of mappings pairing two of them into one key, a·2^19 + b; the rule's
// runtimes write a map at every key, a transfer's two cells, only below a million)
export const MOD = 'W256$', PAIR_BITS = 19
// (the width the check runs the rule at: past 2^256's half the code's values are the rule's near W)
const CHECK_W = 2 ** 52
const U256: SType = {k: 'int', bits: 256, signed: false, mod: MOD}
const env = () => (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env ?? {}

// --- solc -------------------------------------------------------------------------------------------------------------
export type Compiled = {main: number, ast: Map<number, Ast>, text: Map<number, string>, paths: Map<number, string>, contracts: Record<string, Record<string, {abi: unknown[], evm: {bytecode: {object: string}, deployedBytecode: {object: string}, methodIdentifiers: Record<string, string>}, storageLayout: {storage: {label: string, slot: string, offset: number, type: string}[], types: Record<string, {encoding: string, numberOfBytes: string, key?: string, value?: string, label: string}>}}>>}
export function compile(file: string, o: SolOptions): Compiled {
  const cp = node<CP>('node:child_process'), fs = node<FS>('node:fs'), path = node<PathM>('node:path')
  const root = path.resolve(o.root ?? path.dirname(file)), rel = path.relative(root, path.resolve(file))
  const input = {language: 'Solidity', sources: {[rel]: {content: fs.readFileSync(file, 'utf8')}},
    settings: {remappings: o.remappings ?? [], optimizer: {enabled: false}, outputSelection: {'*': {'': ['ast'], '*': ['abi', 'evm.bytecode.object', 'evm.deployedBytecode.object', 'evm.methodIdentifiers', 'storageLayout']}}}}
  let out: string
  const solc = o.solc ?? env().GDP_SOLC ?? 'solc'
  try { out = cp.execFileSync(solc, ['--standard-json', '--base-path', root, '--include-path', `${root}/node_modules`, '--allow-paths', root], {input: JSON.stringify(input), encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['pipe', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(file, `solc didn't run (${String((e as Error).message).slice(0, 300)}): solc 0.8 is needed to extract Solidity (on the PATH, or $GDP_SOLC)`) }
  const j = JSON.parse(out) as {errors?: {severity: string, formattedMessage: string}[], sources: Record<string, {id: number, ast: Ast}>, contracts: Compiled['contracts']}
  const errs = (j.errors ?? []).filter(e => e.severity === 'error')
  if (errs.length) throw new Refusal(file, `solc: ${errs.map(e => e.formattedMessage.split('\n')[0]).join(' | ').slice(0, 600)}`)
  const ast = new Map<number, Ast>(), text = new Map<number, string>(), paths = new Map<number, string>()
  let main = -1
  for (const [p, s] of Object.entries(j.sources)) {
    if (p === rel) main = s.id
    ast.set(s.id, s.ast); paths.set(s.id, p)
    const abs = p === rel ? path.resolve(file) : [path.resolve(root, p), path.resolve(root, 'node_modules', p)].find(x => fs.existsSync(x))
    text.set(s.id, abs ? fs.readFileSync(abs, 'utf8') : '')
  }
  return {main, ast, text, paths, contracts: j.contracts}
}

// --- the lowering -------------------------------------------------------------------------------------------------------
type Field = {name: string, t: SType, decl: Ast, sol: string}
export type SolMeta = {calls: boolean, resumes: string[], addrBits: number, contract: string, source: string, fields: Field[], fns: Record<string, Ast>, payable: string[], minW: number, nested: string[], entries: Record<string, {sig: string, inputs: string[], payable: boolean, out?: string}>, ctor: {inputs: string[], payable: boolean}, ether: boolean}

class Lower {
  readonly defs = new Map<number, Ast>()
  readonly funcs: Record<string, SFunc> = {}
  readonly fields: Field[] = []
  readonly consts = new Map<number, SX>()
  minW = 2
  addrBits = PAIR_BITS
  get ADDR(): SType { return {k: 'int', bits: this.addrBits, signed: false} }
  unchecked = false
  ether = false
  nested = new Set<string>()
  lin: Ast[] = []
  // (the function being lowered: whether it is an entry, payable; its return locals)
  cur: {entry: boolean, payable: boolean, rets: string[], tmp: number} = {entry: false, payable: false, rets: [], tmp: 0}
  // (reenter: an address called is any code, which may call back into the contract before the call returns)
  readonly frames: SRec[] = []
  constructor(readonly c: Compiled, readonly file: string, readonly reenter = false) {
    const walk = (n: unknown) => {
      if (Array.isArray(n)) { n.forEach(walk); return }
      if (!n || typeof n !== 'object') return
      const a = n as Ast
      if (typeof a.id === 'number' && typeof a.nodeType === 'string') this.defs.set(a.id, a)
      for (const v of Object.values(a)) if (v && typeof v === 'object') walk(v)
    }
    for (const a of c.ast.values()) walk(a)
  }
  // `file:line:col` of a node.
  at(n: Ast): string {
    const [s, , f] = String(n.src).split(':').map(Number), t = this.c.text.get(f!) ?? ''
    const before = t.slice(0, s), line = before.split('\n').length, col = s! - before.lastIndexOf('\n')
    return `${(this.c.paths.get(f!) ?? this.file).split('/').pop()}:${line}:${col}`
  }
  text(n: Ast): string { const [s, l, f] = String(n.src).split(':').map(Number); return (this.c.text.get(f!) ?? '').slice(s, s! + l!).replace(/\s+/g, ' ').slice(0, 120) }
  no(n: Ast, why: string): never { throw new Refusal(this.at(n), `${this.text(n)}: ${why}`) }

  // A type's SType by solc's type string (where the subset reads it).
  ty(ts: string, n: Ast): SType {
    const s = ts.replace(/ (storage|memory|calldata)( ref| pointer)?$/, '')
    if (s === 'uint256') return U256
    if (s === 'bool') return {k: 'bool'}
    if (s === 'address' || s === 'address payable') return this.ADDR
    let m = /^uint(\d+)$/.exec(s)
    if (m && Number(m[1]) <= 48) return {k: 'int', bits: Number(m[1]), signed: false}
    m = /^int(\d+)$/.exec(s)
    if (m && Number(m[1]) <= 48) return {k: 'int', bits: Number(m[1]), signed: true}
    m = /^enum (.+)$/.exec(s)
    if (m) { const d = this.byName('EnumDefinition', m[1]!.split('.').pop()!); if (d) return {k: 'choice', values: d.members.map((x: Ast) => x.name)} }
    if (s.startsWith('mapping(')) return this.mapTy(s, n)
    if (/^(int_const|rational_const)/.test(s)) return {k: 'int'}
    return {k: 'opaque', why: `a ${s} (outside the Solidity subset)`}
  }
  byName(kind: string, name: string): Ast | undefined { for (const d of this.defs.values()) if (d.nodeType === kind && d.name === name) return d; return undefined }
  // mapping(K => V), and mapping(K1 => mapping(K2 => V)) as one map keyed by K1·2^26 + K2 (both below 2^26).
  mapTy(s: string, n: Ast): SType {
    const inner = s.slice('mapping('.length, -1), arrow = topArrow(inner)
    const k = this.ty(inner.slice(0, arrow).trim(), n), v = inner.slice(arrow + 2).trim()
    const small = (t: SType) => t.k === 'int' && t.bits !== undefined && t.bits > 0 && t.bits <= PAIR_BITS && !t.signed
    if (!(k.k === 'int' && !k.signed)) return {k: 'opaque', why: `a mapping keyed by ${inner.slice(0, arrow).trim()}`}
    if (v.startsWith('mapping(')) {
      const vv = v.slice('mapping('.length, -1), a2 = topArrow(vv), k2 = this.ty(vv.slice(0, a2).trim(), n), val = this.ty(vv.slice(a2 + 2).trim(), n)
      if (!small(k) || !small(k2)) return {k: 'opaque', why: 'a mapping of mappings not keyed by two addresses (or two small numbers)'}
      if (!scalarT(val)) return {k: 'opaque', why: `a mapping of mappings of ${vv.slice(a2 + 2).trim()}`}
      return {k: 'map', key: {k: 'int'}, val, nested: true} as SType
    }
    const val = this.ty(v, n)
    if (!scalarT(val)) return {k: 'opaque', why: `a mapping of ${v}`}
    return {k: 'map', key: k.k === 'int' && k.mod ? {k: 'int'} : k, val}
  }

  // The contract: its linearized bases, state, functions.
  module(name: string | undefined): {mod: SModule, meta: SolMeta} {
    const contracts = [...this.defs.values()].filter(d => d.nodeType === 'ContractDefinition')
    const main = this.c.ast.get(this.c.main)
    const own = contracts.filter(d => main && (main.nodes as Ast[]).includes(d))
    const cands = (name ? contracts.filter(d => d.name === name) : own.filter(d => d.contractKind === 'contract' && !d.abstract))
    if (cands.length !== 1) throw new Refusal(this.file, name ? `no contract ${name}` : cands.length ? `several contracts (${cands.map(d => d.name).join(', ')}): name one (entry)` : 'no contract that isn\'t abstract in the file (name one: entry)')
    const k = cands[0]!
    if (k.contractKind !== 'contract' || k.abstract) throw new Refusal(this.at(k), `${k.name}: a${k.abstract ? 'n abstract contract' : ` ${k.contractKind}`} (the subset reads a contract that is deployed)`)
    this.lin = (k.linearizedBaseContracts as number[]).map(id => this.defs.get(id)!)
    // The state: every base's variables, base first (storage order); constants inlined.
    for (const c of [...this.lin].reverse()) for (const n of c.nodes as Ast[]) {
      if (n.nodeType !== 'VariableDeclaration') continue
      if (n.constant) { const v = n.value as Ast | undefined; if (!v) this.no(n, 'a constant with no value'); this.consts.set(n.id, this.ex(v!)); continue }
      if (n.mutability === 'immutable') this.no(n, 'an immutable (not yet)')
      if (n.name === 'balance' || n.name === MOD) this.no(n, `a state variable named ${n.name} (the rule's own name for the contract's ether, or its width)`)
      this.fields.push({name: n.name, t: this.ty(n.typeDescriptions.typeString, n), decl: n, sol: n.typeDescriptions.typeString})
    }
    // The functions: every base's, a virtual one resolved to the most derived override.
    const fns: Record<string, Ast> = {}
    const entries: SolMeta['entries'] = {}
    const methods: Record<string, string | null> = {}
    for (const c of this.lin) for (const f of c.nodes as Ast[]) {
      if (f.nodeType !== 'FunctionDefinition' || !f.body) continue
      if (f.kind === 'constructor') continue
      const id = this.fnId(f)
      if (this.funcs[id]) continue
      const pub = f.visibility === 'public' || f.visibility === 'external'
      const name = f.kind === 'receive' ? 'receive' : f.kind === 'fallback' ? 'fallback' : f.name as string
      if (pub && f.stateMutability !== 'view' && f.stateMutability !== 'pure') {
        if (methods[name]) this.no(f, `${name}: an overloaded external function (the subset reads one of a name)`)
        methods[name] = `entry:${id}`
        const inputs = (f.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString as string)
        const outs = (f.returnParameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString as string)
        entries[name] = {sig: `${f.name}(${(f.parameters.parameters as Ast[]).map(x => abiType(x.typeDescriptions.typeString)).join(',')})`, inputs, payable: f.stateMutability === 'payable', ...(outs.length === 1 ? {out: outs[0]} : {})}
      }
      fns[id] = f
    }
    // (lowered where read: the entries now, the functions they call where they call them)
    for (const [id, f] of Object.entries(fns)) if (Object.values(methods).includes(`entry:${id}`)) this.funcs[`entry:${id}`] = this.fn(f, `entry:${id}`, true)
    // The constructor: every base's state initializers and constructor, base first, with the arguments given to it.
    const init = this.ctor(k)
    for (const fr of this.frames) { const n = fr.name.slice('Frame$'.length); methods[`${n}$resume`] = `entry:${Object.keys(fns).find(i => methods[n] === `entry:${i}`)}$resume` }
    const rec: SRec = {name: k.name, short: k.name, fields: [...this.fields.map(f => ({name: f.name, t: f.t})), {name: MOD, t: {k: 'int'}}, ...(this.ether ? [{name: 'balance', t: U256}] : []),
      ...this.frames.map(fr => ({name: `frames$${fr.name.slice('Frame$'.length)}`, t: {k: 'map', key: {k: 'int'}, val: {k: 'rec', name: fr.name}} as SType})), ...(this.frames.length ? [{name: 'pending$', t: {k: 'int'} as SType}] : [])],
      methods: {__init__: '__init__', ...methods}, kinds: [], own: true, module: k.name, p: this.at(k)}
    this.funcs.__init__ = init
    const ctorDef = this.lin[0]!.nodes.find((n: Ast) => n.nodeType === 'FunctionDefinition' && n.kind === 'constructor') as Ast | undefined
    const meta: SolMeta = {calls: this.calls, resumes: this.frames.map(fr => `${fr.name.slice('Frame$'.length)}$resume`), addrBits: this.addrBits, contract: k.name, source: this.c.paths.get(Number(String(k.src).split(':')[2]))!, fields: this.fields, fns, payable: Object.entries(entries).filter(([, e]) => e.payable).map(([n]) => n), minW: this.minW, nested: [...this.nested], entries,
      ctor: {inputs: ctorDef ? (ctorDef.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString as string) : [], payable: ctorDef?.stateMutability === 'payable'}, ether: this.ether}
    const mod: SModule = {lang: 'solidity', file: this.file.split('/').pop()!, path: this.file, module: k.name, root: '', entries: [{k: 'class', rec: k.name}], recs: {[k.name]: rec, ...Object.fromEntries(this.frames.map(fr => [fr.name, fr]))}, funcs: this.funcs}
    return {mod, meta}
  }
  // A function's id: the most derived override of its name and parameter types.
  fnId(f: Ast): string {
    const sig = `${f.name}(${(f.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString).join(',')})`
    for (const c of this.lin) for (const g of c.nodes as Ast[]) if (g.nodeType === 'FunctionDefinition' && g.kind === f.kind && `${g.name}(${(g.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString).join(',')})` === sig && g.body) return `f${g.id}`
    return `f${f.id}`
  }
  // A function: self, msg.sender, msg.value (an entry that isn't payable takes none: 0), then its own parameters.
  fn(f: Ast, id: string, entry: boolean): SFunc {
    const payable = f.stateMutability === 'payable'
    this.cur = {entry, payable, rets: [], tmp: 0}
    const params: SParam[] = [{name: 'self', t: {k: 'rec', name: this.lin[0]!.name}, self: true}, {name: 'msg.sender', t: this.ADDR}, ...(entry && !payable ? [] : [{name: 'msg.value', t: U256}])]
    for (const pa of f.parameters.parameters as Ast[]) params.push({name: pa.name || `_${pa.id}`, t: this.ty(pa.typeDescriptions.typeString, pa)})
    const rets = f.returnParameters.parameters as Ast[]
    if (rets.length > 1) this.no(f, 'several results (the subset reads one)')
    const ret: SType = rets.length ? this.ty(rets[0]!.typeDescriptions.typeString, rets[0]!) : {k: 'none'}
    const body: SS[] = []
    const p = this.at(f)
    if (entry) body.push(senderNonzero(p))
    // (a payable entry: the value is the contract's before its body runs)
    // (the ether there is is below 2^256: a value past it is no request)
    if (entry && payable) { this.ether = true; body.push({s: 'set', p, to: self('balance', p), x: {e: 'bin', op: '+', p, text: 'balance + msg.value', x: self('balance', p), y: {e: 'var', n: 'msg.value', p}, ovf: 'trap', ity: {bits: 256, signed: false, mod: MOD}, trap: 'no ether past 2^256 exists'}}) }
    // (named results: locals from 0, returned at the end)
    for (const r of rets) if (r.name) { this.cur.rets.push(r.name); body.push({s: 'set', p, to: {e: 'var', n: r.name, p}, x: zero(this.ty(r.typeDescriptions.typeString, r), p)}) }
    body.push(...this.withModifiers(f, f.modifiers as Ast[], 0))
    if (this.cur.rets.length) body.push({s: 'ret', p, x: {e: 'var', n: this.cur.rets[0]!, p}})
    const name = f.kind === 'receive' ? 'receive' : f.kind === 'fallback' ? 'fallback' : f.name as string
    if (this.reenter && callsOut(body)) {
      if (!entry) this.no(f, `${name}: a call into other code inside a function an entry calls (the subset splits an entry's own body at it)`)
      return this.split(name, id, params, ret, body, p)
    }
    return {id, name, p, span: [p, 0, 0], params, ret, body, decorators: []}
  }
  // An entry that calls into other code, as two steps: up to the call (the value moved, the call pending: its locals in
  // a frame of the state, `frames$<fn>`, at its depth), and from it (`<fn>$resume`: the frame on top given back, ok
  // whether the callee returned or reverted). Between them any step may run: other code called back. `pending$` is the
  // depth: the calls pending, the last resumed first (as the code's return).
  split(name: string, id: string, params: SParam[], ret: SType, body: SS[], p: string): SFunc {
    const i = body.findIndex(x => x.s === 'callout')
    if (i < 0) return refuse(p, `${name}: a call into other code inside a branch (the subset splits a body at a call at its top)`)
    const mk = body[i]!, pre = body.slice(0, i), rest = body.slice(i + 1)
    if (callsOut(rest)) refuse(p, `${name}: two calls into other code (the subset splits at one)`)
    // The locals the rest may read: the parameters, and every local the part before sets.
    const locals = new Map<string, SType>()
    for (const pa of params) if (!pa.self) locals.set(pa.name, pa.t)
    const scan = (ss: SS[]) => { for (const x of ss) { const to = x.to as SX | undefined; if (x.s === 'set' && to?.e === 'var') { if (!x.t && !locals.has(String(to.n))) refuse(x.p, `${String(to.n)}: a local of no stated type before a call into other code`); if (x.t) locals.set(String(to.n), x.t as SType) } if (x.s === 'if') { scan(x.then as SS[]); scan(x.else as SS[]) } } }
    scan(pre)
    const fld = (n: string) => n.replace(/[^\w]/g, '_')
    const rec: SRec = {name: `Frame$${name}`, short: `Frame$${name}`, fields: [...locals].map(([n, t]) => ({name: fld(n), t})), methods: {}, kinds: ['dataclass'], own: true, module: this.lin[0]!.name, p}
    this.frames.push(rec)
    const M = self(`frames$${name}`, p), D = self('pending$', p), amount = String(mk.amount), ok = String(mk.ok), how = String(mk.how)
    const v = (n: string): SX => ({e: 'var', n, p}), int = (k: number): SX => ({e: 'int', v: k, p})
    const fail = (why: string): SS => ({s: 'fail', p, why})
    const bal = (op: '+' | '-'): SS => ({s: 'set', p, to: self('balance', p), x: {e: 'bin', op, p, text: `balance ${op} value`, x: self('balance', p), y: v(amount)}})
    const begin: SS[] = [...pre, {s: 'if', p, c: {e: 'cmp', op: '<', p, text: 'balance < value', x: self('balance', p), y: v(amount)},
      // (the contract holds less: the call fails at once, and no code runs)
      then: [{s: 'set', p, to: v(ok), x: {e: 'bool', v: false, p}, t: {k: 'bool'}}, ...(how === 'transfer' ? [fail(String(mk.why))] : []), ...rest],
      else: [
        bal('-'),
        {s: 'set', p, to: D, x: {e: 'bin', op: '+', p, text: 'pending$ + 1', x: D, y: int(1)}},
        {s: 'set', p, to: {e: 'idx', p, text: 'frames[pending$]', x: M, i: D}, x: {e: 'new', p, text: rec.name, rec: rec.name, fields: [...locals.keys()].map(n => [fld(n), v(n)])}},
        {s: 'ret', p},
      ]}]
    const f = '$f'
    const resume: SS[] = [
      // (the call on top, this one's: else this is no request, the code returns from the last call first)
      {s: 'if', p, c: {e: 'cmp', op: '<', p, text: 'pending$ < 1', x: D, y: int(1)}, then: [fail('no call pending')], else: []},
      {s: 'set', p, to: v(f), x: {e: 'idx', p, text: 'frames[pending$]', x: M, i: D}},
      ...[...locals.keys()].map((n): SS => ({s: 'set', p, to: v(n), x: {e: 'get', p, text: `$f.${fld(n)}`, x: v(f), f: fld(n)}})),
      {s: 'del', p, x: {e: 'idx', p, text: 'frames[pending$]', x: M, i: D}},
      {s: 'set', p, to: D, x: {e: 'bin', op: '-', p, text: 'pending$ - 1', x: D, y: int(1)}},
      {s: 'set', p, to: v(ok), x: v('$ok'), t: {k: 'bool'}},
      // (the callee reverted: the value is the contract's again; what the callee's own calls did stays, in the rule)
      {s: 'if', p, c: {e: 'not', p, strict: true, text: '!ok', x: v('$ok')}, then: [bal('+'), ...(how === 'transfer' ? [fail(String(mk.why))] : [])], else: []},
      ...rest]
    this.funcs[`${id}$resume`] = {id: `${id}$resume`, name: `${name}$resume`, p, span: [p, 0, 0], params: [{name: 'self', t: {k: 'rec', name: this.lin[0]!.name}, self: true}, {name: '$ok', t: {k: 'bool'}}], ret, body: resume, decorators: []}
    return {id, name, p, span: [p, 0, 0], params, ret, body: begin, decorators: []}
  }
  // A function's body inside its modifiers: each modifier's body, `_;` the next one's (or the function's own).
  withModifiers(f: Ast, mods: Ast[], i: number): SS[] {
    const m = mods.slice(i).find(x => this.defs.get(x.modifierName.referencedDeclaration)?.nodeType === 'ModifierDefinition')
    if (!m) return this.block(f.body)
    const j = mods.indexOf(m), def = this.modDef(this.defs.get(m.modifierName.referencedDeclaration)!)
    const out: SS[] = []
    const args = (m.arguments ?? []) as Ast[]
    ;(def.parameters.parameters as Ast[]).forEach((pa, k) => out.push({s: 'set', p: this.at(m), to: {e: 'var', n: pa.name, p: this.at(m)}, x: this.ex(args[k]!)}))
    const inner = this.withModifiers(f, mods, j + 1), stmts = def.body.statements as Ast[]
    const ph = stmts.findIndex(s => s.nodeType === 'PlaceholderStatement')
    if (stmts.slice(ph + 1).length && hasReturn(inner)) this.no(f, `a return inside ${m.modifierName.name}, which runs code after _ (not yet)`)
    for (const s of stmts) out.push(...(s.nodeType === 'PlaceholderStatement' ? inner : this.stmt(s)))
    return out
  }
  modDef(d: Ast): Ast { for (const c of this.lin) for (const g of c.nodes as Ast[]) if (g.nodeType === 'ModifierDefinition' && g.name === d.name) return g; return d }
  ctor(k: Ast): SFunc {
    const p = this.at(k), body: SS[] = []
    const W = {e: 'var', n: MOD, p}
    // The width: any value above the code's constants (fixed once the code is read: minW).
    body.push(senderNonzero(p), {s: 'set', p, to: self(MOD, p), x: W})
    const ctorOf = (c: Ast) => (c.nodes as Ast[]).find(n => n.nodeType === 'FunctionDefinition' && n.kind === 'constructor')
    const top = ctorOf(k)
    // Arguments each base's constructor is given: in the inheritance list, or as a modifier of a constructor.
    const given = new Map<number, Ast[]>()
    for (const c of this.lin) {
      for (const b of (c.baseContracts ?? []) as Ast[]) if (b.arguments?.length) given.set(b.baseName.referencedDeclaration, b.arguments)
      const cf = ctorOf(c)
      for (const m of (cf?.modifiers ?? []) as Ast[]) if (this.defs.get(m.modifierName.referencedDeclaration)?.nodeType === 'ContractDefinition') given.set(m.modifierName.referencedDeclaration, m.arguments ?? [])
    }
    this.cur = {entry: true, payable: top?.stateMutability === 'payable', rets: [], tmp: 0}
    if (this.cur.payable) this.ether = true
    for (const c of [...this.lin].reverse()) {
      for (const n of c.nodes as Ast[]) {
        if (n.nodeType !== 'VariableDeclaration' || n.constant) continue
        const f = this.fields.find(x => x.decl === n)!
        if (f.t.k === 'opaque') continue
        body.push({s: 'set', p: this.at(n), to: self(f.name, this.at(n)), x: n.value ? this.ex(n.value) : f.t.k === 'map' ? {e: 'dict', keys: [], p: this.at(n), text: '{}'} : zero(f.t, this.at(n))})
      }
      const cf = ctorOf(c)
      if (!cf) continue
      if (c !== k) (cf.parameters.parameters as Ast[]).forEach((pa, i) => { const a = given.get(c.id)?.[i]; if (!a) this.no(cf, `${c.name}'s constructor given no ${pa.name}`); body.push({s: 'set', p: this.at(cf), to: {e: 'var', n: pa.name, p: this.at(cf)}, x: this.ex(a!)}) })
      body.push(...this.withModifiers(cf, ((cf.modifiers ?? []) as Ast[]).filter(m => this.defs.get(m.modifierName.referencedDeclaration)?.nodeType === 'ModifierDefinition'), 0))
    }
    if (this.ether) body.splice(1, 0, {s: 'set', p, to: self('balance', p), x: this.cur.payable ? {e: 'var', n: 'msg.value', p} : {e: 'int', v: 0, p}})
    // (no call pending at the start)
    for (const fr of this.frames) body.push({s: 'set', p, to: self(`frames$${fr.name.slice('Frame$'.length)}`, p), x: {e: 'dict', keys: [], p, text: '{}'}})
    if (this.frames.length) body.push({s: 'set', p, to: self('pending$', p), x: {e: 'int', v: 0, p}})
    // (the width above every constant the code reads: a constant is below it, as the type's are)
    body.unshift({s: 'if', p, c: {e: 'cmp', op: '<', p, text: `${MOD} >= ${this.minW}`, x: W, y: {e: 'int', v: this.minW, p}}, then: [{s: 'fail', p, why: `the width ${MOD} (2^256) is at least ${this.minW}`}], else: []})
    const params: SParam[] = [{name: 'self', t: {k: 'rec', name: k.name}, self: true}, {name: MOD, t: {k: 'int'}}, {name: 'msg.sender', t: this.ADDR}, ...(this.cur.payable ? [{name: 'msg.value', t: U256}] : [])]
    for (const pa of (top?.parameters.parameters ?? []) as Ast[]) params.push({name: pa.name, t: this.ty(pa.typeDescriptions.typeString, pa)})
    return {id: '__init__', name: '__init__', p, span: [p, 0, 0], params, ret: {k: 'none'}, body, decorators: []}
  }

  // --- statements ------------------------------------------------------------------------------------------------------
  block(b: Ast): SS[] { const was = this.unchecked; if (b.nodeType === 'UncheckedBlock') this.unchecked = true; try { return (b.statements as Ast[]).flatMap(s => this.stmt(s)) } finally { this.unchecked = was } }
  stmt(n: Ast): SS[] {
    const p = this.at(n)
    switch (n.nodeType) {
      case 'Block': case 'UncheckedBlock': return this.block(n)
      case 'EmitStatement': return []
      case 'PlaceholderStatement': return this.no(n, '_ outside a modifier')
      case 'RevertStatement': return [{s: 'fail', p, why: `revert ${this.text(n.errorCall).replace(/^revert /, '')}`}]
      case 'Return': {
        if (!n.expression) return [{s: 'ret', p, ...(this.cur.rets.length ? {x: {e: 'var', n: this.cur.rets[0]!, p}} : {})}]
        return [{s: 'ret', p, x: this.ex(n.expression)}]
      }
      case 'IfStatement': return [{s: 'if', p, c: this.ex(n.condition), then: n.trueBody ? this.stmt(n.trueBody) : [], else: n.falseBody ? this.stmt(n.falseBody) : []}]
      case 'VariableDeclarationStatement': {
        const ds = n.declarations as (Ast | null)[], v = n.initialValue as Ast | undefined
        if (v && isValueCall(v)) return this.valueCall(v, ds)
        if (ds.length !== 1 || !ds[0]) return this.no(n, 'a tuple declared (the subset reads one variable)')
        const d = ds[0], t = this.ty(d.typeDescriptions.typeString, d)
        return [{s: 'set', p, to: {e: 'var', n: d.name, p}, x: v ? this.ex(v) : zero(t, p), t}]
      }
      case 'ExpressionStatement': return this.exprStmt(n.expression)
      case 'ForStatement': case 'WhileStatement': case 'DoWhileStatement': return this.no(n, 'a loop (outside the Solidity subset)')
      case 'InlineAssembly': return this.no(n, 'inline assembly')
      case 'TryStatement': return this.no(n, 'try/catch (a call of another contract)')
    }
    return this.no(n, `a ${n.nodeType} (outside the Solidity subset)`)
  }
  exprStmt(e: Ast): SS[] {
    const p = this.at(e)
    if (e.nodeType === 'FunctionCall' && e.expression.nodeType === 'Identifier' && ['require', 'assert'].includes(e.expression.name)) {
      return [{s: 'if', p, c: {e: 'not', p, strict: true, text: this.text(e), x: this.ex(e.arguments[0])}, then: [{s: 'fail', p, why: this.text(e)}], else: []}]
    }
    if (e.nodeType === 'FunctionCall' && e.expression.nodeType === 'Identifier' && e.expression.name === 'revert') return [{s: 'fail', p, why: this.text(e)}]
    if (isValueCall(e)) return this.valueCall(e, [])
    if (e.nodeType === 'FunctionCall' && e.expression.nodeType === 'MemberAccess' && e.expression.memberName === 'transfer' && /^address/.test(e.expression.expression.typeDescriptions.typeString)) return this.valueCall(e, [], 'transfer')
    if (e.nodeType === 'Assignment') return this.assign(e)
    if (e.nodeType === 'UnaryOperation' && ['++', '--'].includes(e.operator)) return this.assign({...e, nodeType: 'Assignment', operator: e.operator === '++' ? '+=' : '-=', leftHandSide: e.subExpression, rightHandSide: {nodeType: 'Literal', kind: 'number', value: '1', id: -1, src: e.src, typeDescriptions: {typeString: 'int_const 1'}}})
    if (e.nodeType === 'FunctionCall') return [{s: 'expr', p, x: this.ex(e)}]
    if (e.nodeType === 'TupleExpression' && e.components.length === 1) return this.exprStmt(e.components[0])
    return this.no(e, 'an expression statement the subset doesn\'t read')
  }
  // A value sent to an address: `(bool ok, ) = a.call{value: v}("")`, `a.send(v)`, `payable(a).transfer(v)`. The
  // address called is an account without code: the value moves where the contract holds it (ok), else nothing does.
  calls = false
  valueCall(e: Ast, ds: (Ast | null)[], how: 'call' | 'send' | 'transfer' = 'call'): SS[] {
    const p = this.at(e)
    this.ether = true
    this.calls = true
    const target = e.expression.nodeType === 'FunctionCallOptions' ? e.expression.expression : e.expression
    let value: Ast | undefined
    if (e.expression.nodeType === 'FunctionCallOptions') value = (e.expression.options as Ast[])[(e.expression.names as string[]).indexOf('value')]
    else if (target.memberName === 'send' || target.memberName === 'transfer') { value = e.arguments[0]; how = target.memberName }
    if (how === 'call' && e.arguments.length && !(e.arguments[0].nodeType === 'Literal' && (e.arguments[0].value ?? '') === '')) this.no(e, 'a call with data (a call of another contract)')
    const v = value ? this.ex(value) : {e: 'int', v: 0, p}
    const okName = ds[0]?.name ?? `$ok${this.cur.tmp++}`
    if (ds.slice(1).some(Boolean)) this.no(e, 'the data a call returns (the subset reads its ok)')
    const amount = `$amount${this.cur.tmp++}`, has: SX = {e: 'cmp', op: '<=', p, text: 'balance >= value', x: {e: 'var', n: amount, p}, y: self('balance', p)}
    if (this.reenter) return [
      {s: 'set', p, to: {e: 'var', n: amount, p}, x: v, t: U256},
      {s: 'expr', p, x: this.ex(target.expression)},
      {s: 'callout', p, amount, ok: okName, how, why: `${this.text(e)}: the call failed (transfer reverts)`},
    ]
    const out: SS[] = [
      {s: 'set', p, to: {e: 'var', n: amount, p}, x: v},
      // (the address is evaluated: what it reads is read; an account without code accepts the value)
      {s: 'expr', p, x: this.ex(target.expression)},
      {s: 'set', p, to: {e: 'var', n: okName, p}, x: has, t: {k: 'bool'}},
      {s: 'if', p, c: {e: 'var', n: okName, p}, then: [{s: 'set', p, to: self('balance', p), x: {e: 'bin', op: '-', p, text: 'balance - value', x: self('balance', p), y: {e: 'var', n: amount, p}}}], else: how === 'transfer' ? [{s: 'fail', p, why: `${this.text(e)}: the contract holds less than the value (transfer reverts)`}] : []},
    ]
    return out
  }
  assign(e: Ast): SS[] {
    const p = this.at(e), op = e.operator as string, lhs = e.leftHandSide as Ast
    let x = this.ex(e.rightHandSide)
    if (op !== '=') x = this.arith(op.slice(0, -1), this.ex(lhs), x, e, lhs.typeDescriptions.typeString)
    const to = this.place(lhs)
    if (!to) return []
    return [{s: 'set', p, to, x, ...(lhs.nodeType === 'Identifier' && !this.fieldOf(lhs) ? {t: this.ty(lhs.typeDescriptions.typeString, lhs)} : {})}]
  }
  fieldOf(n: Ast): Field | undefined { return n.nodeType === 'Identifier' ? this.fields.find(f => f.decl.id === n.referencedDeclaration) : undefined }
  // Where an assignment writes: a local, a state variable, a mapping's cell (undefined: a string's, left out).
  place(n: Ast): SX | undefined {
    const p = this.at(n)
    if (n.nodeType === 'Identifier') {
      const f = this.fieldOf(n)
      if (f) return f.t.k === 'opaque' ? (/string|bytes/.test(f.sol) ? undefined : this.no(n, f.t.why)) : self(f.name, p)
      return {e: 'var', n: n.name, p}
    }
    if (n.nodeType === 'IndexAccess') { const [m, k] = this.cell(n); return {e: 'idx', p, text: this.text(n), x: m, i: k, nz: true} }
    if (n.nodeType === 'TupleExpression' && n.components.length === 1) return this.place(n.components[0])
    return this.no(n, 'an assignment to other than a variable or a mapping\'s cell')
  }
  // A mapping's cell: the map and its key (two keys of a mapping of mappings as one).
  cell(n: Ast): [SX, SX] {
    const p = this.at(n), b = n.baseExpression as Ast
    if (b.nodeType === 'IndexAccess' && b.typeDescriptions.typeString.startsWith('mapping(')) {
      const [m, k1] = this.cell(b), k2 = this.ex(n.indexExpression)
      this.nested.add(String(m.f))
      return [m, {e: 'bin', op: '+', p, text: `a·2^${PAIR_BITS} + b`, x: {e: 'bin', op: '*', p, text: `a·2^${PAIR_BITS}`, x: k1, y: {e: 'int', v: 2 ** PAIR_BITS, p}}, y: k2}]
    }
    if (b.nodeType === 'Identifier') {
      const f = this.fieldOf(b)
      if (!f || f.t.k !== 'map') return this.no(n, f?.t.k === 'opaque' ? f.t.why : 'an index of other than a state mapping')
      return [self(f.name, p), this.ex(n.indexExpression)]
    }
    return this.no(n, 'an index of other than a state mapping')
  }

  // --- expressions -----------------------------------------------------------------------------------------------------
  ex(n: Ast): SX {
    const p = this.at(n), text = this.text(n)
    const ts: string = n.typeDescriptions?.typeString ?? ''
    // A constant the compiler folds (10**18, 1 days): its value, where it is a safe integer.
    if (/^int_const /.test(ts) && n.nodeType !== 'Literal' && n.nodeType !== 'Identifier') return this.lit(ts.slice(10), n)
    switch (n.nodeType) {
      case 'Literal': {
        if (n.kind === 'bool') return {e: 'bool', v: n.value === 'true', p}
        if (n.kind === 'number') return this.lit(/^int_const /.test(ts) ? ts.slice(10) : n.value, n)
        return {e: 'opaque', p, why: `${text}: a string`}
      }
      case 'Identifier': {
        const d = this.defs.get(n.referencedDeclaration)
        if (n.name === 'msg' || n.name === 'block' || n.name === 'tx') return this.no(n, `${n.name} alone`)
        if (this.consts.has(n.referencedDeclaration)) return this.consts.get(n.referencedDeclaration)!
        const f = this.fieldOf(n)
        if (f) return f.t.k === 'opaque' ? {e: 'opaque', p, why: `${n.name}: ${f.t.why}`} : self(f.name, p)
        if (d?.nodeType === 'FunctionDefinition') return this.no(n, 'a function as a value')
        if (n.name === 'this') return this.no(n, 'the contract\'s own address (not yet)')
        return {e: 'var', n: n.name, p}
      }
      case 'TupleExpression': if (n.components.length === 1) return this.ex(n.components[0]); return this.no(n, 'a tuple')
      case 'UnaryOperation': {
        if (n.operator === '!') return {e: 'not', p, text, strict: true, x: this.ex(n.subExpression)}
        return this.no(n, `${n.operator} (as a value)`)
      }
      case 'BinaryOperation': {
        const op = n.operator as string, a = this.ex(n.leftExpression), b = this.ex(n.rightExpression)
        if (['<', '<=', '>', '>='].includes(op) && /^address/.test(n.leftExpression.typeDescriptions.typeString)) return this.no(n, 'addresses ordered (the subset compares them for equality)')
        if (['<', '<=', '>', '>=', '==', '!='].includes(op)) return {e: 'cmp', op, p, text, x: a, y: b}
        if (op === '&&' || op === '||') return {e: op === '&&' ? 'and' : 'or', p, text, xs: [a, b]}
        if (['+', '-', '*', '/', '%'].includes(op)) return this.arith(op, a, b, n, ts)
        return this.no(n, `${op}: a bit operation (outside the subset)`)
      }
      case 'Conditional': return {e: 'ite', p, text, c: this.ex(n.condition), a: this.ex(n.trueExpression), b: this.ex(n.falseExpression)}
      case 'IndexAccess': {
        const [m, k] = this.cell(n), vt = this.ty(ts, n)
        return {e: 'call', p, text, f: {e: 'get', p, text, x: m, f: 'get'}, args: [k, zero(vt, p)], kw: []}
      }
      case 'MemberAccess': return this.member(n)
      case 'FunctionCall': return this.call(n)
      case 'Assignment': return this.no(n, 'an assignment used as a value')
    }
    return this.no(n, `a ${n.nodeType} (outside the Solidity subset)`)
  }
  lit(v: string, n: Ast): SX {
    const x = Number(v)
    if (!/^-?\d+$/.test(v) || !Number.isSafeInteger(x)) return this.no(n, `the constant ${v.length > 30 ? `${v.slice(0, 12)}…` : v} (past the rule's 2^53, or not whole)`)
    if (x >= this.minW) this.minW = x + 1
    return {e: 'int', v: x, p: this.at(n)}
  }
  arith(op: string, a: SX, b: SX, n: Ast, ts: string): SX {
    const t = this.ty(ts, n)
    if (t.k !== 'int') return this.no(n, `${op} of a ${ts}`)
    const ity = t.bits === undefined ? undefined : {bits: t.bits, signed: t.signed ?? false, name: ts, ...(t.mod ? {mod: t.mod} : {})}
    return {e: 'bin', op, p: this.at(n), text: this.text(n), x: a, y: b, ...(ity ? {ovf: this.unchecked && op !== '/' && op !== '%' ? 'wrap' : 'trap', ity, trap: 'a panic: an arithmetic overflow reverts'} : {})}
  }
  member(n: Ast): SX {
    const p = this.at(n), e = n.expression as Ast, m = n.memberName as string
    if (e.nodeType === 'Identifier' && e.name === 'msg') {
      if (m === 'sender') return {e: 'var', n: 'msg.sender', p}
      if (m === 'value') return this.cur.entry && !this.cur.payable ? {e: 'int', v: 0, p} : {e: 'var', n: 'msg.value', p}
      return this.no(n, `msg.${m}`)
    }
    if (e.nodeType === 'Identifier' && e.name === 'block' && m === 'timestamp') return {e: 'clock', p, text: 'block.timestamp'}
    if (m === 'balance' && e.nodeType === 'FunctionCall' && e.kind === 'typeConversion' && e.arguments[0]?.nodeType === 'Identifier' && e.arguments[0].name === 'this') { this.ether = true; return self('balance', p) }
    // type(uint256).max: the width less one; .min of an unsigned type: 0.
    if (e.nodeType === 'FunctionCall' && e.expression.nodeType === 'Identifier' && e.expression.name === 'type') {
      const t = this.ty(e.arguments[0].typeDescriptions.typeString.replace(/^type\((.*)\)$/, '$1'), n)
      if (t.k === 'int' && !t.signed && m === 'min') return {e: 'int', v: 0, p}
      if (t.k === 'int' && t.mod && m === 'max') return {e: 'bin', op: '-', p, text: 'type(uint256).max', x: self(MOD, p), y: {e: 'int', v: 1, p}}
      if (t.k === 'int' && t.bits !== undefined && t.bits <= 48 && m === 'max') return {e: 'int', v: t.signed ? 2 ** (t.bits - 1) - 1 : 2 ** t.bits - 1, p}
      if (t.k === 'int' && t.bits !== undefined && t.bits <= 48 && m === 'min') return {e: 'int', v: -(2 ** (t.bits - 1)), p}
      return this.no(n, `type(...).${m}`)
    }
    // An enum's value.
    const d = this.defs.get(n.referencedDeclaration)
    if (d?.nodeType === 'EnumValue') { const en = this.defs.get(e.referencedDeclaration); return {e: 'variant', p, v: m, values: (en?.members as Ast[] | undefined)?.map(x => x.name) ?? [m]} }
    return this.no(n, `.${m} (outside the Solidity subset)`)
  }
  call(n: Ast): SX {
    const p = this.at(n), text = this.text(n), f = n.expression as Ast
    if (n.kind === 'typeConversion') {
      const a = n.arguments[0] as Ast, to: string = n.typeDescriptions.typeString, from: string = a.typeDescriptions.typeString
      if (/^address/.test(to) && a.nodeType === 'Literal' && Number(a.value) === 0) return {e: 'int', v: 0, p}
      if (/^address/.test(to) && /^address/.test(from)) return this.ex(a)
      const tt = this.ty(to, n), ft = this.ty(from, a)
      // (a widening of an unsigned value: the same number)
      if (tt.k === 'int' && ft.k === 'int' && !tt.signed && !ft.signed && (tt.mod || (ft.bits !== undefined && tt.bits !== undefined && ft.bits <= tt.bits)) && !(ft.mod && !tt.mod)) return {e: 'as', p, x: this.ex(a), ity: {bits: tt.bits ?? 0, signed: false, ...(tt.mod ? {mod: tt.mod} : {})}}
      if (/^int_const/.test(from) && tt.k === 'int') return this.ex(a)
      return this.no(n, `a conversion of ${from} to ${to}`)
    }
    if (n.kind === 'structConstructorCall') return this.no(n, 'a struct made')
    if (f.nodeType === 'Identifier') {
      const d = this.defs.get(f.referencedDeclaration)
      if (d?.nodeType === 'FunctionDefinition') return this.internal(d, n.arguments as Ast[], n)
      if (d?.nodeType === 'EventDefinition' || d?.nodeType === 'ErrorDefinition') return this.no(n, 'an event or an error made')
      return this.no(n, `${f.name}(...) (outside the Solidity subset)`)
    }
    if (f.nodeType === 'MemberAccess') {
      const d = this.defs.get(f.referencedDeclaration)
      // super.f(...) and Base.f(...): the function named, not the most derived override.
      if (d?.nodeType === 'FunctionDefinition' && f.expression.nodeType === 'Identifier' && (f.expression.name === 'super' || this.defs.get(f.expression.referencedDeclaration)?.nodeType === 'ContractDefinition')) return this.internal(d, n.arguments as Ast[], n, f.expression.name === 'super' ? 'super' : 'base')
      if (f.expression.nodeType === 'Identifier' && f.expression.name === 'this') return this.no(n, 'this.f(...): an external call of the contract itself (not yet)')
      if (isValueCall(n)) return this.no(n, 'a value sent inside an expression (the subset reads it as its own statement)')
      return this.no(n, `${text}: a call of another contract (outside the Solidity subset)`)
    }
    return this.no(n, `${text}: a call the subset doesn't read`)
  }
  // An internal call: inlined, with self, msg.sender and msg.value.
  internal(d: Ast, args: Ast[], n: Ast, how: 'virtual' | 'super' | 'base' = 'virtual'): SX {
    const p = this.at(n)
    let id = how === 'virtual' ? this.fnId(d) : `f${d.id}`
    if (how === 'super') {
      // The next override along the linearization after the contract that calls it.
      const sig = `${d.name}(${(d.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString).join(',')})`
      const from = this.lin.findIndex(c => (c.nodes as Ast[]).some(g => g.id === this.containing(n)))
      const next = this.lin.slice(from + 1).flatMap(c => (c.nodes as Ast[]).filter(g => g.nodeType === 'FunctionDefinition' && g.body && `${g.name}(${(g.parameters.parameters as Ast[]).map(x => x.typeDescriptions.typeString).join(',')})` === sig))[0]
      if (!next) this.no(n, 'super of no implementation')
      id = `f${next!.id}`
    }
    if (!this.funcs[id]) {
      const def = [...this.defs.values()].find(g => `f${g.id}` === id)
      if (!def?.body) return this.no(n, `${d.name}: a function with no body (an interface's)`)
      this.funcs[id] = {id, name: def.name, p, span: [p, 0, 0], params: [], ret: {k: 'none'}, body: [], decorators: []}
      const saved = this.cur
      this.funcs[id] = this.fn(def, id, false)
      this.cur = saved
    }
    const mv: SX = this.cur.entry && !this.cur.payable ? {e: 'int', v: 0, p} : {e: 'var', n: 'msg.value', p}
    return {e: 'call', p, text: this.text(n), f: {e: 'fn', id, p}, args: [{e: 'var', n: 'self', p}, {e: 'var', n: 'msg.sender', p}, mv, ...args.map(a => this.ex(a))], kw: []}
  }
  // The function a node is inside.
  containing(n: Ast): number {
    const [s] = String(n.src).split(':').map(Number)
    for (const c of this.lin) for (const g of c.nodes as Ast[]) { const [gs, gl] = String(g.src).split(':').map(Number); if (g.nodeType === 'FunctionDefinition' && s! >= gs! && s! < gs! + gl! && String(g.src).split(':')[2] === String(n.src).split(':')[2]) return g.id }
    return -1
  }
}
// (no transaction is sent from address(0): a request from it is no request)
const senderNonzero = (p: string): SS => ({s: 'if', p, c: {e: 'cmp', op: '==', p, text: 'msg.sender == address(0)', x: {e: 'var', n: 'msg.sender', p}, y: {e: 'int', v: 0, p}}, then: [{s: 'fail', p, why: 'msg.sender is never address(0)'}], else: []})
const self = (f: string, p: string): SX => ({e: 'get', p, text: `self.${f}`, x: {e: 'var', n: 'self', p}, f})
const zero = (t: SType, p: string): SX => (t.k === 'bool' ? {e: 'bool', v: false, p} : t.k === 'choice' ? {e: 'variant', p, v: t.values[0], values: t.values} : {e: 'int', v: 0, p})
const scalarT = (t: SType) => t.k === 'int' || t.k === 'bool' || t.k === 'choice'
const topArrow = (s: string) => { let d = 0; for (let i = 0; i < s.length; i++) { if (s[i] === '(') d++; else if (s[i] === ')') d--; else if (d === 0 && s.startsWith('=>', i)) return i } return -1 }
const isValueCall = (e: Ast): boolean => e.nodeType === 'FunctionCall' && ((e.expression.nodeType === 'FunctionCallOptions' && e.expression.expression.nodeType === 'MemberAccess' && e.expression.expression.memberName === 'call') || (e.expression.nodeType === 'MemberAccess' && e.expression.memberName === 'send' && /^address/.test(e.expression.expression.typeDescriptions.typeString)))
const callsOut = (ss: SS[]): boolean => ss.some(s => s.s === 'callout' || (s.s === 'if' && (callsOut(s.then as SS[]) || callsOut(s.else as SS[]))))
const hasReturn = (ss: SS[]): boolean => ss.some(s => s.s === 'ret' || (s.s === 'if' && (hasReturn(s.then as SS[]) || hasReturn(s.else as SS[]))))
// The ABI's name of a type.
const abiType = (ts: string) => (ts.startsWith('address') ? 'address' : ts.startsWith('enum ') ? 'uint8' : ts.startsWith('contract ') ? 'address' : ts.replace(/ (storage|memory|calldata).*$/, ''))

// --- the front end ---------------------------------------------------------------------------------------------------
export function readSolidity(file: string, o: SolOptions = {}, reenter = false, compiled?: Compiled): {mod: SModule, meta: SolMeta, c: Compiled} {
  const c = compiled ?? compile(file, o)
  const L = new Lower(c, file, reenter)
  const entry = typeof o.entry === 'string' ? o.entry : undefined
  const {mod, meta} = L.module(entry)
  return {mod, meta, c}
}

export function extractSolidity(at: string | FileURL, opts: SolOptions = {}): Extraction & {read?: StepRead} {
  const file = pathOf(at)
  let r: ReturnType<typeof readSolidity>
  try { r = readSolidity(file, opts) } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const {mod, meta, c} = r
  const out = c.contracts[meta.source]?.[meta.contract]
  const harness = (read: StepRead): Harness => {
    read.arms.length = 0
    read.model.notes.push(...boundaryNotes(meta))
    if (!out) return {cmd: 'false', args: [], hello: {}, error: `solc made no bytecode for ${meta.contract}`}
    const types = out.storageLayout.types
    const slots = Object.fromEntries(out.storageLayout.storage.map(s => [s.label, {slot: s.slot, offset: s.offset, bytes: Number(types[s.type]?.numberOfBytes ?? 32), map: types[s.type]?.encoding === 'mapping', nested: meta.nested.includes(s.label), type: s.type}]))
    const kinds = Object.fromEntries(meta.fields.map(f => [f.name, kindOf(f.t, f.sol)]))
    const mapKeys = Object.fromEntries(meta.fields.filter(f => f.t.k === 'map').map(f => [f.name, keyKinds(f.sol)]))
    return {cmd: opts.python ?? 'python3', args: [new URL('./sol/harness.py', import.meta.url).pathname], env: {...(opts.anvil ? {GDP_ANVIL: opts.anvil} : {})},
      hello: {sol: {creation: out.evm.bytecode.object, abi: out.abi, ids: out.evm.methodIdentifiers, slots, kinds, mapKeys, mod: MOD, minW: meta.minW, addrBits: meta.addrBits, pairBits: PAIR_BITS, entries: meta.entries, ctor: meta.ctor, ether: meta.ether}}}
  }
  // (methods: the external functions that may write the state, unless named)
  const methods = opts.methods ?? Object.keys(meta.entries)
  // (the check's probes: the branches' conditions, each a state and request the prover finds; a revert's condition
  // holds at no step the rule takes, and a contract's rule is large)
  const o: StepOptions = {...opts, methods, strict: true, onError: 'discard', entry: meta.contract, check: {probes: 'writes', ...opts.check}}
  // extractStep's run, the width's param fixed for the check's own draws (2^52: the proof is for every width)
  const notes: string[] = []
  let read: StepRead
  try { read = readStep(mod, o) } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  const w = read.model.params.find(v => v.name.startsWith(MOD))
  if (w) (w as {derived?: unknown}).derived = {op: 'const', v: CHECK_W}
  // (an unsigned value is a natural, wrapped where it would go below 0: its state and its mappings' cells naturals, by
  // the rule's names of the code's fields)
  const unsignedField = new Set([...meta.fields, ...(meta.ether ? [{name: 'balance', t: U256}] : [])].filter(f => { const t = f.t.k === 'map' ? (f.t as {val: SType}).val : f.t; return t.k === 'int' && t.bits !== undefined && !t.signed }).map(f => f.name))
  const nats = (r: StepRead) => Object.fromEntries(r.leaves.filter(l => l.name && unsignedField.has(l.path[0]!)).map(l => [l.kind === 'map' ? `${l.name}.value` : l.name, 'nat' as const]))
  o.domains = {...nats(read), ...opts.domains}
  const unsigned = Object.fromEntries([...read.model.inputs, ...read.model.params].filter(v => read.ints[v.name] && !read.ints[v.name]!.signed).map(v => [v.name, 'nat' as const]))
  const x = fromModel(read.model, mod.file, {...unsigned, ...o.domains}, notes, (rule, sorts) => checkStep(harness(read), read, rule, sorts, o))
  if (!x.ok) return {...x, read, names: stepNames(read)}
  // (a run that breaks a law, from the prover at any width: replayed on the code at the check's before it is shown)
  if (!meta.calls || opts.reentrant === false) {
    const rp = replayer({rule: x.rule!, sorts: x.sorts!, model: read.model, names: stepNames(read), leaves: read.leaves, hello: (harness(read).hello as {sol: unknown}).sol, ctor: read.ctor, replay: compileReplay(opts), opts})
    return {...x, read, names: stepNames(read), replay: (run: Run, law?: unknown) => rp(run, law)}
  }
  // The rule the laws are proven of: every call into other code a point where any of the contract's calls may run.
  let re: ReturnType<typeof readSolidity>, rread: StepRead
  try {
    re = readSolidity(file, opts, true, c)
    rread = readStep(re.mod, {...o, methods: [...methods, ...re.meta.resumes]})
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: `re-entrancy: ${e.what}`}], notes: [...x.notes]}
    throw e
  }
  const rw = rread.model.params.find(v => v.name.startsWith(MOD))
  if (rw) (rw as {derived?: unknown}).derived = {op: 'const', v: CHECK_W}
  rread.model.notes.push(...boundaryNotes(meta), `re-entrancy: each call into other code (${re.meta.resumes.map(r => r.replace(/\$resume$/, '')).join(', ')}) is two steps, any of the contract's calls between them (a callee that calls back); a law about the state holds where no call is pending (pending$ == 0)`)
  const rnotes: string[] = []
  // The check of the re-entrant rule: its own random runs (calls inside calls, by any address) replayed on the code,
  // every address an Agent that makes the run's calls from inside the call it receives.
  let replays: ReturnType<typeof replayer> | undefined
  const runs = {runs: 0, txs: 0, nested: 0, steps: 0}
  const rx = fromModel(rread.model, mod.file, {...unsigned, ...nats(rread), ...opts.domains, 'pending$': 'nat'}, rnotes, (rule, sorts) => {
    replays = replayer({rule, sorts, model: rread.model, names: stepNames(rread), leaves: read.leaves, hello: (harness(read).hello as {sol: unknown}).sol, ctor: read.ctor, replay: compileReplay(opts), opts})
    const ev = {...x.evidence!}
    const n = opts.check?.runs === undefined ? 40 : Math.max(4, Math.round(opts.check.runs / 5)), rand = seeded((opts.check?.seed ?? 11) >>> 0 || 1)
    for (let i = 0; i < n; i++) {
      const run = randomRun(rule, rread.model, rand)
      if (!run.trace.length) continue
      const r = replays(run)
      if (!r.ok) return {...ev, mismatch: `re-entrancy: a run of the rule replayed on the code: ${r.what}`}
      runs.runs++; runs.txs += r.txs; runs.nested += r.nested; runs.steps += run.trace.length
    }
    return ev
  })
  if (rx.ok) rx.notes.push(`re-entrancy: checked by ${runs.runs} runs of the rule replayed on the code (${runs.txs} transactions, ${runs.nested} calls made from inside another, ${runs.steps} steps), an Agent at every address making each call from inside the one it receives`)
  return {...rx, read: rread, names: stepNames(rread), quiet: 'pending$', ...(replays ? {replay: (run: Run, law?: unknown) => replays!(run, law)} : {})}
}

// --- re-entrant runs replayed on the code ---------------------------------------------------------------------------------
type Run = {params: Record<string, number>, trace: Record<string, unknown>[]}
function compileReplay(o: SolOptions): {agent: string, director: string} {
  const c = compile(new URL('./sol/Replay.sol', import.meta.url).pathname, {...o, root: new URL('./sol/', import.meta.url).pathname})
  const k = c.contracts[c.paths.get(c.main)!]!
  return {agent: k.Agent!.evm.deployedBytecode.object, director: k.Director!.evm.deployedBytecode.object}
}
// A random run of the re-entrant rule: requests the rule allows, then every pending call resumed (ok), at the width the
// check runs at.
function randomRun(rule: Rule, model: Model, rand: (k: number) => number): Run {
  const m = rule.machine, it = interpret(m), w = model.params.find(v => v.name.startsWith(MOD))
  const params = rule.randomParams(rand, 6)
  if (w) params[w.name] = CHECK_W
  for (const v of model.params) if (v.name !== w?.name && params[v.name] === 0 && /sender/.test(v.name)) params[v.name] = 1
  if (m.pre && !evalC(m.pre, params, {scalars: {}, maps: {}}, m)) return {params, trace: []}
  const ev = model.inputs.find(v => v.name === model.event), names = ev?.sort.k === 'choice' ? ev.sort.values : []
  const resumes = names.flatMap((n, i) => (n.endsWith('$resume') ? [i] : []))
  let st = it.init(params)
  const trace: Record<string, unknown>[] = []
  const take = (input: Request): boolean => {
    try { if (!allowed(m, it, params, st, input)) return false; st = it.step(params, st, input); trace.push({...input}); return true } catch { return false }
  }
  const depth = 2 + rand(10)
  for (let tries = 0; trace.length < depth && tries < 200; tries++) take(rule.randomInput(rand, 6, params))
  // (the calls pending returned, the last first: a request of a resume, its ok true)
  for (let tries = 0; Number(rule.decode(st)['pending$'] ?? 0) > 0 && tries < 400; tries++) {
    const input = rule.randomInput(rand, 6, params) as Record<string, number>
    if (!ev || !resumes.length) break
    input[ev.name] = resumes[rand(resumes.length)]!
    for (const k of Object.keys(input)) if (k.endsWith('$ok')) input[k] = 1
    take(input as Request)
  }
  return Number(rule.decode(st)['pending$'] ?? 0) > 0 ? {params, trace: []} : {params, trace}
}
type ReplayCtx = {rule: Rule, sorts: Sorts, model: Model, names: Name[], leaves: StepRead['leaves'], hello: unknown, ctor: StepRead['ctor'], replay: {agent: string, director: string}, opts: SolOptions}
// A run replayed: the rule's steps at the check's width, cut into the code's transactions (a call made at no depth up to
// the depth back at 0), each call by its Agent, each resume an Agent's return; the state after each transaction the
// rule's, every call made. With a law, the law broken by the run at that width too.
function replayer(c: ReplayCtx) {
  return (run: Run, law?: unknown): {ok: boolean, what: string, txs: number, nested: number} => {
    const no = (what: string) => ({ok: false, what, txs: 0, nested: 0})
    const isLaw = !!law && typeof law === 'object' && 'holds' in law
    let R: Rule = c.rule
    try { if (isLaw) R = (c.rule as unknown as {withSumsOf: (l: unknown) => Rule}).withSumsOf(law) } catch { R = c.rule }
    const m = R.machine, it = interpret(m), w = c.model.params.find(v => v.name.startsWith(MOD))
    const ps: Record<string, number> = {...run.params, ...(w ? {[w.name]: CHECK_W} : {})}
    if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) return no(`made at the width 2^52, the precondition refuses it`)
    let st = it.init(ps)
    const watcher = law ? watch(m, it, law as never, ps, 8) : undefined
    let broke = watcher ? (watcher.start(st) ? -1 : 0) : -1
    const ev = c.model.event, steps: {method: string, args: [string, unknown][], ok?: boolean, depth: number, before: number}[] = []
    const decodeIn = (req: Record<string, unknown>, name: string): unknown => { const v = c.model.inputs.find(x => x.name === name)!; const k = kindOfVar(v, c.sorts); return k.decode(name, Object.fromEntries(k.vars(name).map(part => [part, Number(req[part] ?? 0)]))) }
    const states: Record<string, unknown>[] = []
    for (const [i, req0] of run.trace.entries()) {
      const req = req0 as Request
      const before = Number(R.decode(st)['pending$'] ?? 0)
      if (!allowed(m, it, ps, st, req)) return no(`step ${i + 1} is refused at the width 2^52 (the run is the rule's at a narrower one)`)
      const next = it.step(ps, st, req)
      if (watcher && broke < 0 && !watcher.step(st, req, next)) broke = i + 1
      st = next
      const method = ev ? String(decodeIn(req0, ev)) : c.model.events[0]!.call
      const args = c.names.filter(n => n.role === 'input' && n.method === method && n.rule).map(n => [n.code, decodeIn(req0, n.rule)] as [string, unknown])
      steps.push({method, args, depth: Number(R.decode(st)['pending$'] ?? 0), before})
      states.push(R.decode(st) as Record<string, unknown>)
      if (broke > 0 && steps.at(-1)!.depth === 0) break
    }
    if (law && broke < 0) return no('the law holds on this run at the width 2^52 (it breaks only at a narrower one)')
    if (steps.at(-1)?.depth) return no('the run ends with a call pending (no state of the code between transactions)')
    // The transactions: each from a call at depth 0 to the depth back at 0.
    const groups: {kind: 'call' | 'ret', m?: string, a?: [string, {in: unknown}][], ok?: boolean}[][] = []
    const after: Record<string, unknown>[] = []
    let nested = 0
    for (const [i, s] of steps.entries()) {
      if (s.before === 0) groups.push([])
      const g = groups.at(-1)!
      if (s.method.endsWith('$resume')) g.push({kind: 'ret', ok: s.args.find(([n]) => n === '$ok')?.[1] === true})
      else { if (s.before > 0) nested++; g.push({kind: 'call', m: s.method, a: s.args.map(([n, v]) => [n, {in: v}])}) }
      if (s.depth === 0) after.push(states[i]!)
    }
    const fs = node<FS & {writeFileSync: (p: string, s: string) => void, mkdtempSync: (p: string) => string, rmSync: (p: string, o?: unknown) => void}>('node:fs'), os = node<{tmpdir: () => string}>('node:os'), cp = node<CP>('node:child_process')
    const dir = fs.mkdtempSync(`${os.tmpdir()}/gdp-solreplay-`)
    const ctorArgs = c.ctor.map(([n, a]) => [n, a.k === 'in' ? {in: n === MOD || n.startsWith(MOD) ? CHECK_W : ps[a.name] ?? 0} : {dflt: true}])
    let out: {error?: string, states?: Record<string, unknown>[], oks?: boolean[][]}
    try {
      fs.writeFileSync(`${dir}/run.json`, JSON.stringify({sol: c.hello, leaves: c.leaves, ctorSpec: c.ctor, ctor: ctorArgs, agent: c.replay.agent, director: c.replay.director, groups}))
      out = JSON.parse(cp.execFileSync(c.opts.python ?? 'python3', [new URL('./sol/harness.py', import.meta.url).pathname, '--replay', `${dir}/run.json`], {encoding: 'utf8', maxBuffer: 1 << 26, stdio: ['ignore', 'pipe', 'pipe'], env: {...env(), ...(c.opts.anvil ? {GDP_ANVIL: c.opts.anvil} : {})}}))
    } catch (e) { return no(`the replay didn't run (${String((e as Error).message).slice(0, 300)})`) } finally { fs.rmSync(dir, {recursive: true, force: true}) }
    if (out.error) return no(`the code: ${out.error}`)
    const shown = (g: number) => groups[g]!.map(e => (e.kind === 'ret' ? `return(${e.ok})` : `${e.m}(${e.a!.map(([n, v]) => `${n}=${String(v.in)}`).join(', ')})`)).join(' ')
    for (const [g, ok] of (out.oks ?? []).entries()) if (ok.some(x => !x)) return no(`transaction ${g + 1} (${shown(g)}): a call the rule takes reverts in the code`)
    for (const [g, code] of (out.states ?? []).entries()) {
      const d = sameState(c.leaves, after[g]!, code)
      if (d) return no(`after transaction ${g + 1} (${shown(g)}): ${d}`)
    }
    return {ok: true, what: `replayed on the code (anvil, the contract's bytecode): ${groups.length} transactions, ${nested} calls made from inside another, the state after each the rule's${law ? ', the law broken there' : ''}`, txs: groups.length, nested}
  }
}
const byKey = (a: [string, string], b: [string, string]) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0)
// The rule's state (decoded) against the code's (the harness's), leaf by leaf: undefined where they agree.
function sameState(leaves: StepRead['leaves'], rule: Record<string, unknown>, code: Record<string, unknown>): string | undefined {
  for (const l of leaves) {
    if (l.kind === 'frame' || l.kind === 'none') continue
    if (l.kind === 'map') {
      const r = Object.fromEntries(Object.entries((rule[l.name] ?? {}) as Record<string, Record<string, unknown>>).filter(([, c]) => c.has).map(([k, c]) => [k, String(c.value)]))
      const k = Object.fromEntries(Object.entries((code[l.name] ?? {}) as Record<string, {value: unknown}>).map(([key, c]) => [key, String(c.value)]))
      if (JSON.stringify(Object.entries(r).sort(byKey)) !== JSON.stringify(Object.entries(k).sort(byKey))) return `${l.path.join('.')} is ${JSON.stringify(k)} in the code, ${JSON.stringify(r)} in the rule`
      continue
    }
    if (String(rule[l.name]) !== String(code[l.name])) return `${l.path.join('.')} is ${String(code[l.name])} in the code, ${String(rule[l.name])} in the rule`
  }
  return undefined
}
const kindOf = (t: SType, sol = ''): string => (t.k === 'map' ? `map:${kindOf((t as {val: SType}).val, valueSol(sol))}` : sol.startsWith('address') ? 'addr' : t.k === 'int' ? (t.mod ? 'u256' : `${t.signed ? 'i' : 'u'}${t.bits ?? 0}`) : t.k === 'choice' ? `choice:${t.values.join('|')}` : t.k)
const valueSol = (sol: string): string => { if (!sol.startsWith('mapping(')) return sol; const inner = sol.slice('mapping('.length, -1); return valueSol(inner.slice(topArrow(inner) + 2).trim()) }
// A mapping's key kinds, as the harness encodes them (two for a mapping of mappings).
const keyKinds = (sol: string): string[] => {
  const one = (k: string) => (k.startsWith('address') ? 'addr' : k === 'uint256' ? 'u256' : k.startsWith('uint') ? `u${k.slice(4)}` : k)
  const inner = sol.slice('mapping('.length, -1), a = topArrow(inner), v = inner.slice(a + 2).trim()
  return [one(inner.slice(0, a).trim()), ...(v.startsWith('mapping(') ? keyKinds(v).slice(0, 1) : [])]
}
function boundaryNotes(m: SolMeta): string[] {
  return [
    `Solidity: ${m.contract} read from solc's AST; checked against its bytecode (the same solc) on anvil`,
    `uint256: exact past 2^53 by the width ${MOD} (any value above ${m.minW - 1} in the rule, 2^256 in the code): a law proven for every width is proven for 2^256`,
    `addresses: naturals below 2^${m.addrBits} compared by equality (address(0) is 0; a mapping of mappings is keyed by two as one number): the claim is for runs among fewer than 2^${m.addrBits} accounts`,
    'a revert is the step\'s refusal (nothing it wrote stays); a mapping\'s cell is held where it isn\'t 0',
    ...(m.ether ? ['balance: the contract\'s ether; an address sent a value is an account without code (it calls nothing back)'] : []),
  ]
}
