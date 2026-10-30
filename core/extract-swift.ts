// The extractor's Swift front end (`gdp-wired/extract-swift`): a type of a Swift package (or of one .swift file) read
// through swift-syntax (core/swift/: a small reader, built once per version of its source and of the toolchain),
// executed by the shared step executor (core/extract-step.ts), printed, built and checked as every front end's rule is.
// The check builds the package as it ships, in a copy beside a generated harness (an extension of the type in its own
// file, so private members are read and set as the code's own extensions do, and an executable target that drives
// it), by `swift build` in debug (overflow traps and assert on); each request runs first in a forked child, so a trap
// (Swift's crash: overflow, precondition, a nil force-unwrapped) is the step's failure, not the harness's end.
//
//   const x = extractSwift('Sources/NIOHTTP2/InboundWindowManager.swift', {entry: 'InboundWindowManager'})
//   const y = extractSwift('Limiter.swift')                // one file (a path or a URL): its package made for the check; the entry inferred
//
// The subset: a class, struct or actor (an actor's methods are its steps: Swift runs each without interleaving between
// suspension points, and the subset reads ones with none) whose stored properties are the state, its init's parameters
// (or a struct's memberwise ones) the rule's params, its methods the requests (mutating ones too); Int (64-bit) and
// every fixed width with Swift's overflow trap (`+ - *`), the wrapping `&+ &- &*`, `/ %` truncating by a constant,
// Int32(x) trapping where x doesn't fit, (truncatingIfNeeded:) wrapping, (clamping:) saturating, (exactly:) an
// Optional, the ReportingOverflow forms; Bool, String, enums without associated values as choices (an Int raw value
// its discriminant); Optional (if let, guard let, ??, !, == nil, if case .some); Dictionary as maps ([k], [k, default:],
// updateValue, removeValue, = nil); throw, precondition, assert and fatalError as failures; switch (cases of an enum,
// literals, ranges, where) and if/guard condition lists as ifs; a struct by its memberwise init as a record (a copy where
// the code copies); the type's own methods, computed properties and the package's free functions inlined. The
// boundary is inferred: an init parameter typed by a protocol is an injected dependency (a store for key-shaped
// methods, its other methods answers over the protocol's declared results), other code's calls left out or answered
// (the check rewrites an answered call in its copy, and gives the protocol a generated conforming fake), `// gdp:` tags.
//
// Refused, each where it is with why: loops, closures, generics, await, do/catch and try?, optional chaining, arrays,
// floats, enums with associated values, inout, a class's superclass of the code's own, other code given the state.
import {type Extraction} from './extract.ts'
import {Refusal, pathOf, type FileURL} from './extract-read.ts'
import {type Answer, type Harness, type Leaf, type PArg, type SModule, type SType, type StepOptions, type StepRead, entryNames, extractStep, node, stubbed} from './extract-step.ts'
export {proveRule, proveSteps} from './dsl.ts'

export type SwiftOptions = StepOptions & {
  // The toolchain's `swift` (by default the one on the PATH; $GDP_SWIFT).
  swift?: string,
  // The init's arity, or its parameters as written (`'(initialValue: Int)'`), where the type has several.
  ctor?: number | string,
  // The package's target read, where a directory is given and the package has several.
  target?: string,
}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
type FS = {existsSync: (p: string) => boolean, readFileSync: (p: string, e: string) => string, writeFileSync: (p: string, s: string) => void, mkdirSync: (p: string, o?: unknown) => void, rmSync: (p: string, o?: unknown) => void,
  readdirSync: (p: string, o?: unknown) => unknown[], statSync: (p: string) => {isDirectory: () => boolean}, renameSync: (a: string, b: string) => void, rmdirSync: (p: string) => void, realpathSync: (p: string) => string}
type Path = {resolve: (...p: string[]) => string, dirname: (p: string) => string, join: (...p: string[]) => string, basename: (p: string) => string, relative: (a: string, b: string) => string}
type Rec = SModule['recs'][string] & {swift?: SwiftRec}
type Sig = {name: string, labels: string[], static: boolean, mutating: boolean, throws: boolean, async: boolean, types: string[], ret: string}
type Req = {kind: 'func' | 'var', name: string, decl?: string, ret: string, params?: {label: string, name: string, t: string}[], throws?: boolean, async?: boolean, static?: boolean, set?: boolean}
type SwiftRec = {kind: string, qual: string, file?: string, priv?: boolean, ctor?: {labels: string[], throws: boolean, types: string[]}, sigs?: Record<string, Sig>, props?: {name: string, t: string, let: boolean, kw: string, init: boolean}[], reqs?: Req[], assoc?: boolean, refused?: string}
const env = () => (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env ?? {}
const errText = (e: unknown) => { const ls = `${(e as {stdout?: string}).stdout ?? ''}\n${(e as {stderr?: string}).stderr ?? ''}`.split('\n'); return (ls.filter(l => /\berror:/.test(l)).length ? ls.filter(l => /\berror:/.test(l)) : ls.filter(l => /error|fatal/i.test(l))).slice(0, 4).join(' | ').slice(0, 900) || String((e as Error).message).slice(0, 300) }
const hash = (s: string) => node<{createHash: (a: string) => {update: (s: string) => {digest: (e: string) => string}}}>('node:crypto').createHash('sha256').update(s).digest('hex').slice(0, 16)
const swiftOf = (o: SwiftOptions) => o.swift ?? env().GDP_SWIFT ?? 'swift'

// --- the reader: compiled once per version of its source and of the toolchain ----------------------------------------
// Against the toolchain's own SwiftSyntax (lib/swift/host, which ships it for macros) where there is one: seconds.
// Else the reader's package, swift-syntax pinned, built by SwiftPM: minutes, once.
export function swiftReader(o: SwiftOptions = {}): string {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), path = node<Path>('node:path')
  const dir = new URL('./swift/', import.meta.url).pathname, main = `${dir}Sources/gdp-swiftreader/main.swift`
  let version: string
  try { version = cp.execFileSync(swiftOf(o), ['--version'], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']}) } catch { throw new Refusal('swift', 'a Swift toolchain (5.9 or later: swift on the PATH, or swift: / $GDP_SWIFT) is needed to extract Swift') }
  const out = `${os.tmpdir()}/gdp-swiftreader-${hash(fs.readFileSync(main, 'utf8') + fs.readFileSync(`${dir}Package.swift`, 'utf8') + version)}`, bin = `${out}/gdp-swiftreader`
  if (fs.existsSync(bin)) return bin
  fs.mkdirSync(out, {recursive: true})
  const tmpBin = `${bin}.${Date.now()}${Math.random().toString(36).slice(2, 8)}`
  // (the toolchain's swiftc and its host modules)
  let swiftc = ''
  try { swiftc = cp.execFileSync('sh', ['-c', `command -v xcrun >/dev/null && xcrun --find swiftc || command -v swiftc`], {encoding: 'utf8'}).trim() } catch { /* none */ }
  const host = swiftc && path.resolve(fs.realpathSync(swiftc), '../../lib/swift/host')
  let err = ''
  if (host && fs.existsSync(`${host}/SwiftSyntax.swiftmodule`)) {
    try {
      cp.execFileSync(swiftc, ['-O', '-I', host, '-L', host, '-lSwiftSyntax', '-lSwiftParser', '-lSwiftOperators', '-Xlinker', '-rpath', '-Xlinker', host, main, '-o', tmpBin], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26})
      fs.renameSync(tmpBin, bin)
      return bin
    } catch (e) { err = errText(e) }
  }
  try {
    cp.execFileSync(swiftOf(o), ['build', '-c', 'release', '--package-path', dir, '--scratch-path', `${out}/build`], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 28})
    const built = cp.execFileSync(swiftOf(o), ['build', '-c', 'release', '--package-path', dir, '--scratch-path', `${out}/build`, '--show-bin-path'], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']}).trim()
    fs.writeFileSync(tmpBin, '')
    cp.execFileSync('cp', [`${built}/gdp-swiftreader`, tmpBin], {})
    fs.renameSync(tmpBin, bin)
    return bin
  } catch (e) { throw new Refusal('swift', `the Swift reader didn't build (${errText(e) || err}): a Swift 5.9 or later toolchain is needed to extract Swift`) }
}

// --- the package: its root, the target a file is in, the target's sources ---------------------------------------------
type Pkg = {root: string, file?: string, target: string, dir: string, files: string[], single: boolean}
function swiftFiles(d: string): string[] {
  const fs = node<FS>('node:fs'), path = node<Path>('node:path')
  if (!fs.existsSync(d)) return []
  return (fs.readdirSync(d, {withFileTypes: true}) as {name: string, isDirectory: () => boolean}[]).flatMap(e => (e.isDirectory() ? (e.name.startsWith('.') ? [] : swiftFiles(path.join(d, e.name))) : e.name.endsWith('.swift') ? [path.join(d, e.name)] : [])).sort()
}
export function swiftPackage(at: string, o: SwiftOptions = {}): Pkg {
  const fs = node<FS>('node:fs'), path = node<Path>('node:path'), cp = node<CP>('node:child_process')
  const abs = path.resolve(at)
  if (!fs.existsSync(abs)) throw new Refusal(at, 'no such file or directory')
  const isDir = fs.statSync(abs).isDirectory()
  let root: string | undefined = isDir ? abs : undefined
  for (let d = isDir ? abs : path.dirname(abs); !root; d = path.dirname(d)) { if (fs.existsSync(path.join(d, 'Package.swift'))) root = d; if (path.dirname(d) === d) break }
  // (one file outside any package: its own package, made for the check)
  if (!root || !fs.existsSync(path.join(root, 'Package.swift'))) { if (isDir) throw new Refusal(at, 'no Package.swift: give a .swift file or a package\'s directory'); return {root: path.dirname(abs), file: abs, target: 'GdpCode', dir: path.dirname(abs), files: [abs], single: true} }
  let targets: {name: string, path?: string, type: string}[] = []
  try { targets = (JSON.parse(cp.execFileSync(swiftOf(o), ['package', 'dump-package', '--package-path', root], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26})) as {targets: typeof targets}).targets }
  catch (e) { throw new Refusal(root, `the package's manifest didn't load (${errText(e)})`) }
  const dirOf = (t: {name: string, path?: string, type: string}) => path.join(root!, t.path ?? (t.type === 'test' ? `Tests/${t.name}` : `Sources/${t.name}`))
  const lib = targets.filter(t => t.type === 'regular')
  const t = !isDir ? lib.find(x => abs.startsWith(`${dirOf(x)}/`)) : o.target ? lib.find(x => x.name === o.target) : lib.length === 1 ? lib[0] : undefined
  if (!t) throw new Refusal(at, isDir ? `the package has ${lib.length} library targets (${lib.map(x => x.name).join(', ')}): give the file, or name one (target)` : 'not a file of one of the package\'s library targets')
  return {root, ...(isDir ? {} : {file: abs}), target: t.name, dir: dirOf(t), files: swiftFiles(dirOf(t)), single: false}
}
export function readSwift(at: string, names: string[], o: SwiftOptions = {}): {mod: SModule, pkg: Pkg} {
  const cp = node<CP>('node:child_process')
  const pkg = swiftPackage(at, o)
  let out: string
  try { out = cp.execFileSync(swiftReader(o), [pkg.root, pkg.file ?? '-', names.length ? names.join(',') : '-', o.ctor === undefined ? '-' : String(o.ctor), ...pkg.files], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(at, `the Swift reader didn't run (${errText(e)})`) }
  const mod = JSON.parse(out) as SModule
  mod.module = pkg.target
  return {mod, pkg}
}

export function extractSwift(where: string | FileURL, opts: SwiftOptions = {}): Extraction & {read?: StepRead} {
  const at = pathOf(where)
  let r: {mod: SModule, pkg: Pkg}
  try {
    if (opts.stores && Object.keys(opts.stores).length) throw new Refusal(at, 'stores: not in the Swift front end yet (an injected protocol\'s are inferred)')
    r = readSwift(at, entryNames(opts), opts)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const x = extractStep(r.mod, read => harnessFor(r.pkg, r.mod, read, opts), opts)
  // (what the check assumed of the code's runtime, in the notes)
  const cls = x.read?.cls ? (r.mod.recs[x.read.cls] as Rec).swift : undefined
  if (cls?.kind === 'actor') x.notes.push(`${x.read!.model.name}: an actor, its methods each one step (Swift runs an actor's method without interleaving up to a suspension point, and these have none): checked as a class whose calls don't overlap`)
  if (x.evidence) x.notes.push('Swift: checked in a debug build (overflow traps, assert and precondition on), each request run first in a forked child (a crash is the step\'s failure); branch arms not counted (no instrumentation yet)')
  return x
}

// --- the harness: Swift beside the code, generated per reading ----------------------------------------------------------
// (its fixed parts, Swift files shipped beside the reader)
const resource = (f: string): string => node<FS>('node:fs').readFileSync(new URL(`./swift/${f}`, import.meta.url).pathname, 'utf8')
// The Swift name of an integer type, and of an answer's type.
const intName = (t: SType): string => { const x = t as {sw?: string, bits?: number, signed?: boolean}; return x.sw ?? (x.bits === 64 || !x.bits ? (x.signed === false ? 'UInt' : 'Int') : `${x.signed === false ? 'UInt' : 'Int'}${x.bits}`) }
function answerType(a: Answer, read: StepRead): string {
  const ty = read.ints[a.inputs.name], base = a.sort.replace(/\s*\|\s*None$/, '').trim()
  const inner = base === 'int' || /^[ui](8|16|32|64|size)$/.test(base) ? (ty ? intName({k: 'int', bits: ty.bits, signed: ty.signed}) : 'Int') : base === 'bool' ? 'Bool' : base === 'str' ? 'String' : base === 'float' ? 'Double' : 'Int'
  return a.inputs.none ? `${inner}?` : inner
}
// The expression making a value of type t from the JSON value `j` (a __GdpJ?), throwing __GdpBad where it can't.
function conv(t: SType, j: string, mod: SModule, depth = 0): string {
  if (t.k === 'int') return `try __gdpInt(${j}, ${intName(t)}.self)`
  if (t.k === 'bool') return `try __gdpBool(${j})`
  if (t.k === 'str') return `try __gdpStr(${j})`
  if (t.k === 'choice') return `try { () throws -> ${t.enum} in switch try __gdpStr(${j}) { ${t.values.map(v => `case ${JSON.stringify(v)}: return .${v}`).join('; ')}; default: throw __GdpBad(why: "no case") } }()`
  if (t.k === 'opt') return `(__gdpIsNone(${j}) ? nil : ${conv(t.of, j, mod, depth + 1)})`
  if (t.k === 'rec') {
    const r = mod.recs[t.name] as Rec | undefined, ps = r?.swift?.props?.filter(p => !p.init)
    if (!r || r.swift?.kind !== 'struct' || depth > 4 || r.methods.__init__ === undefined || !ps) return `try { throw __GdpBad(why: "a value of ${t.name}") }()`
    return `${t.name}(${ps.map(p => `${p.name}: ${conv(r.fields.find(f => f.name === p.name)!.t, `${j}?["f"]?[${JSON.stringify(p.name)}]`, mod, depth + 1)}`).join(', ')})`
  }
  return `try { throw __GdpBad(why: "a value of ${t.k}") }()`
}
// A value as a leaf of the state holds it (numbers as strings, choices by their case's name).
const caseName = (t: SType & {k: 'choice'}, x: string) => `{ () -> String in switch ${x} { ${t.values.map(v => `case .${v}: return ${JSON.stringify(v)}`).join('; ')} } }()`
function enc(t: SType, x: string): string {
  return t.k === 'int' ? `__GdpJ.s(String(${x}))` : t.k === 'bool' ? `__GdpJ.b(${x})` : t.k === 'str' ? `__GdpJ.s(${x})` : t.k === 'choice' ? `__GdpJ.s(${caseName(t, x)})` : '__GdpJ.null'
}
// A method's result as the protocol tags it.
function out(t: SType, x: string): string {
  return t.k === 'int' ? `__GdpJ.o(["n": .s(String(${x}))])` : t.k === 'bool' ? `__GdpJ.b(${x})` : t.k === 'str' ? `__GdpJ.o(["s": .s(${x})])` : t.k === 'choice' ? `__GdpJ.o(["s": ${enc(t, x)}])`
    : t.k === 'opt' ? `(${x}.map { (__v) -> __GdpJ in ${out(t.of, '__v')} } ?? __GdpJ.null)` : t.k === 'none' ? '__GdpJ.null' : `__GdpJ.o(["o": .s("value")])`
}
type Gen = {edits: Map<string, string[]>, access: Map<string, Set<string>>}
// The accessor of a field of a record type (in the type's own file, so its private members are in reach).
function accessor(g: Gen, mod: SModule, rec: string, f: string): string {
  const r = mod.recs[rec] as Rec, p = r.swift?.props?.find(x => x.name === f)
  if (!r.swift?.file || !p || /^no declared type|unknown/.test(p.t)) throw new Refusal(r.p, `${r.short}.${f}: a property of no type the check's harness can name`)
  const s = g.access.get(rec) ?? g.access.set(rec, new Set()).get(rec)!
  if (!s.has(f)) { s.add(f); (g.edits.get(r.swift.file) ?? g.edits.set(r.swift.file, []).get(r.swift.file)!).push(`extension ${r.swift.qual} { var __gdp_${f}: ${p.t} { get { self.${f} } set { self.${f} = newValue } } }`) }
  return `__gdp_${f}`
}
function harnessCode(g: Gen, mod: SModule, read: StepRead, cls: Rec): {entry: string, main: string} {
  const sw = cls.swift!, E = sw.qual, isClass = sw.kind !== 'struct', mut = isClass ? '' : 'mutating '
  if (read.inject?.length) throw new Refusal(cls.p, 'a field injected after the init: the Swift harness gives dependencies only through the init')
  // (each leaf's place: the object's field, through its records' accessors)
  const place = (path: string[]): string => { let cur = cls.name, out = 'o'; for (const seg of path) { const fd = (mod.recs[cur] as Rec).fields.find(f => f.name === seg); out += `.${accessor(g, mod, cur, seg)}`; if (fd?.t.k === 'rec') cur = fd.t.name } return out }
  const typeAt = (path: string[]): SType | undefined => { let cur = cls.name, t: SType | undefined; for (const seg of path) { t = (mod.recs[cur] as Rec | undefined)?.fields.find(f => f.name === seg)?.t; if (t?.k === 'rec') cur = t.name } return t }
  const get: string[] = [], set: string[] = []
  const byPath = new Map<string, Leaf[]>()
  for (const l of read.leaves) if (l.kind !== 'frame' && !l.store) { const k = l.path.join('.'); byPath.set(k, [...(byPath.get(k) ?? []), l]) }
  for (const [, ls] of byPath) {
    const val = ls.find(l => l.kind !== 'none'), none = ls.find(l => l.kind === 'none'), path = ls[0]!.path, pl = place(path), t0 = typeAt(path)
    if (!t0) throw new Refusal(cls.p, `${path.join('.')}: a leaf of no type the harness reads`)
    if (val?.kind === 'map') {
      if (t0.k !== 'map') throw new Refusal(cls.p, `${path.join('.')}: a map of no declared type`)
      const kt = t0.key, vt = t0.val, vr = vt.k === 'rec' ? vt.name : undefined
      const tyName = (t: SType): string => (t.k === 'int' ? intName(t) : t.k === 'bool' ? 'Bool' : t.k === 'str' ? 'String' : t.k === 'choice' ? t.enum! : t.k === 'rec' ? (mod.recs[t.name] as Rec).swift?.qual ?? t.name : 'Never')
      const vfields = vr ? (val.fields ?? []).map(f => ({name: f.name, t: (mod.recs[vr] as Rec).fields.find(y => y.name === f.name)!.t})) : []
      const cell = (x: string) => (vr ? `__GdpJ.o([${vfields.map(f => `${JSON.stringify(f.name)}: ${enc(f.t, `${x}.${accessor(g, mod, vr, f.name)}`)}`).join(', ')}])` : `__GdpJ.o(["value": ${enc(vt, x)}])`)
      const keyText = kt.k === 'choice' ? caseName(kt, '$0.key') : 'String(describing: $0.key)'
      get.push(`s[${JSON.stringify(val.name)}] = .o(Dictionary(uniqueKeysWithValues: ${pl}.map { (${keyText}, ${cell('$0.value')}) }))`)
      // (a record value made by its memberwise init: the fields the rule reads from the cell, the others their zero)
      const vrec = vr ? mod.recs[vr] as Rec : undefined
      if (vrec && (vrec.swift?.kind !== 'struct' || !vrec.swift.props)) throw new Refusal(cls.p, `${path.join('.')}: a map of ${vrec.short}, which the harness can't make (a struct by its memberwise init)`)
      const mk = vrec ? `${tyName(vt)}(${vrec.swift!.props!.filter(p => !p.init).map(p => { const f = vfields.find(x => x.name === p.name), ft = vrec.fields.find(x => x.name === p.name)!.t; return `${p.name}: ${f ? conv(ft, `__c[${JSON.stringify(p.name)}]`, mod) : '__gdpZero()'}` }).join(', ')})` : conv(vt, '__c["value"]', mod)
      set.push(`do { var __m: [${tyName(kt)}: ${tyName(vt)}] = [:]; if case .o(let __cs)? = st[${JSON.stringify(val.name)}] { for (__k, __c) in __cs { __m[${conv(kt, '__GdpJ.s(__k)', mod)}] = ${mk} } }; ${pl} = __m }`)
      continue
    }
    if (!val) continue
    const t = t0.k === 'opt' ? t0.of : t0
    if (none) {
      get.push(`if let __x = ${pl} { s[${JSON.stringify(val.name)}] = ${enc(t, '__x')}; s[${JSON.stringify(none.name)}] = .b(false) } else { s[${JSON.stringify(val.name)}] = ${t.k === 'int' ? '.s("0")' : t.k === 'bool' ? '.b(false)' : t.k === 'choice' ? `.s(${JSON.stringify(t.values[0])})` : '.s("")'}; s[${JSON.stringify(none.name)}] = .b(true) }`)
      set.push(`${pl} = __gdpIsTrue(st[${JSON.stringify(none.name)}]) ? nil : ${conv(t, `st[${JSON.stringify(val.name)}]`, mod)}`)
    } else {
      get.push(`s[${JSON.stringify(val.name)}] = ${enc(t, pl)}`)
      set.push(`${pl} = ${conv(t, `st[${JSON.stringify(val.name)}]`, mod)}`)
    }
  }
  // The stores (an injected dependency's keys, by template): each object's, its cells by the template's hole.
  const storeLeaves = read.leaves.filter(l => l.store)
  for (const l of storeLeaves) {
    get.push(`do { var __cs: [String: __GdpJ] = [:]; for (__k, __v) in (__gdpS.cur[${JSON.stringify(l.store)}]?.data ?? [:]) { if let __h = __gdpTpl(${JSON.stringify(l.tpl ?? '{}')}, __k) { __cs[__h] = .o(["value": __gdpLeaf(__v)]) } }; s[${JSON.stringify(l.name)}] = .o(__cs) }`)
    set.push(`if let __st = __gdpS.cur[${JSON.stringify(l.store)}] { for __k in __st.data.keys where __gdpTpl(${JSON.stringify(l.tpl ?? '{}')}, __k) != nil { __st.data[__k] = nil }; if case .o(let __cs)? = st[${JSON.stringify(l.name)}] { for (__h, __c) in __cs { __st.data[__gdpFill(${JSON.stringify(l.tpl ?? '{}')}, __h)] = __c["value"] } } }`)
  }
  const tpls: Record<string, string[]> = {}
  for (const l of storeLeaves) (tpls[l.store!] ??= []).push(l.tpl ?? '{}')
  // The frames (fields the rule leaves out): each as it was, after a call.
  const frames = read.leaves.filter(l => l.kind === 'frame' && !l.cls).map(l => l.path).filter(p => { try { place(p); return true } catch { return false } })
  // The fakes: an injected protocol's conforming class (get, set and delete over what it keeps; answered methods from
  // the request; those left out doing nothing; any other one a crash, which the check reports).
  const fakes: string[] = [], fakeOf = new Map<string, string>()
  const init = mod.funcs[cls.methods.__init__ ?? ''], ctorParams = init?.params.filter(p => !p.self) ?? []
  for (const [name, a] of read.ctor) {
    if (a.k !== 'store') continue
    const pa = ctorParams.find(p => p.name === name), pt = pa?.t.k === 'opt' ? pa.t.of : pa?.t, pr = pt?.k === 'rec' ? mod.recs[pt.name] as Rec : undefined
    if (!pr?.swift?.reqs) throw new Refusal(cls.p, `${cls.short}(${name}): an injected dependency of a protocol outside the files read (the check can't make one)`)
    if (pr.swift.assoc) throw new Refusal(cls.p, `${cls.short}(${name}): a protocol with associated types (the check can't make one)`)
    // (the executor's names where the reading states none: get, set and delete)
    const d0 = read.stores[name] ?? {}, d = {...d0, get: d0.get ?? ['get', 'async_get_cache', 'get_cache'], set: d0.set ?? ['set', 'async_set_cache', 'set_cache'], delete: d0.delete ?? ['delete', 'delete_cache', 'async_delete_cache']}, cname = `__GdpFake_${name}`
    fakeOf.set(name, cname)
    const body = (q: Req): string => {
      const ps = q.params ?? [], key = ps[0] ? `"\\(${ps[0].name === '_' ? '__a0' : ps[0].name})"` : '""'
      const ans = read.answers.find(x => x.patch.store === name && x.patch.path?.at(-1) === q.name)
      if (ans) return `return __gdpAnswer(${JSON.stringify(ans.key)})`
      if (d.get.includes(q.name)) return `return __gdpStoreGet(__store, ${key})`
      if (d.set.includes(q.name) && ps[1]) return `__store.data[${key}] = __gdpEnc(${ps[1].name === '_' ? '__a1' : ps[1].name})${q.ret === 'Void' || q.ret === '()' ? '' : '; return __gdpZero()'}`
      if (d.delete.includes(q.name)) return `__store.data[${key}] = nil${q.ret === 'Void' || q.ret === '()' ? '' : '; return __gdpZero()'}`
      if (d.skip?.includes(q.name)) return q.ret === 'Void' || q.ret === '()' ? '' : 'return __gdpZero()'
      return `fatalError(${JSON.stringify(`${name}.${q.name}: a method of the injected dependency the rule doesn't read`)})`
    }
    const members = pr.swift.reqs.map(q => {
      if (q.kind === 'var') return `var ${q.name}: ${q.ret} { get { ${body({...q, params: []})} }${q.set ? ' set { }' : ''} }`
      // (the requirement's own declaration, its unnamed parameters named, `mutating` dropped: a class conforms)
      let i = 0
      const decl = (q.decl ?? '').replace(/\bmutating\s+/, '').replace(/(\(|,\s*)_\s*:/g, (_m, pre: string) => `${pre}_ __a${i++}:`)
      return `${decl} { ${body(q)} }`
    })
    fakes.push(`final class ${cname}: ${pr.swift.qual}, @unchecked Sendable { let __store: __GdpStore; init(_ s: __GdpStore) { __store = s }\n  ${members.join('\n  ')}\n}`)
  }
  // The object made (the init's arguments, a store for each injected dependency).
  const ctor = sw.ctor ?? {labels: [], throws: false, types: []}
  const made = ctorParams.map((pa, i) => {
    const a = read.ctor.find(([n]) => n === pa.name)?.[1], lab = ctor.labels[i] ?? '_', arg = (x: string) => (lab === '_' ? x : `${lab}: ${x}`)
    if (a?.k === 'store') return arg(`${fakeOf.get(pa.name)}({ let __s = __GdpStore(); __gdpS.cur[${JSON.stringify(pa.name)}] = __s; return __s }())`)
    return arg(conv(pa.t, `a?[${i}]?[1]`, mod))
  })
  if (sw.refused) throw new Refusal(cls.p, sw.refused)
  // The requests: each method by its labels, its result as the protocol tags it.
  const calls = Object.keys(read.args).map(m => {
    const fid = cls.methods[m], fn = fid ? mod.funcs[fid] : undefined, sig = sw.sigs?.[m]
    if (!fn || !sig) throw new Refusal(cls.p, `${m}: a request the harness can't call`)
    if (sig.async) throw new Refusal(fn.p, `${m}: an async method (the check's harness calls synchronously; an actor's methods are read as its class's)`)
    const ps = fn.params.filter(p => !p.self)
    const lets = ps.map((p, i) => `let __a${i} = ${conv(p.t, `a?[${i}]?[1]`, mod)}`)
    const callArgs = ps.map((_, i) => (sig.labels[i] === '_' ? `__a${i}` : `${sig.labels[i]}: __a${i}`)).join(', ')
    const ret = fn.ret.k === 'none' || sig.ret === 'Void' ? 'none' : 'some'
    return `case ${JSON.stringify(m)}:\n      ${lets.join('; ')}${lets.length ? '\n      ' : ''}do { ${ret === 'none' ? `try self.${sig.name}(${callArgs}); return .null` : `let __r = try self.${sig.name}(${callArgs}); return ${out(fn.ret, '__r')}`} } catch { throw __GdpErr(why: "\\(error)") }`
  })
  const entry = `
// --- gdp-wired's check harness (generated in the check's copy; the code itself is never changed) ---
extension ${E} {
  static func __gdpNew(_ a: __GdpJ?) throws -> ${E} {
    do { return try ${E}(${made.join(', ')}) } catch let b as __GdpBad { throw b } catch { throw __GdpErr(why: "\\(error)") }
  }
  ${mut}func __gdpCall(_ m: String, _ a: __GdpJ?) throws -> __GdpJ {
    switch m {
    ${calls.join('\n    ')}
    default: throw __GdpBad(why: "no method \\(m)")
    }
  }
}
${fakes.join('\n')}
func __gdpGet(_ o: ${E}) -> [String: __GdpJ] { var s: [String: __GdpJ] = [:]; ${get.join('\n  ')}
  return s }
func __gdpSet(_ o: inout ${E}, _ st: [String: __GdpJ]) throws { ${set.join('\n  ')} }
func __gdpFrames(_ o: ${E}) -> [String: String] { [${frames.map(p => `${JSON.stringify(p.join('.'))}: String(describing: ${place(p)})`).join(', ') || ':'}] }
let __gdpTpls: [String: [String]] = [${Object.entries(tpls).map(([k, v]) => `${JSON.stringify(k)}: ${JSON.stringify(v)}`).join(', ') || ':'}]
final class __GdpState: @unchecked Sendable { var objs: [${E}] = []; var stores: [[String: __GdpStore]] = []; var cur: [String: __GdpStore] = [:]; var answers: [String: __GdpJ] = [:]; var discard = false }
let __gdpS = __GdpState()
typealias __GdpEntry = ${E}
${resource('Harness.swift')}`
  const main = resource('Main.swift').replace('__GDP_MODULE__', mod.module)
  return {entry, main}
}

// The package copied (stable per package, so `swift build` rebuilds only what changed), the harness generated beside the
// type, the answered calls rewritten to the request's answers, an actor read as a class (its methods don't interleave),
// its `let` properties `var` (the check sets them; the code can't), an executable target that drives it, built in debug.
function harnessFor(pkg: Pkg, mod: SModule, read: StepRead, opts: SwiftOptions): Harness {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), path = node<Path>('node:path')
  read.arms.length = 0
  const cls = read.cls ? mod.recs[read.cls] as Rec : undefined
  if (!cls?.swift) return {cmd: 'false', args: [], hello: {}, error: 'the Swift harness reads a type\'s methods (not free functions yet)'}
  const work = `${os.tmpdir()}/gdp-swiftcheck-${hash(pkg.root + (pkg.single ? pkg.file! : ''))}`, lock = `${work}.lock`
  const rel = (f: string) => (pkg.single ? `Sources/GdpCode/${path.basename(f)}` : f)
  // (one check at a time per package: its copy is shared)
  for (let i = 0; ; i++) { try { fs.mkdirSync(lock); break } catch { if (i > 1200) { try { fs.rmdirSync(lock) } catch { /* gone */ } } else Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 500) } }
  try {
    const g: Gen = {edits: new Map(), access: new Map()}
    let code: {entry: string, main: string}
    try { code = harnessCode(g, mod, read, cls) } catch (e) { if (e instanceof Refusal) return {cmd: 'false', args: [], hello: {}, error: e.what}; throw e }
    // The copy: every file of the package written where it differs (so its mtime moves only then).
    const want = new Map<string, string>(), links = new Map<string, string>()
    if (pkg.single) {
      want.set('Package.swift', `// swift-tools-version:5.9\nimport PackageDescription\nlet package = Package(name: "GdpCode", targets: [.target(name: "GdpCode", path: "Sources/GdpCode")])\n`)
      want.set(rel(pkg.file!), fs.readFileSync(pkg.file!, 'utf8'))
    } else {
      // (a link to a directory linked again in the copy, to where it points)
      const walk = (d: string): string[] => (fs.readdirSync(d, {withFileTypes: true}) as {name: string, isDirectory: () => boolean}[]).flatMap(e => { const p = path.join(d, e.name); if (['.build', '.git', '.swiftpm', 'GdpHarness'].includes(e.name)) return []; if (e.isDirectory()) return walk(p); if (fs.statSync(p).isDirectory()) { links.set(path.relative(pkg.root, p), fs.realpathSync(p)); return [] } return [p] })
      for (const f of walk(pkg.root)) want.set(path.relative(pkg.root, f), fs.readFileSync(f, 'binary' as 'utf8'))
    }
    // (the check's own changes: let as var where the harness sets a property, the answered calls, the actor, the harness)
    const lets = new Map<string, Set<string>>()
    for (const rn of [cls.name, ...g.access.keys()]) for (const p of (mod.recs[rn] as Rec).swift?.props ?? []) if (p.let) { const m = /^(.*):(\d+):(\d+)$/.exec(p.kw); if (m) (lets.get(m[1]!) ?? lets.set(m[1]!, new Set()).get(m[1]!)!).add(`${m[2]}:${m[3]}`) }
    const text = (f: string): string | undefined => {
      const t = want.get(rel(f)) ?? want.get(f)
      if (t === undefined || !lets.has(f)) return t
      return t.split('\n').map((l, i) => { let s = l; for (const lc of lets.get(f)!) { const [ln, col] = lc.split(':').map(Number); if (ln === i + 1 && s.slice(col! - 1, col! + 2) === 'let') s = `${s.slice(0, col! - 1)}var${s.slice(col! + 2)}` } return s }).join('\n')
    }
    const changed = new Map<string, string>()
    for (const f of new Set([...lets.keys()])) changed.set(f, text(f)!)
    let stubs: Map<string, string>
    try { stubs = stubbed({...read, answers: read.answers.filter(a => !a.patch.store)}, f => changed.get(f) ?? text(f), a => `(__gdpAnswer(${JSON.stringify(a.key)}) as ${answerType(a, read)})`) }
    catch (e) { if (e instanceof Refusal) return {cmd: 'false', args: [], hello: {}, error: e.what}; throw e }
    for (const [f, t] of stubs) changed.set(f, t)
    const ef = cls.swift.file!
    let et = changed.get(ef) ?? text(ef)!
    if (cls.swift.kind === 'actor') et = et.replace(new RegExp(`\\bactor(\\s+${cls.short}\\b)`), 'final class$1').replace(/\bnonisolated(\(unsafe\))?\s+/g, '')
    changed.set(ef, `${et}\n${code.entry}`)
    for (const [f, exts] of g.edits) changed.set(f, `${changed.get(f) ?? text(f)!}\n${exts.join('\n')}\n`)
    for (const [f, t] of changed) want.set(rel(f), t)
    for (const m of [...want.keys()].filter(k => /^Package(@swift-[\d.]+)?\.swift$/.test(k))) want.set(m, `${want.get(m)}\npackage.targets.append(.executableTarget(name: "GdpHarness", dependencies: [.target(name: ${JSON.stringify(pkg.target)})], path: "GdpHarness"))\n`)
    want.set('GdpHarness/main.swift', code.main)
    fs.mkdirSync(work, {recursive: true})
    for (const [f, t] of want) {
      const to = path.join(work, f)
      let same = false
      try { same = fs.readFileSync(to, 'binary' as 'utf8') === t } catch { /* new */ }
      if (!same) { fs.mkdirSync(path.dirname(to), {recursive: true}); fs.writeFileSync(to, t) }
    }
    // (files of an earlier copy the package no longer has)
    const walkW = (d: string): string[] => (fs.readdirSync(d, {withFileTypes: true}) as {name: string, isDirectory: () => boolean}[]).flatMap(e => (['.build', '.swiftpm'].includes(e.name) || links.has(path.relative(work, path.join(d, e.name))) ? [] : e.isDirectory() ? walkW(path.join(d, e.name)) : [path.join(d, e.name)]))
    for (const f of walkW(work)) if (!want.has(path.relative(work, f)) && !links.has(path.relative(work, f))) fs.rmSync(f)
    for (const [l, to] of links) if (!fs.existsSync(path.join(work, l))) { fs.mkdirSync(path.dirname(path.join(work, l)), {recursive: true}); node<{symlinkSync: (a: string, b: string) => void}>('node:fs').symlinkSync(to, path.join(work, l)) }
    try { cp.execFileSync(swiftOf(opts), ['build', '--product', 'GdpHarness', '--package-path', work], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 28}) }
    catch (e) { return {cmd: 'false', args: [], hello: {}, error: `the package doesn't build with the check's harness: ${errText(e)}`} }
    const bin = cp.execFileSync(swiftOf(opts), ['build', '--package-path', work, '--show-bin-path'], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']}).trim()
    return {cmd: `${bin}/GdpHarness`, args: [], hello: {}}
  } finally { try { fs.rmdirSync(lock) } catch { /* gone */ } }
}
export type {PArg}
