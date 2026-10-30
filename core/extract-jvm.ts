// The extractor's JVM front ends (`gdp-wired/extract-java`, `gdp-wired/extract-kotlin`): a class read through its
// language's own parser (Java: the JDK's javac tree API, core/jvm/JavaReader.java; Kotlin: the Kotlin compiler's PSI,
// core/jvm/KtReader.java), both lowered into the shared step IR through one JVM layer (core/jvm/Jvm.java: the types,
// maps, Optional and nullability, atomics, Math, TimeUnit, the clock), executed by the shared step executor
// (core/extract-step.ts), printed, built and checked as every front end's rule is. The check compiles the code (javac
// or kotlinc, the clock's and the answered calls' sites rewritten to read the request's) or loads the project's own
// jars (`prebuilt`), and runs it through one reflective harness for both (core/jvm/Harness.java). A JDK (17 or later)
// is needed for both, kotlinc (its lib/ has the compiler's PSI and the standard library) for Kotlin, only here.
//
//   const x = extractJava('core/src/main/java/io/grpc/internal/RetriableStream.java', {root: 'core/src/main/java', entry: 'Throttle'})
//   const k = extractKotlin('okhttp3/internal/http2/flowcontrol/WindowCounter.kt', {entry: 'WindowCounter', failures: 'kept'})
//
// The subset: a class (a static nested one too; its superclasses of the code's own sources merged in), its one
// constructor (or the one of the arity given: `ctor`) with the fields' initializers as the rule's start and its
// arguments the params, its methods as requests; int, long, short, byte and char with Java's wraparound (Kotlin's Int
// and Long the same), Math.addExact and the other exact methods trapping (an ArithmeticException: the step's failure),
// / and % truncating by a constant, floats at whole values; booleans, strings set and compared, enums as choices;
// records (Java's, Kotlin's data classes, plain classes whose constructor sets their fields, Lombok's @Value and @Data)
// as values, a data class's copy(...) an update; Map, HashMap, ConcurrentHashMap and Kotlin's maps as maps; Optional and
// Kotlin's nullable types as options (?:, !!, ?.let, checkNotNull); a throw, check, require and error as the step's
// failure; synchronized, @Synchronized, a ReentrantLock's lock()/finally unlock() and withLock as the step atomic;
// AtomicInteger, AtomicLong, AtomicBoolean and AtomicReference as the fields they hold (compare-and-set loops read as
// their first pass); switch and when as chains of ifs; TimeUnit's conversions; System.currentTimeMillis, nanoTime and
// a Clock's millis as the request's time. An immutable class's method that returns its next value (a data class's
// copy, `this`) is a step whose result is the new state.
//
// Refused, each where it is with why: other loops, try/catch, lambdas (but Kotlin's scope functions), arrays and other
// collections, instanceof, static fields that aren't constants, inner classes, generic classes and methods, other
// code's calls not answered or skipped. Not yet: `stores`, branch coverage (the arms aren't counted).
import {type Extraction} from './extract.ts'
import {Refusal} from './extract-read.ts'
import {type Harness, type SModule, type SX, type StepOptions, type StepRead, entryNames, extractStep, node} from './extract-step.ts'

export type JvmOptions = StepOptions & {
  // The source root the file's package resolves from (javac's -sourcepath); by default the file's package root.
  root?: string,
  // Jars and class directories the code compiles and runs against.
  classpath?: string[],
  // Run the classes the classpath already has (the project's own jars, as they ship) instead of compiling the file:
  // the clock and answered calls then can't be read as the request's.
  prebuilt?: boolean,
  // Kotlin: other files of the code compiled with the file (kotlinc has no source path).
  sources?: string[],
  // The constructor's arity, where the class has several.
  ctor?: number,
  // The JDK's home (by default $JAVA_HOME, else java and javac on the PATH); Kotlin's (by default $KOTLIN_HOME, else
  // the kotlinc on the PATH).
  javaHome?: string, kotlinHome?: string,
}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
type FS = {existsSync: (p: string) => boolean, readFileSync: (p: string, e: string) => string, writeFileSync: (p: string, s: string) => void, mkdirSync: (p: string, o?: unknown) => void, mkdtempSync: (p: string) => string, realpathSync: (p: string) => string, renameSync: (a: string, b: string) => void, rmSync: (p: string, o?: unknown) => void}
type Path = {resolve: (...p: string[]) => string, dirname: (p: string) => string, join: (...p: string[]) => string, delimiter: string}
const here = (f: string) => new URL(`./jvm/${f}`, import.meta.url).pathname
const TOOLS = ['Jvm.java', 'JavaReader.java', 'Harness.java', 'Rt.java']
// (a JVM's stack trace: its exception's line first)
const errText = (e: unknown) => { const ls = String((e as {stderr?: string}).stderr || (e as {stdout?: string}).stdout || (e as Error).message).split('\n').filter(l => l.trim() && !/^\s+at /.test(l)); return ls.slice(-3).join(' | ').slice(0, 600) }

function jdk(o: JvmOptions): {java: string, javac: string} {
  const env = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env ?? {}
  const home = o.javaHome ?? env.JAVA_HOME
  return home ? {java: `${home}/bin/java`, javac: `${home}/bin/javac`} : {java: 'java', javac: 'javac'}
}
function kotlinLib(o: JvmOptions): string {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), path = node<Path>('node:path')
  const env = (globalThis as {process?: {env?: Record<string, string | undefined>}}).process?.env ?? {}
  let home = o.kotlinHome ?? env.KOTLIN_HOME
  if (!home) { try { home = path.resolve(path.dirname(fs.realpathSync(cp.execFileSync('sh', ['-c', 'command -v kotlinc'], {encoding: 'utf8'}).trim())), '..') } catch { /* none */ } }
  const lib = home && [`${home}/lib`, `${home}/libexec/lib`].find(d => fs.existsSync(`${d}/kotlin-compiler.jar`))
  if (!lib) throw new Refusal('kotlinc', 'kotlinc (the Kotlin compiler: its lib/kotlin-compiler.jar and kotlin-stdlib.jar) is needed to extract Kotlin; set kotlinHome or $KOTLIN_HOME')
  return lib
}
// The tools (the readers and the harness), compiled once per version of their sources and of the compiler.
function tools(o: JvmOptions, kt?: string): string {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), crypto = node<{createHash: (a: string) => {update: (s: string) => {digest: (e: string) => string}}}>('node:crypto')
  const files = kt ? ['KtReader.java'] : TOOLS
  const h = crypto.createHash('sha256').update(files.map(f => fs.readFileSync(here(f), 'utf8')).join('\0') + (kt ?? '') + jdk(o).javac).digest('hex').slice(0, 16)
  const dir = `${os.tmpdir()}/gdp-jvm${kt ? 'kt' : ''}-${h}`
  if (fs.existsSync(`${dir}/ok`)) return dir
  const base = kt ? tools(o) : undefined, tmp = fs.mkdtempSync(`${dir}-`)
  try { cp.execFileSync(jdk(o).javac, ['-nowarn', '-Xlint:none', '-d', tmp, ...(kt ? ['-cp', `${base}:${kt}/kotlin-compiler.jar:${kt}/kotlin-stdlib.jar`] : []), ...files.map(here)], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { fs.rmSync(tmp, {recursive: true, force: true}); throw new Refusal('javac', `the JVM tools didn't compile (${errText(e)}): a JDK 17 or later is needed to extract ${kt ? 'Kotlin' : 'Java'}`) }
  fs.writeFileSync(`${tmp}/ok`, '')
  try { fs.renameSync(tmp, dir) } catch { fs.rmSync(tmp, {recursive: true, force: true}) }
  return dir
}

type Sig = {name: string, params: string[]}
type Jvm = {cls: string, ctor?: string[], methods: Record<string, Sig>, rewrites: {span: [number, number], to: string}[], reducers?: string[], javac?: string[]}
const jvmOf = (mod: SModule) => (mod as SModule & {jvm: Jvm}).jvm
// The class read's own (an entry inferred among the file's classes): its binary name, constructor and methods.
const classOf = (mod: SModule, read: StepRead): {cls: string, ctor: string[], methods: Record<string, Sig>, reducers: string[]} => {
  const j = jvmOf(mod), r = read.cls ? (mod.recs[read.cls] as {jvm?: {cls?: string, sigs?: Record<string, Sig>, ctor?: {params?: string[]}, reducers?: string[]}} | undefined)?.jvm : undefined
  return r?.cls ? {cls: r.cls, ctor: r.ctor?.params ?? [], methods: r.sigs ?? {}, reducers: r.reducers ?? j.reducers ?? []} : {cls: j.cls, ctor: j.ctor ?? [], methods: j.methods, reducers: j.reducers ?? []}
}
// The package root of a file: its directory less the package's.
function packageRoot(file: string, kotlin: boolean): string {
  const fs = node<FS>('node:fs'), path = node<Path>('node:path')
  let text = ''
  try { text = fs.readFileSync(file, 'utf8') } catch { /* read by the reader, which says so */ }
  const m = /^\s*package\s+([\w.]+)/m.exec(text)
  let d = path.dirname(path.resolve(file))
  if (m && !kotlin) for (const _ of m[1]!.split('.')) d = path.dirname(d)
  return d
}
export function readJvm(lang: 'java' | 'kotlin', file: string, names: string[], o: JvmOptions = {}): SModule {
  const cp = node<CP>('node:child_process'), path = node<Path>('node:path')
  const abs = path.resolve(file), root = path.resolve(o.root ?? packageRoot(abs, lang === 'kotlin'))
  const kt = lang === 'kotlin' ? kotlinLib(o) : undefined
  const t = tools(o), cpath = kt ? [t, tools(o, kt), `${kt}/kotlin-compiler.jar`, `${kt}/kotlin-stdlib.jar`, ...(o.classpath ?? [])].join(':') : t
  let out: string
  try { out = cp.execFileSync(jdk(o).java, ['-cp', cpath, `gdp.jvm.${kt ? 'KtReader' : 'JavaReader'}`, JSON.stringify({root, file: abs, names, classpath: (o.classpath ?? []).join(':'), sources: o.sources ?? [], ctor: o.ctor ?? null})], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(file, `the ${kt ? 'Kotlin' : 'Java'} reader didn't run (${errText(e)}): a JDK 17 or later${kt ? ' and kotlinc' : ''} is needed to extract ${kt ? 'Kotlin' : 'Java'}`) }
  return JSON.parse(out) as SModule
}

// An answered call's sites: the calls of other code whose names the answer's key matches (the executor's own rule):
// a static one's (`ext`) and a method's of an object of other code (an injected dependency's are the harness's own).
function answerSites(mod: SModule, keys: string[]): {span: [number, number], key: string, jt: string}[] {
  const out: {span: [number, number], key: string, jt: string}[] = []
  const hit = (names: string[]) => keys.find(e => names.some(n => n === e || n.startsWith(`${e}.`) || n.endsWith(`.${e}`) || n.endsWith(`.${e.replace(/^self\./, '')}`)))
  const walk = (x: unknown) => {
    if (Array.isArray(x)) { x.forEach(walk); return }
    if (!x || typeof x !== 'object') return
    const n = x as SX & {span?: [number, number], jt?: string}
    const f = n.f as SX | undefined
    if (n.e === 'call' && f && (f.e === 'ext' || f.e === 'get') && n.span) { const k = hit([String(f.text), ...(f.e === 'ext' ? [String(f.q)] : [String(f.f)])]); if (k) out.push({span: n.span, key: k, jt: n.jt ?? 'java.lang.Object'}) }
    for (const v of Object.values(n)) walk(v)
  }
  walk(mod.funcs)
  return out
}
const BOXES: Record<string, string> = {int: 'java.lang.Integer', long: 'java.lang.Long', short: 'java.lang.Short', byte: 'java.lang.Byte', char: 'java.lang.Character', boolean: 'java.lang.Boolean', float: 'java.lang.Float', double: 'java.lang.Double'}
const KT: Record<string, string> = {int: 'Int', long: 'Long', short: 'Short', byte: 'Byte', char: 'Char', boolean: 'Boolean', float: 'Float', double: 'Double', 'java.lang.String': 'String'}

// The code compiled for the check: a copy of the file with the clock's and the answered calls' sites rewritten.
function compiled(lang: 'java' | 'kotlin', mod: SModule, read: StepRead, o: JvmOptions): {dirs: string[], error?: string} {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os'), path = node<Path>('node:path')
  const j = jvmOf(mod), kotlin = lang === 'kotlin'
  const sites = [...j.rewrites.map(r => ({span: r.span, text: 'gdp.Rt.now()'})), ...answerSites(mod, read.answers.filter(a => !a.patch.store).map(a => a.key)).map(s => {
    const t = s.jt.replace(/\?$/, '').replace(/<.*$/, ''), box = BOXES[t] ?? t
    return {span: s.span, text: kotlin ? `(gdp.Rt.answer(${JSON.stringify(s.key)}, ${box}::class.java) as ${KT[t] ?? t.split('.').pop()}${s.jt.endsWith('?') ? '?' : ''})` : `((${box}) gdp.Rt.answer(${JSON.stringify(s.key)}, ${box}.class))`}
  })]
  if (o.prebuilt) return sites.length ? {dirs: [], error: 'prebuilt: the rule reads the clock or an answered call, which the shipped classes can\'t be given (compile the file instead)'} : {dirs: []}
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-jvmcheck-`)
  const src = fs.readFileSync(mod.path, 'utf8')
  let text = src
  for (const s of [...sites].sort((a, b) => b.span[0] - a.span[0])) text = text.slice(0, s.span[0]) + s.text + text.slice(s.span[1])
  const rel = mod.path.startsWith(`${mod.root}/`) ? mod.path.slice(mod.root.length + 1) : mod.file
  const copy = `${work}/src/${rel}`
  fs.mkdirSync(path.dirname(copy), {recursive: true})
  fs.writeFileSync(copy, text)
  const out = `${work}/classes`, t = tools(o), extra = (o.classpath ?? []).join(':')
  try {
    if (kotlin) {
      const kt = kotlinLib(o)
      cp.execFileSync(jdk(o).java, ['-Xss8m', '-cp', `${kt}/kotlin-compiler.jar`, 'org.jetbrains.kotlin.cli.jvm.K2JVMCompiler', '-kotlin-home', path.dirname(kt), '-nowarn', '-no-reflect', '-d', out, '-cp', [t, extra].filter(Boolean).join(':'), copy, ...(o.sources ?? []).map(f => path.resolve(f))], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26})
      return {dirs: [out, `${kt}/kotlin-stdlib.jar`]}
    }
    cp.execFileSync(jdk(o).javac, ['-nowarn', '-Xlint:none', '-proc:none', '-implicit:class', '-d', out, '-sourcepath', `${work}/src:${mod.root}`, '-cp', [t, extra].filter(Boolean).join(':'), copy], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26})
    return {dirs: [out]}
  } catch (e) { return {dirs: [], error: `the code doesn't compile for the check (${errText(e)})`} }
}

export function extractJvm(lang: 'java' | 'kotlin', file: string, opts: JvmOptions): Extraction & {read?: StepRead} {
  let mod: SModule
  try {
    if (opts.stores && Object.keys(opts.stores).length) throw new Refusal(file, `stores: not in the ${lang === 'java' ? 'Java' : 'Kotlin'} front end yet`)
    mod = readJvm(lang, file, entryNames(opts), opts)
    // (the shipped classes can't be rewritten: an answer, other than an injected dependency's, can't be stubbed)
    if (opts.prebuilt) mod.stubs = false
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const harness = (read: StepRead): Harness => {
    read.arms.length = 0
    read.model.notes.push(`${lang === 'java' ? 'Java' : 'Kotlin'}: the code is checked as ${opts.prebuilt ? 'its classes ship' : 'compiled from the file'}; its branch arms are not counted (no instrumentation yet)`)
    const j = classOf(mod, read)
    let c: {dirs: string[], error?: string}
    try { c = compiled(lang, mod, read, opts) } catch (e) { if (e instanceof Refusal) return {cmd: 'false', args: [], hello: {}, error: e.what}; throw e }
    if (c.error) return {cmd: 'false', args: [], hello: {}, error: c.error}
    const t = tools(opts)
    return {cmd: jdk(opts).java, args: ['-cp', t, 'gdp.jvm.Harness'], hello: {jcls: j.cls, cp: [...c.dirs, ...(opts.classpath ?? [])], jctor: {params: j.ctor}, methods: j.methods, reducers: j.reducers}}
  }
  return extractStep(mod, harness, opts)
}
export const extractJava = (file: string, opts: JvmOptions) => extractJvm('java', file, opts)
export const extractKotlin = (file: string, opts: JvmOptions) => extractJvm('kotlin', file, opts)
