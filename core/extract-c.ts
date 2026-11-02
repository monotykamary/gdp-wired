// The extractor's C front end (`gdp-wired/extract-c`): a struct of a C file and the functions that take it by pointer,
// read through clang (core/c/reader.ts: its JSON dump, with the project's flags or its compile_commands.json), put in
// the typed shape Go's reader prints and lowered by Go's lowering into the shared step IR (core/extract-go.ts, then
// core/extract-step.ts): one lowering for both, C's semantics written as explicit nodes where clang's types say so.
// The check compiles the file as it ships with a generated harness (it #includes the file, so its static functions are
// called as they are, with the same flags and the undefined-behavior sanitizer trapping), drives the functions with
// the rule's requests and compares every state (core/extract-go-check.ts's `speak`, Go's own driver).
//
//   const x = extractC('src/bucket.c', {fails: {bucket_take: '< 0'}, flags: ['-Iinclude']})   // a path or a URL; the struct inferred
//
// The subset: a struct of the file (its typedef's name or its tag) starting at all zeros, each function of the file
// whose first parameter points to it a request (by default the non-static ones; `functions` names them), the others
// called inlined; fields of integer types (every width, signed and unsigned, enums as their integers), bool, nested
// structs, pointers to the state's structs; locals, assignment (=, op=, ++, --), if, switch (a case runs into the
// next unless it breaks), early returns, ?:, the file's functions inlined; assert and abort (the step's refusal), and
// a result the caller states is a failure (`fails: {take: '< 0'}`).
//
// Integers are exactly C's: unsigned arithmetic wraps modulo 2^n (by cases, the bounds and the path's facts deciding
// where it may); signed overflow is undefined behavior, refused where the bounds and the path's facts don't exclude it
// (never wrapped, never assumed away); the promotions and conversions are clang's, a conversion to a narrower type
// wrapping as clang and gcc define it; / and % by a constant truncate, by zero undefined (refused); u & (2^k − 1) of an
// unsigned u is u % 2^k; a 64-bit number stops at the rule's ±2^53 (refused past it), an unsigned one below 0 refused.
//
// Refused, each where it is with why: loops, goto, arrays and pointer arithmetic, floats, strings, unions, globals and
// static locals (state every object shares), calls of other files' or libraries' code, function pointers, bit
// operations but the mask above, the comma operator, an assignment or ++ inside an expression, and sizeof.
import {type Extraction, fromModel} from './extract.ts'
import {Refusal, pathOf, type FileURL} from './extract-read.ts'
import {buildCheck, builtEvidence, compileLimit, stubbed} from './extract-step.ts'
import type {Rule} from './dsl.ts'
import type {Sorts} from './extract-print.ts'
import type {Coverage} from './extract-check.ts'
import {type GoOptions, type GoPkg, type GoRead, goNames, readGo, unsignedDomains} from './extract-go.ts'
import {type GoCheckOptions, type GoEvidence, type GoLeaf, speak} from './extract-go-check.ts'
import {type CRead, clangDump, constantsOf, flagsFor, node, readC} from './c/reader.ts'
export {proveRule, proveSteps} from './dsl.ts'

export type COptions = {
  // The struct (C++: the class), and the functions read as its requests (by default each non-static one whose first
  // parameter points to it; `name/arity` for an overload).
  entry?: string, methods?: string[],
  /** @deprecated methods (the same: the struct's functions read as its requests) */
  functions?: string[],
  // true: another file's or a library's function refused where it is called (nothing inferred)
  strict?: boolean,
  // The project's flags (-I, -D, -std), or its compile_commands.json (the file's entry's), and the clang to run.
  flags?: string[], compileCommands?: string, clang?: string,
  // The project's own files (their functions are read too: a header's static inline ones); by default the file's directory.
  root?: string,
  // A function's result that is its failure where it compares so: {take: '< 0'} (the step's refusal there).
  fails?: Record<string, string>,
  // Calls of other code answered by the request (the callee's name: its result's type) or left out, as `gdp: answer`
  // and `gdp: skip` comments say at one call.
  answers?: Record<string, string>, skip?: string[],
  // Globals the rule leaves out (a file keeping its state in globals), or the entry's fields: an output the code writes
  // for other code (a database mirror, a CAN buffer, a report), which nothing the rule keeps reads; a read of one into
  // what it keeps is refused. (`answers` may name the file's own functions too: each call of one the request's value.)
  leave?: string[],
  // The file's own functions read as other code's (a getter of another object's state, CANopen's CO_isError): each call
  // the request's value, of its declared type, the check giving it in the copy of the file.
  cut?: string[],
  onError?: 'refuse' | 'discard', domains?: Record<string, 'nat' | 'int'>, check?: GoCheckOptions,
}
type FS = {readFileSync: (p: string, e: string) => string, mkdtempSync: (p: string) => string, writeFileSync: (p: string, s: string) => void, rmSync: (p: string, o?: unknown) => void, mkdirSync: (p: string, o?: unknown) => void}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}

// (C++ that includes little, embedded code's without the standard library: its whole dump is small, read whole; else
// only the class's, its headers' being hundreds of MB)
const smallTUs = new Map<string, boolean>()
function smallTU(file: string, flags: string[], clang: string): boolean {
  const k = `${clang} ${flags.join(' ')} ${file}`
  if (!smallTUs.has(k)) { try { smallTUs.set(k, node<CP>('node:child_process').execFileSync(clang, ['-x', 'c++', ...flags, '-E', '-P', file], {encoding: 'utf8', maxBuffer: 1 << 26, stdio: ['ignore', 'pipe', 'ignore']}).length < 400_000) } catch { smallTUs.set(k, false) } }
  return smallTUs.get(k)!
}
export function readCFile(file: string, opts: COptions, cpp = false): {c: CRead, flags: string[]} {
  // (no entry, C++: each class the file declares tried, its dump read for its name only)
  if (!opts.entry && cpp) {
    let text = ''
    try { text = node<FS>('node:fs').readFileSync(file, 'utf8') } catch { throw new Refusal(file, 'no such file') }
    const why: string[] = [], names = [...new Set([...text.matchAll(/^\s*(?:class|struct)\s+(\w+)\s*(?:final\s*)?(?::[^{;]*)?\{/gm)].map(m => m[1]!))]
    const ok = names.flatMap(n => { try { const r = readCFile(file, {...opts, entry: n}, cpp); readGo(r.c.pkg, {methods: r.c.methods}); return [r] } catch (e) { if (e instanceof Refusal) { why.push(`${n}: ${e.what}`); return [] } throw e } })
    if (ok.length !== 1) throw new Refusal(file, ok.length ? `several classes write their state (${ok.map(r => r.c.entry).join(', ')}): name one (entry)` : `no class whose methods write its state${why.length ? ` (${why.join('; ')})` : ''}: name the entry`)
    return ok[0]!
  }
  const flags0 = [...flagsFor(file, opts.compileCommands), ...(opts.flags ?? [])], flags = cpp && !flags0.some(f => f.startsWith('-std=')) ? [...flags0, '-std=c++17'] : flags0, {tu, target} = clangDump(file, flags, opts.clang ?? (cpp ? 'clang++' : 'clang'), cpp, cpp && !smallTU(file, flags, opts.clang ?? 'clang++') ? opts.entry : undefined)
  // (C++, its dump filtered to the class: each variable outside it the class reads, a namespace's constant, dumped too)
  if (cpp && opts.entry && !smallTU(file, flags, opts.clang ?? 'clang++')) {
    const have = new Set<string>(), want = new Map<string, string>()
    const walk = (n: {kind: string, id?: string, name?: string, inner?: unknown[], referencedDecl?: {id: string, kind: string, name: string}}) => { if (n.kind === 'VarDecl' && n.id) have.add(n.id); const d = n.referencedDecl; if (n.kind === 'DeclRefExpr' && d?.kind === 'VarDecl') want.set(d.id, d.name); for (const c of n.inner ?? []) walk(c as never) }
    walk(tu as never)
    // (and each struct a method takes by reference or pointer, the caller's object: its fields read as inputs)
    const recs = new Set<string>(), haveRec = new Set<string>()
    const walkP = (n: {kind: string, name?: string, inner?: unknown[], type?: {qualType: string}}) => { if (/Record/.test(n.kind) && n.name) haveRec.add(n.name); if (n.kind === 'ParmVarDecl' && n.type) { const b = n.type.qualType.replace(/\b(const|volatile|struct|class)\b|[&*]/g, '').trim(); if (/^[A-Za-z_]\w*$/.test(b)) recs.add(b) } for (const c of n.inner ?? []) walkP(c as never) }
    walkP(tu as never)
    for (const name of [...recs].filter(r => !haveRec.has(r))) {
      try { const more = clangDump(file, flags, opts.clang ?? 'clang++', cpp, name).tu.inner ?? []; tu.inner = [...(tu.inner ?? []), ...more.filter(m => /^(CXX)?RecordDecl$/.test(m.kind) && m.name === name && m.completeDefinition)] } catch { /* read where it is, as before */ }
    }
    for (const name of new Set([...want].filter(([id]) => !have.has(id)).map(([, n]) => n))) {
      try { const more = clangDump(file, flags, opts.clang ?? 'clang++', cpp, name).tu.inner ?? []; const ids = [...want].filter(([id, n]) => n === name && !have.has(id)).map(([id]) => id); for (const m of more) if (m.kind === 'VarDecl' && m.name === name) for (const id of ids) tu.inner = [...(tu.inner ?? []), {...m, id}] } catch { /* read where it is, as before */ }
    }
  }
  // (no entry: the file's one struct its functions write, each struct of the dump tried)
  if (!opts.entry) {
    // (each struct by its tag or a typedef's name, an unnamed one's typedef too, that a function of the file takes a
    // pointer to first)
    const firsts = new Set((tu.inner ?? []).filter(n => n.kind === 'FunctionDecl' && n.inner?.some(c => c.kind === 'CompoundStmt')).map(n => n.inner!.find(c => c.kind === 'ParmVarDecl')?.type?.qualType.replace(/\b(const|volatile|struct)\b|\*/g, '').trim()).filter((t): t is string => !!t))
    const typedefNames = (tu.inner ?? []).filter(n => n.kind === 'TypedefDecl' && (n.inner ?? []).some(c => /Record|Elaborated/.test(c.kind))).map(n => String(n.name))
    const names = [...new Set([...(tu.inner ?? []).filter(n => n.kind === 'RecordDecl' && n.name && n.completeDefinition).map(n => String(n.name)), ...typedefNames])].filter(n => firsts.has(n))
    const ok = names.filter(n => { try { const c = readC(file, n, tu, target, cpp, opts.root); readGo(c.pkg, {methods: c.methods}); return true } catch (e) { if (e instanceof Refusal) return false; throw e } })
    // (none: the file's globals, where its functions keep the state there)
    if (!ok.length && !cpp) {
      const stem = file.replace(/^.*\//, '').replace(/\.[^.]*$/, '')
      try { const r = readCFile(file, {...opts, entry: stem}, cpp); readGo(r.c.pkg, {methods: r.c.methods, ...(opts.onError ? {onError: opts.onError} : {})} as GoOptions); return r } catch (e) {
        if (!(e instanceof Refusal)) throw e
        // (its globals are its state, and something in them is refused: that, not the structs)
        if (!/^no global of /.test(e.what)) throw new Refusal(e.where, `${e.what} (the file's globals read as its state, ${stem}: no struct its functions write)`)
      }
    }
    if (ok.length !== 1) throw new Refusal(file, ok.length ? `several structs written by the file's functions (${ok.join(', ')}): name one (entry)` : 'no struct the file\'s functions write: name the entry')
    return readCFile(file, {...opts, entry: ok[0]!}, cpp)
  }
  return {c: readC(file, opts.entry, tu, target, cpp, opts.root, Object.fromEntries((opts.functions ?? []).filter(f => f.includes('/')).map(f => [f.split('/')[0]!, Number(f.split('/')[1])])), (opts.functions ?? opts.methods ?? []).map(f => f.split('/')[0]!), opts.leave ?? [], [...Object.keys(opts.answers ?? {}), ...(opts.cut ?? [])]), flags}
}
export function extractC(at: string | FileURL, given: COptions = {}, cpp = false): Extraction & {leaves?: GoLeaf[]} {
  const notes: string[] = [], file = pathOf(at), fns = given.methods ?? given.functions, opts: COptions = {...given, ...(fns ? {functions: fns} : {})}
  let read: GoRead, c: CRead, flags: string[]
  try {
    ;({c, flags} = readCFile(file, opts, cpp))
    c.pkg.dir = node<{resolve: (p: string) => string}>('node:path').resolve(file).replace(/\/[^/]*$/, '')
    read = readGo(c.pkg, {entry: c.entry, methods: opts.functions?.map(f => f.split('/')[0]!) ?? c.methods, ...(opts.onError ? {onError: opts.onError} : {}), ...(opts.fails ? {fails: opts.fails} : {}), ...(opts.strict ? {strict: true} : {}), ...(opts.answers ? {answers: opts.answers} : {}), ...(opts.skip ? {skip: opts.skip} : {})} as GoOptions)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  // (a signed leaf the caller states is a natural: its range law from 0, the claim for those states)
  for (const [n, d] of Object.entries(opts.domains ?? {})) if (d === 'nat') read.model.laws = read.model.laws?.map(l => (l.includes(`"${n} within its type's range"`) ? l.replace(/\.atLeast\(-\d+\)/, '.atLeast(0)') : l))
  if (!opts.entry) read.model.notes.unshift(`the entry inferred: ${c.entry}, ${cpp ? 'the class whose methods write its state' : 'the struct the file\'s functions write'}`)
  // (the names the laws read that the code defines as constants: its enum constants, else clang's value of each)
  // (a qualified one, C++'s vehicle_status_s::ARMING_STATE_ARMED, by its law's spelling, vehicle_status_s.ARMING_STATE_ARMED)
  const keep = ((given as {keep?: string[]}).keep ?? []).filter(n => !(n in c.consts)), found = keep.length ? constantsOf(file, flags, opts.clang ?? (cpp ? 'clang++' : 'clang'), cpp, keep) : {}
  const consts = {...c.consts, ...Object.fromEntries(Object.entries(found).map(([k, v]) => [k.replaceAll('::', '.'), v]))}
  const x = fromModel(read.model, `${c.entry}.${cpp ? 'cpp' : 'c'}`, {...unsignedDomains(read), ...signedDomains(c.pkg, read), ...opts.domains}, notes, (rule, sorts) => checkC(file, flags, c, read, rule, sorts, opts, cpp))
  return {...x, leaves: read.leaves, names: goNames(read), ...(Object.keys(consts).length ? {consts} : {})}
}

// A signed field (and a signed result) is an integer, never inferred a natural: its range law reads below 0.
function signedDomains(pkg: GoPkg, read: GoRead): Record<string, 'int'> {
  const out: Record<string, 'int'> = {}
  for (const l of read.leaves) if (l.kind === 'int' && ty(pkg, l.t).signed !== false) out[l.name] = 'int'
  for (const l of read.leaves) if (l.kind === 'list' && ty(pkg, ty(pkg, l.t).elem!).k === 'int' && ty(pkg, ty(pkg, l.t).elem!).signed !== false) out[`${l.name}.$item`] = 'int'
  for (const m of read.methods) if (m.results[0] !== undefined && ty(pkg, m.results[0]).k === 'int' && ty(pkg, m.results[0]).signed !== false) out[`${m.name}_result`] = 'int'
  return out
}

// The C++ front end (`gdp-wired/extract-cpp`): a class, its public methods the requests, its constructor the start (its
// parameters the rule's); `this` and references are pointers into the state, std::array a fixed array, std::min and
// std::max, std::lock_guard, std::scoped_lock and std::unique_lock of a member mutex the step atomic (Go's Lock with its
// deferred Unlock), a throw the step's refusal. Refused: templates, virtual methods, overloads, other classes' methods,
// STL containers but std::array, lambdas, try and catch.
export const extractCpp = (at: string | FileURL, opts: COptions = {}) => extractC(at, opts, true)

// --- the harness: C (or C++) that #includes the file, sets and prints the state's leaves as JSON lines -------------------
const ty = (pkg: GoPkg, t: number) => pkg.ttab[t] ?? {k: 'invalid'}
export function harnessC(file: string, c: CRead, read: GoRead, opts: COptions, cpp: boolean): string {
  const pkg = c.pkg, T = (t: number) => ty(pkg, t), q = JSON.stringify, robs: string[] = []
  // A leaf's place: o->a.b in C; in C++ each member through a pointer to it the explicit instantiation of gdp_rob takes
  // (access isn't checked there), so private members are read and set as the class's own code does.
  const G = c.globals
  const acc = (path: string[]) => {
    if (!cpp || G) return `o->${path.join('.')}`
    let e = '(*o)', t = pkg.types[0]!.t
    for (const f of path) {
      const r = T(t), k = `&${t === pkg.types[0]!.t ? c.cname : r.go}::${f}`
      if (!robs.includes(k)) robs.push(k)
      e = `(${e}.*gdp_ptr(gdp_tag${robs.indexOf(k)}()))`; t = r.fields!.find(g => g.name === f)!.t
    }
    return e
  }
  const cast = (dst: string, t: number) => (cpp ? `std::remove_reference_t<decltype(${dst})>` : T(t).go!)
  const get: string[] = [], set: string[] = []
  const intOut = (e: string, t: number) => (T(t).signed === false ? `gdp_putf("\\"%llu\\"", (unsigned long long)(${e}))` : `gdp_putf("\\"%lld\\"", (long long)(${e}))`)
  const intIn = (dst: string, raw: string, t: number, err: string) => `{ long long s_; unsigned long long u_; if (!gdp_int(${raw}, ${T(t).bits ?? 64}, ${T(t).signed === false ? 0 : 1}, &s_, &u_)) ${err}; ${dst} = (${cast(dst, t)})(${T(t).signed === false ? 'u_' : 's_'}); }`
  for (const l of read.leaves) {
    const a = acc(l.path), k = q(l.name)
    if (l.kind === 'int') { get.push(`gdp_putf("%s\\"%s\\":", sep, ${k}); sep = ","; ${intOut(a, l.t)};`); set.push(`if ((v = gdp_key(st, ${k}))) ${intIn(a, 'v', l.t, `return "${l.name} outside its type"`)}`) }
    else if (l.kind === 'list') {
      // (a fixed array: all its items, exactly its length set)
      const at = T(l.t), n = at.len!, et = at.elem!, item = (e: string) => (T(et).k === 'int' ? intOut(e, et) : `gdp_putf("%s", ${e} ? "true" : "false")`)
      get.push(`gdp_putf("%s\\"%s\\":[", sep, ${k}); sep = ","; for (int i = 0; i < ${n}; i++) { if (i) gdp_putf(","); ${item(`${a}[i]`)}; } gdp_putf("]");`)
      set.push(`if ((v = gdp_key(st, ${k}))) { for (int i = 0; i < ${n}; i++) { const char *e = gdp_idx(v, i); if (!e) return "${l.name}: not ${n} items"; ${T(et).k === 'int' ? intIn(`${a}[i]`, 'e', et, `return "${l.name}: an item outside its type"`) : `${a}[i] = !strncmp(e, "true", 4);`} } if (gdp_idx(v, ${n})) return "${l.name}: not ${n} items"; }`)
    } else if (l.kind === 'bool') { get.push(`gdp_putf("%s\\"%s\\":%s", sep, ${k}, ${a} ? "true" : "false"); sep = ",";`); set.push(`if ((v = gdp_key(st, ${k}))) { if (!strncmp(v, "true", 4)) ${a} = ${T(l.t).nullflag ? '(void *)1' : '1'}; else if (!strncmp(v, "false", 5)) ${a} = 0; else return "${l.name}: not a boolean"; }`) }
  }
  const frames = read.leaves.filter(l => l.kind === 'frame' && !T(l.t).mutex)
  // (a field left out that points to an object other code owns, a buffer: a zeroed one of its own, as the code's setup
  // would give)
  const et = T(pkg.types[0]!.t), leftPtrs = cpp || G ? [] : (opts.leave ?? []).filter(f => { const fd = et.fields?.find(g => g.name === f); return fd && T(fd.t).k === 'ptr' && ['struct', 'int', 'bool'].includes(T(T(fd.t).elem!).k) })
  // (the longest method name the request names, in UTF-8 bytes, its buffer: a name of any length is called)
  const M = Math.max(256, ...read.methods.map(x => new TextEncoder().encode(x.name).length + 1))
  const calls = read.methods.map(meth => {
    const lines: string[] = [], args: string[] = ['o'], outs: [string, string, number][] = [], given: [string, string][] = []
    meth.params.forEach((pa, i) => {
      // (a global the request gives: set before the call, not passed)
      const push = (a: string) => { if (G?.inputs.includes(pa.name) && i >= meth.params.length - G.inputs.filter(n => meth.params.some(q => q.name === n)).length) given.push([pa.name, a]); else args.push(a) }
      const t = T(pa.t), raw = `gdp_idx(a, ${i})`
      if (pa.arg.k === 'input') {
        lines.push(`${t.go} a${i}; memset(&a${i}, 0, sizeof a${i}); const char *r${i} = ${raw}; if (!r${i}) return "no argument ${i}";`)
        lines.push(t.k === 'int' ? intIn(`a${i}`, `r${i}`, pa.t, `return "argument ${i} outside its type"`) : `a${i} = !strncmp(r${i}, "true", 4);`)
        push(`a${i}`)
      } else if (pa.arg.k === 'rec' && t.k === 'ptr' && T(t.elem!).box) {
        // (an out-parameter: a local of its type, its address given, what is left in it reported)
        const et = T(t.elem!).fields![0]!.t
        lines.push(`${T(et).go} a${i} = 0; const char *r${i} = ${raw}; if (r${i} && (v = gdp_key(r${i}, "value"))) ${T(et).k === 'int' ? intIn(`a${i}`, 'v', et, `return "argument ${i} outside its type"`) : `a${i} = !strncmp(v, "true", 4);`}`)
        args.push(t.go?.trim().endsWith('&') ? `a${i}` : `&a${i}`); outs.push([pa.name, `a${i}`, et])
      } else if (pa.arg.k === 'rec') {
        const byValue = t.k !== 'ptr', st = byValue ? t : T(t.elem!)
        lines.push(`${st.go} a${i}; memset(&a${i}, 0, sizeof a${i}); const char *r${i} = ${raw}; if (!r${i}) return "no argument ${i}";`)
        for (const [f] of pa.arg.fields) {
          const ft = st.fields!.find(g => g.name === f)!.t
          lines.push(`if ((v = gdp_key(r${i}, ${q(f)}))) ${T(ft).k === 'int' ? intIn(`a${i}.${f}`, 'v', ft, `return "argument ${i}.${f} outside its type"`) : `a${i}.${f} = !strncmp(v, "true", 4);`}`)
        }
        push(byValue || t.go?.trim().endsWith('&') ? `a${i}` : `&a${i}`)
      } else lines.push(`return "an argument the harness can't make";`)
    })
    const rt = meth.results[0], fails = opts.fails?.[meth.name]?.trim()
    const callee = G ? `${meth.name}(${args.slice(1).join(', ')})` : cpp ? `o->${meth.name}(${args.slice(1).join(', ')})` : `${meth.name}(${args.join(', ')})`
    const invoke = rt === undefined ? `${callee};` : `${cpp ? 'auto' : T(rt).go} r0 = ${callee}; gdp_has = 1; ${T(rt).k === 'int' ? `gdp_outv = ${T(rt).signed === false ? '(long long)' : ''}r0; gdp_outu = ${T(rt).signed === false ? 1 : 0};` : 'gdp_outb = r0; gdp_isb = 1;'}`
    const failed = fails !== undefined && rt !== undefined ? `if (r0 ${fails.replace(/^(==|!=|<=|>=|<|>)\s*/, '$1 ')}) gdp_err = 1;` : ''
    // (with out-parameters, the result is a record: the value returned and what each holds)
    const rec = outs.length ? `gdp_rec = 1; gdp_putf(",\\"out\\":{"); ${[...(rt !== undefined ? [['result', 'r0', rt] as [string, string, number]] : []), ...outs].map(([n, v, et], j) => `gdp_putf("${j ? ',' : ''}\\"${n}\\":"); ${T(et).k === 'int' ? `gdp_putf(${T(et).signed === false ? '"%llu", (unsigned long long)' : '"%lld", (long long)'}(${v}))` : `gdp_putf("%s", ${v} ? "true" : "false")`};`).join(' ')} gdp_putf("},\\"hasOut\\":true");` : ''
    const load = G ? `gdp_load(o); ${given.map(([n, a]) => `memcpy((void *)&${n}, (const void *)&${a}, sizeof ${n});`).join(' ')}\n    ` : ''
    return `if (!strcmp(m, ${q(meth.name)})) {\n    ${lines.join('\n    ')}\n    memcpy(gdp_pre, (void *)o, sizeof(gdp_T));\n    ${load}int sg = sigsetjmp(gdp_jb, 1);\n    if (!sg) { gdp_armed = 1; gdp_watch(1); ${cpp ? 'try { ' : ''}${invoke} ${failed} gdp_watch(0); gdp_armed = 0; ${rec}${cpp ? ' } catch (...) { gdp_watch(0); gdp_armed = 0; gdp_sig = SIGUSR2; }' : ''} } else { gdp_watch(0); gdp_sig = sg; }\n    ${G ? 'gdp_store(o);\n    ' : ''}return gdp_after(o);\n  }`
  })
  const frameLines = frames.map(l => { const e = acc(l.path); return `if (memcmp((char *)&${e}, (char *)gdp_pre + ((char *)&${e} - (char *)o), sizeof ${e})) return ${q(l.path.join('.'))};` })
  // The object, made as the code makes it: C's zeroed; C++'s constructed (in zeroed memory) with the rule's parameters.
  const cps = read.ctor ?? [], make = `static gdp_T *gdp_make(const char *line, const char **bad) {
  const char *a = gdp_key(line, "a"), *v; (void)a; (void)v;
  ${cps.map((pa, i) => `${T(pa.t).go} c${i}${cpp ? '{}' : ' = 0'}; if (!(v = a ? gdp_idx(a, ${i}) : 0)) { *bad = "no argument ${i}"; return 0; } ${T(pa.t).k === 'int' ? intIn(`c${i}`, 'v', pa.t, `{ *bad = "argument ${i} outside its type"; return 0; }`) : `c${i} = !strncmp(v, "true", 4);`}`).join('\n  ')}
  void *mem = calloc(1, sizeof(gdp_T));${G ? '\n  memcpy(mem, &gdp_init, sizeof(gdp_T));' : ''}${leftPtrs.map(f => `\n  ((gdp_T *)mem)->${f} = calloc(1, sizeof *((gdp_T *)mem)->${f});`).join('')}
  return ${cpp ? `new (mem) gdp_T(${cps.map((_, i) => `c${i}`).join(', ')})` : '(gdp_T *)mem'};
}`
  return `// Generated by gdp-wired's ${cpp ? 'C++' : 'C'} check (core/extract-c.ts): the file's code is called as it is.
${read.answers?.length ? `// The stub point of an answered call, by the callee's name (each call rewritten to it in the file's copy): the
// request's input for it, 0 where it is none.
#include <stdlib.h>
static const char *gdp_answers;
static const char *gdp_key(const char *p, const char *k);
static long long gdp_answer(const char *name) {
  const char *a = gdp_answers ? gdp_key(gdp_answers, name) : 0, *v = a ? gdp_key(a, "in") : 0;
  if (!v) return 0;
  if (*v == '"') v++;
  return strtoll(v, 0, 10);
}
` : ''}#define main gdp_orig_main
#include ${q(file)}
#undef main
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <setjmp.h>
#include <errno.h>
#include <sys/time.h>
${cpp ? '#include <new>\n#include <type_traits>\n' : '#include <stdbool.h>\n'}
${G ? `// The file's globals, the state: an object of them each request loads, and stores back after it.
${G.externs.map(n => `__typeof__(${n}) ${n};`).join('\n')}
typedef struct { ${G.state.map(n => `${cpp ? `std::remove_cv_t<decltype(${n})>` : `__typeof__(${n})`} ${n};`).join(' ')} } gdp_G;
static void gdp_load(const gdp_G *o) { ${G.state.map(n => `memcpy((void *)&${n}, (const void *)&o->${n}, sizeof ${n});`).join(' ')} }
static void gdp_store(gdp_G *o) { ${G.state.map(n => `memcpy((void *)&o->${n}, (const void *)&${n}, sizeof ${n});`).join(' ')} }
static gdp_G gdp_init;
` : ''}typedef ${c.cname} gdp_T;
static unsigned char gdp_pre[sizeof(gdp_T)];
${robs.length ? `template <typename Tag, auto M> struct gdp_rob { friend auto gdp_ptr(Tag) { return M; } };\n${robs.map((k, i) => `struct gdp_tag${i} { friend auto gdp_ptr(gdp_tag${i}); };\ntemplate struct gdp_rob<gdp_tag${i}, ${k}>;`).join('\n')}` : ''}
static char *gdp_buf; static size_t gdp_n, gdp_cap;
static void gdp_putf(const char *f, ...) {
  va_list ap; va_start(ap, f); char tmp[512]; int k = vsnprintf(tmp, sizeof tmp, f, ap); va_end(ap);
  if (gdp_n + k + 1 > gdp_cap) { gdp_cap = (gdp_n + k + 1) * 2; gdp_buf = (char *)realloc(gdp_buf, gdp_cap); }
  memcpy(gdp_buf + gdp_n, tmp, k + 1); gdp_n += k;
}
static const char *gdp_ws(const char *p) { while (*p == ' ' || *p == '\\t' || *p == '\\n' || *p == '\\r') p++; return p; }
static const char *gdp_skip(const char *p) {
  p = gdp_ws(p);
  if (*p == '"') { p++; while (*p && *p != '"') { if (*p == '\\\\' && p[1]) p++; p++; } return *p ? p + 1 : p; }
  if (*p == '{' || *p == '[') { int d = 0; do { if (*p == '"') { p = gdp_skip(p); continue; } if (*p == '{' || *p == '[') d++; else if (*p == '}' || *p == ']') d--; p++; } while (*p && d > 0); return p; }
  while (*p && *p != ',' && *p != '}' && *p != ']') p++;
  return p;
}
// (a key's value in an object, an item of an array)
static const char *gdp_key(const char *o, const char *key) {
  const char *p = gdp_ws(o); size_t n = strlen(key);
  if (*p != '{') return 0; p++;
  for (;;) {
    p = gdp_ws(p); if (*p != '"') return 0;
    const char *k = p + 1, *e = strchr(k, '"'); if (!e) return 0;
    p = gdp_ws(e + 1); if (*p == ':') p++; p = gdp_ws(p);
    if ((size_t)(e - k) == n && !strncmp(k, key, n)) return p;
    p = gdp_ws(gdp_skip(p)); if (*p == ',') p++; else return 0;
  }
}
static const char *gdp_idx(const char *a, int i) {
  const char *p = gdp_ws(a); if (*p != '[') return 0; p++;
  for (int j = 0;; j++) { p = gdp_ws(p); if (*p == ']' || !*p) return 0; if (j == i) return p; p = gdp_ws(gdp_skip(p)); if (*p == ',') p++; }
}
static int gdp_int(const char *v, int bits, int sgn, long long *s, unsigned long long *u) {
  char tmp[64]; size_t n = 0; v = gdp_ws(v); if (*v == '"') v++;
  while (*v && *v != '"' && *v != ',' && *v != '}' && *v != ']' && n < 63) tmp[n++] = *v++;
  tmp[n] = 0; if (!n) return 0;
  char *end; errno = 0;
  if (sgn) { long long x = strtoll(tmp, &end, 10); if (*end || errno) return 0; if (bits < 64 && (x < -(1LL << (bits - 1)) || x > (1LL << (bits - 1)) - 1)) return 0; *s = x; }
  else { if (tmp[0] == '-') return 0; unsigned long long x = strtoull(tmp, &end, 10); if (*end || errno) return 0; if (bits < 64 && x > (1ULL << bits) - 1) return 0; *u = x; }
  return 1;
}
static void gdp_get(gdp_T *o) {
  const char *sep = ""; (void)sep; (void)o;
  gdp_putf("{");
  ${get.join('\n  ')}
  gdp_putf("}");
}
static const char *gdp_set(gdp_T *o, const char *st) {
  const char *v; (void)v; (void)o; (void)st;
  ${set.join('\n  ')}
  return 0;
}
static sigjmp_buf gdp_jb; static volatile sig_atomic_t gdp_armed;
static int gdp_sig, gdp_err, gdp_has, gdp_outu, gdp_isb, gdp_rec; static long long gdp_outv; static bool gdp_outb;
static void gdp_on(int s) { if (gdp_armed) { gdp_armed = 0; siglongjmp(gdp_jb, s); } signal(s, SIG_DFL); raise(s); }
// (a call that doesn't return within 2 s, an endless loop: the code's failure, as the rule's)
static void gdp_watch(int on) { struct itimerval t; memset(&t, 0, sizeof t); t.it_value.tv_sec = on ? 2 : 0; setitimer(ITIMER_REAL, &t, 0); }
static const char *gdp_frame(gdp_T *o) {
  (void)o;
  ${frameLines.join('\n  ')}
  return 0;
}
// (another file's function, linked as a stub, reached: the step's failure)
static const char *gdp_extern;
${cpp ? 'extern "C" ' : ''}void gdp_extern_called(const char *n) { gdp_extern = n; if (gdp_armed) { gdp_armed = 0; siglongjmp(gdp_jb, SIGUSR1); } abort(); }
static const char *gdp_after(gdp_T *o) {
  const char *f = gdp_frame(o);
  if (f) { gdp_putf(",\\"frame\\":\\"%s\\"", f); }
  if (gdp_sig) gdp_putf(",\\"panic\\":\\"%s\\"", gdp_sig == SIGABRT ? "SIGABRT (abort, or an assertion failing)" : gdp_sig == SIGTRAP || gdp_sig == SIGILL ? "undefined behavior (the sanitizer's trap)" : gdp_sig == SIGUSR1 ? "another file's function called" : gdp_sig == SIGUSR2 ? "an exception thrown" : gdp_sig == SIGALRM ? "the code didn't return (an endless loop)" : "a signal");
  else if (gdp_err) gdp_putf(",\\"err\\":\\"its result is its failure (%lld)\\"", gdp_outv);
  if (!gdp_sig && gdp_has && !gdp_rec) { if (gdp_isb) gdp_putf(",\\"out\\":%s,\\"hasOut\\":true", gdp_outb ? "true" : "false"); else if (gdp_outu) gdp_putf(",\\"out\\":\\"%llu\\",\\"hasOut\\":true", (unsigned long long)gdp_outv); else gdp_putf(",\\"out\\":\\"%lld\\",\\"hasOut\\":true", gdp_outv); }
  if (${opts.onError === 'discard' ? 1 : 0} && (gdp_sig || gdp_err)) memcpy((void *)o, gdp_pre, sizeof(gdp_T));
  gdp_putf(",\\"state\\":"); gdp_get(o);
  return 0;
}
${make}
static const char *gdp_call(gdp_T *o, const char *m, const char *a) {
  const char *v; (void)v; (void)a;
  gdp_sig = gdp_err = gdp_has = gdp_outu = gdp_isb = gdp_rec = 0; gdp_outv = 0;
  ${calls.join('\n  ')}
  return "no such function";
}
int main(int argc, char **argv) {
  ${G ? 'gdp_store(&gdp_init);\n  ' : ''}if (argc == 2 && !strcmp(argv[1], "--probe")) return 0;
  if (argc < 3) return 2;
  FILE *in = fopen(argv[1], "r"), *out = fopen(argv[2], "w");
  if (!in || !out) return 2;
  int sigs[] = {SIGABRT, SIGTRAP, SIGILL, SIGFPE, SIGSEGV, SIGBUS, SIGALRM};
  for (unsigned i = 0; i < sizeof sigs / sizeof *sigs; i++) signal(sigs[i], gdp_on);
  gdp_T **objs = 0; size_t nobj = 0;
  char *line = 0; size_t lcap = 0;
  for (;;) {
    size_t ln = 0; int ch;
    while ((ch = fgetc(in)) != EOF && ch != '\\n') { if (ln + 2 > lcap) { lcap = lcap ? lcap * 2 : 4096; line = (char *)realloc(line, lcap); } line[ln++] = (char)ch; }
    if (ch == EOF && !ln) break;
    if (!line) continue;
    line[ln] = 0;
    const char *op = gdp_key(line, "op"), *id = gdp_key(line, "id");
    long long k = 0; unsigned long long ku; if (id) gdp_int(id, 64, 1, &k, &ku);
    gdp_n = 0;
    if (op && !strncmp(op, "\\"new\\"", 5)) { const char *bad = 0; gdp_T *o = gdp_make(line, &bad); if (!o) gdp_putf("{\\"bad\\":\\"%s\\"}", bad); else { objs = (gdp_T **)realloc(objs, ++nobj * sizeof *objs); objs[nobj - 1] = o; gdp_putf("{\\"id\\":%zu}", nobj); } }
    else if (op && !strncmp(op, "\\"at\\"", 4)) {
      const char *bad = 0; gdp_T *o = gdp_make(line, &bad); const char *st = gdp_key(line, "state");
      if (o) bad = st ? gdp_set(o, st) : "no state";
      if (bad) gdp_putf("{\\"bad\\":\\"%s\\"}", bad);
      else { objs = (gdp_T **)realloc(objs, ++nobj * sizeof *objs); objs[nobj - 1] = o; gdp_putf("{\\"id\\":%zu}", nobj); }
    }
    else if (op && !strncmp(op, "\\"get\\"", 5)) { gdp_putf("{\\"state\\":"); gdp_get(objs[k - 1]); gdp_putf("}"); }
    else if (op && !strncmp(op, "\\"call\\"", 6)) {
      const char *mv = gdp_key(line, "m"), *av = gdp_key(line, "a"); char m[${M}] = {0};
      if (mv && *mv == '"') { const char *e = strchr(mv + 1, '"'); size_t n = e ? (size_t)(e - mv - 1) : 0; if (n > ${M - 1}) n = ${M - 1}; memcpy(m, mv + 1, n); }
      gdp_putf("{\\"ok\\":true");${read.answers?.length ? `
      gdp_answers = gdp_key(line, "answers");` : ''}
      const char *bad = gdp_call(objs[k - 1], m, av ? av : "[]");
      if (bad) { gdp_n = 0; gdp_putf("{\\"bad\\":\\"%s\\"", bad); }
      gdp_putf("}");
    }
    fputs(gdp_buf ? gdp_buf : "{}", out); fputc('\\n', out); fflush(out);
  }
  return 0;
}
`
}

// (a fixed array last in a struct is still of its length, its index checked: clang 15 and later)
const flexOK = new Map<string, boolean>()
function strictFlex(clang: string): string[] {
  if (!flexOK.has(clang)) { try { node<CP>('node:child_process').execFileSync(clang, ['-fstrict-flex-arrays=3', '-x', 'c', '-fsyntax-only', '/dev/null'], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe']}); flexOK.set(clang, true) } catch { flexOK.set(clang, false) } }
  return flexOK.get(clang) ? ['-fstrict-flex-arrays=3'] : []
}
// A demangled C++ function's own name: `void events::send<A, B>(unsigned int, ...)` is send, `A::f(int) const` f.
function shortName(d: string): string | undefined {
  let depth = 0, end = -1
  for (let i = 0; i < d.length; i++) { const ch = d[i]; if (ch === '<') depth++; else if (ch === '>') depth--; else if (ch === '(' && depth === 0) { end = i; break } }
  if (end < 0) return undefined
  let head = d.slice(0, end), out = '', dd = 0
  for (const ch of head) { if (ch === '<') dd++; else if (ch === '>') dd--; else if (dd === 0) out += ch }
  head = out.trim().split(/\s+/).pop() ?? ''
  return head.split('::').pop() || undefined
}
// --- the check ------------------------------------------------------------------------------------------------------------
export function checkC(file: string, flags: string[], c: CRead, read: GoRead, r: Rule, sorts: Sorts, opts: COptions, cpp: boolean): GoEvidence {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string, platform: () => string}>('node:os'), path = node<{resolve: (p: string) => string}>('node:path')
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-ccheck-`), b0 = performance.now()
  // (each answered call rewritten to the harness's answer in a copy of the file, its own includes found beside it)
  const copy = stubbed(read as never, f => fs.readFileSync(`${path.resolve(file).replace(/[^/]*$/, '')}${f}`, 'utf8'), a => `((${a.ty})gdp_answer(${JSON.stringify(a.key)}))`)
  for (const [f, t] of copy) fs.writeFileSync(`${work}/${f}`, t)
  const code = harnessC(copy.size ? `${work}/${path.resolve(file).split('/').pop()}` : path.resolve(file), c, read, opts, cpp)
  if (copy.size) flags = [...flags, '-iquote', path.resolve(file).replace(/\/[^/]*$/, '')]
  const empty = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, buildMs: 0, runMs: 0}
  try {
    const h = `${work}/harness.${cpp ? 'cpp' : 'c'}`
    fs.writeFileSync(h, code)
    if (opts.check?.keep) { fs.mkdirSync(opts.check.keep, {recursive: true}); fs.writeFileSync(`${opts.check.keep}/harness.${cpp ? 'cpp' : 'c'}`, code) }
    // The same flags; undefined behavior trapped (the rule refuses it, so the code must fail there too); another
    // file's functions linked as stubs that report themselves (the rule refuses their calls: one reached is the
    // code's failure where the rule took the step, a difference), but those left out (skip, stated or inferred: they
    // change nothing the rule keeps, and nothing reads their value), which do nothing.
    const clang = opts.clang ?? (cpp ? 'clang++' : 'clang'), stubs = `${work}/gdp_stubs.c`
    const run = (cc: string, args: string[]) => cp.execFileSync(cc, args, {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26, timeout: compileLimit(), killSignal: 'SIGKILL'})
    // (the stubs are C, compiled apart: the project's flags, a C++ -std among them, are the harness's)
    const link = (more: string[]) => { for (const m of more) run(clang.replace(/\+\+$/, ''), ['-w', '-c', '-x', 'c', m, '-o', `${m}.o`]); return run(clang, [...(cpp ? ['-x', 'c++'] : []), ...flags, '-w', '-O0', '-fsanitize=undefined', '-fsanitize-trap=undefined', '-fno-sanitize=vptr,function', ...strictFlex(clang), h, ...(more.length ? ['-x', 'none', ...more.map(m => `${m}.o`)] : []), '-o', `${work}/harness`]) }
    const why = (x: unknown) => String((x as {stderr?: string}).stderr ?? (x as Error).message)
    // (the compiler's errors: where they are in the code's own files, the source's; the linker's alone say nothing of it)
    const base = path.resolve(file).split('/').pop()!, errorsOf = (x: unknown) => why(x).split('\n').filter(l => /\berror:/.test(l) && !/linker command failed|ld returned/.test(l))
    const ofSource = (l: string) => !/(^|\/)(harness\.(c|cpp)|gdp_stubs\.c):/.test(l) && (l.includes(`${base}:`) || !l.includes(work))
    try { link([]) } catch (x) {
      // (C's names: a C++ one is demangled, `A::f(int)`, below)
      const names = [...new Set([...why(x).matchAll(/undefined (?:reference to [`']|symbol: )_?([A-Za-z_]\w*)(?=['`]|$)|"_([A-Za-z_]\w*)", referenced from/gm)].map(m => m[1] ?? m[2]!))]
      // (C++: the linker names other code's functions demangled, `A::f(int) const`: their own names from the object's
      // undefined symbols, each matched by its demangled form; a stub is named so, `void _ZNK1A1fEi(void)`)
      const demangled = new Set([...why(x).matchAll(/"([^"]+)", referenced from|undefined reference to [`']([^'`]+)'/g)].map(m => m[1] ?? m[2]!).filter(d => /[:(]/.test(d)))
      const base = new Map<string, string>()
      if (cpp && demangled.size) {
        try {
          run(clang, ['-x', 'c++', ...flags, '-w', '-O0', '-fsanitize=undefined', '-fsanitize-trap=undefined', '-fno-sanitize=vptr,function', ...strictFlex(clang), '-c', h, '-o', `${work}/harness.o`])
          const und = run('nm', ['-u', `${work}/harness.o`]).split('\n').map(l => l.trim().replace(/^U\s+/, '')).filter(Boolean)
          const out = cp.execFileSync('c++filt', [], {input: und.join('\n'), encoding: 'utf8'}).split('\n')
          und.forEach((m, i) => { const d = out[i]?.trim() ?? ''; if (demangled.has(d) || demangled.has(d.replace(/^_/, ''))) { const n = m.replace(/^_(?=_Z)/, ''); if (/^\w+$/.test(n)) { names.push(n); base.set(n, shortName(d) ?? n) } } })
        } catch { /* the names the linker gave */ }
      }
      if (!names.length) { const b = buildCheck(clang, () => link([]), errorsOf, ofSource, x); if (!('ok' in b)) return {...empty, ...builtEvidence(b)} }
      else {
        // (left out by its name, or by its name and constant arguments, CO_error_x_1_27: answered per arguments)
        const left = new Set(read.leftOut ?? []), out = {has: (n: string) => left.has(n) || [...left].some(k => k.startsWith(`${n}_`) && /^[xm\d_]+$/.test(k.slice(n.length + 1)))}
        fs.writeFileSync(stubs, `void gdp_extern_called(const char *);\n${names.map(n => (out.has(n) || out.has(base.get(n) ?? '') ? `void ${n}(void) {}` : `void ${n}(void) { gdp_extern_called(${JSON.stringify(base.get(n) ?? n)}); }`)).join('\n')}\n`)
        const b = buildCheck(clang, () => link([stubs]), errorsOf, ofSource)
        if (!('ok' in b)) return {...empty, ...builtEvidence(b)}
      }
    }
    // (a harness that doesn't start would leave the pipes unopened: asked to start and stop first)
    try { cp.execFileSync(`${work}/harness`, ['--probe'], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], timeout: 20_000}) }
    catch (x) { return {...empty, mismatch: `the check's harness doesn't start: ${why(x).split('\n').filter(Boolean).slice(0, 3).join(' | ')}`} }
    const buildMs = Math.round(performance.now() - b0), none = (): Coverage => ({arms: 0, hit: 0, missed: []})
    return {...speak(work, `${work}/harness`, (globalThis as {process?: {env?: Record<string, string>}}).process?.env, c.pkg, read, r, sorts, opts.check ?? {}, none), buildMs}
  } finally {
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
}
