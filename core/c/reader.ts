// The C reader (core/extract-c.ts's): a file read through clang's own parser and type checker (`clang -Xclang
// -ast-dump=json -fsyntax-only`, with the project's flags), its own declarations kept (the dump holds every header's
// too), and put in the shape core/go/reader.go prints (core/extract-go.ts's GoPkg: a table of types, the functions'
// typed expressions and statements), so that one lowering, Go's, reads both: what C's semantics need beyond Go's is
// written here as Go's own nodes, made explicit where clang's types say so. Integer promotions and the usual arithmetic
// conversions are clang's ImplicitCastExpr nodes, each a conversion; a condition is a comparison with 0 (or NULL); a
// switch's case runs into the next unless it breaks (a fallthrough); `x op= y` computed at a wider type is
// `x = (T)(x op y)`; `x & (2^k − 1)` is x's floor remainder by 2^k (two's complement); assert and abort are panics; a signed type's
// overflow is undefined (`ub`, refused by the executor where it may be). What the subset doesn't read becomes a
// `no` node with why, refused where a step reaches it.
//
// The state is a struct of the file (`entry`, its typedef's name or its tag); each function whose first parameter
// points to it is a method of it (the receiver), the others plain functions.
import type {GS, GX, GoFunc, GoPkg, TT} from '../extract-go.ts'
import {Refusal} from '../extract-read.ts'

type CN = {id?: string, kind: string, name?: string, inner?: CN[], type?: {qualType: string, desugaredQualType?: string}, value?: string, opcode?: string, castKind?: string, isArrow?: boolean, isPostfix?: boolean,
  referencedDecl?: {id: string, kind: string, name: string}, referencedMemberDecl?: string, storageClass?: string, isImplicit?: boolean, completeDefinition?: boolean, tagUsed?: string, hasElse?: boolean,
  computeLHSType?: {qualType: string, desugaredQualType?: string}, init?: string, decl?: {id: string, kind: string}, loc?: L, range?: {begin: L, end: L}, $at?: At, $b?: At, $e?: At, [k: string]: unknown}
type L = {offset?: number, file?: string, line?: number, col?: number, tokLen?: number, spellingLoc?: L, expansionLoc?: L, includedFrom?: unknown}
type At = {file: string, line: number, col: number, off: number, tok: number}
export type CTarget = {int: number, long: number, short: number, llong: number, charUnsigned: boolean}
export type CRead = {pkg: GoPkg, methods: string[], entry: string, cname: string}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
const proc = (globalThis as {process?: {getBuiltinModule?: (id: string) => unknown}}).process
export const node = <T>(id: string): T => { const m = proc?.getBuiltinModule?.(id); if (!m) throw new Error(`the C front end runs clang through ${id} (Node 20.16 or later, or Bun)`); return m as T }

// --- running clang ------------------------------------------------------------------------------------------------------
export function clangDump(file: string, flags: string[], clang = 'clang', cpp = false): {tu: CN, target: CTarget} {
  const cp = node<CP>('node:child_process'), lang = cpp ? ['-x', 'c++'] : ['-x', 'c']
  const run = (args: string[]) => {
    try { return cp.execFileSync(clang, args, {encoding: 'utf8', maxBuffer: 1 << 30, stdio: ['ignore', 'pipe', 'pipe']}) }
    catch (e) {
      const x = e as {code?: string, stderr?: string, message: string}
      throw new Refusal(file, x.code === 'ENOENT' ? `no ${clang} to run: clang is needed to extract ${cpp ? 'C++' : 'C'}` : `clang doesn't compile it (${String(x.stderr ?? x.message).split('\n').filter(l => /error/.test(l)).slice(0, 3).join(' | ')})`)
    }
  }
  const tu = JSON.parse(run([...lang, ...flags, '-Xclang', '-ast-dump=json', '-fsyntax-only', file])) as CN
  const defs = run([...lang, ...flags, '-dM', '-E', '/dev/null']), def = (k: string) => Number(new RegExp(`#define ${k} (\\d+)`).exec(defs)?.[1] ?? 0)
  return {tu, target: {int: def('__SIZEOF_INT__') * 8, long: def('__SIZEOF_LONG__') * 8, short: def('__SIZEOF_SHORT__') * 8, llong: def('__SIZEOF_LONG_LONG__') * 8, charUnsigned: /#define __CHAR_UNSIGNED__/.test(defs)}}
}
// The project's flags for a file: from a compile_commands.json (its -I, -D, -std, -include and -f options), or given.
export function flagsFor(file: string, compileCommands?: string): string[] {
  if (!compileCommands) return []
  const fs = node<{readFileSync: (p: string, e: string) => string}>('node:fs'), path = node<{resolve: (...p: string[]) => string}>('node:path')
  const db = JSON.parse(fs.readFileSync(compileCommands, 'utf8')) as {directory: string, file: string, arguments?: string[], command?: string}[]
  const e = db.find(x => path.resolve(x.directory, x.file) === path.resolve(file))
  if (!e) throw new Refusal(file, `${compileCommands} has no command for it`)
  const args = e.arguments ?? (e.command ?? '').match(/(?:[^\s"']+|"[^"]*"|'[^']*')+/g)!.map(a => a.replace(/^["']|["']$/g, ''))
  const out: string[] = []
  for (let i = 1; i < args.length; i++) {
    const a = args[i]!
    if (/^-(I|D|U|include|isystem|iquote)$/.test(a)) { const v = args[++i]!; out.push(a, a === '-D' || a === '-U' ? v : path.resolve(e.directory, v)) }
    else if (/^-[IDU]./.test(a)) out.push(a.startsWith('-I') ? `-I${path.resolve(e.directory, a.slice(2))}` : a)
    else if (/^-(std=|f(un)?signed-char|m32|m64)/.test(a)) out.push(a)
  }
  return out
}

// Where each node is: clang writes a location's file and line only where they change from the last one it wrote, in
// the dump's order (an include's chain, `includedFrom`, doesn't count): read in that order, each node gets its own.
function locate(root: CN) {
  let file = '', line = 0
  const at = (l: L | undefined): At | undefined => {
    if (!l) return undefined
    if (l.spellingLoc || l.expansionLoc) { at(l.spellingLoc); return at(l.expansionLoc) }
    if (l.file !== undefined) file = l.file
    if (l.line !== undefined) line = l.line
    return l.offset === undefined ? undefined : {file, line, col: l.col ?? 0, off: l.offset, tok: l.tokLen ?? 0}
  }
  const walk = (n: CN) => {
    for (const k of Object.keys(n)) {
      if (k === 'loc') n.$at = at(n.loc)
      else if (k === 'range') { n.$b = at(n.range!.begin); n.$e = at(n.range!.end) }
      else if (k === 'inner') for (const c of n.inner!) walk(c)
    }
    n.$at ??= n.$b
  }
  walk(root)
}

const CMP = new Set(['==', '!=', '<', '<=', '>', '>=']), ARITH = new Set(['+', '-', '*', '/', '%', '<<', '>>', '&', '|', '^'])
const FAIL: Record<string, string> = {abort: 'abort()', __assert_rtn: 'an assertion failing', __assert_fail: 'an assertion failing', __assert: 'an assertion failing', _assert: 'an assertion failing', __builtin_trap: 'a trap', __builtin_unreachable: 'unreachable code reached (undefined behavior)'}

// --- the reading --------------------------------------------------------------------------------------------------------
// (`root`: the project's own files, whose functions are read too: a static inline helper of its header; by default the
// file's directory)
export function readC(file: string, entry: string, tu: CN, target: CTarget, cpp = false, root?: string): CRead {
  const path = node<{resolve: (...p: string[]) => string, basename: (p: string) => string}>('node:path'), fs = node<{readFileSync: (p: string, e: string) => string}>('node:fs')
  const main = path.resolve(file), base = path.basename(file), dir = `${path.resolve(root ?? main.replace(/\/[^/]*$/, ''))}/`, srcs = new Map<string, string>()
  locate(tu)
  const top = tu.inner ?? [], mine = (n: CN) => n.$at?.file === main || n.$at?.file === file, own = (n: CN) => mine(n) || (!!n.$at?.file && path.resolve(n.$at.file).startsWith(dir))
  const refuse = (n: CN | undefined, what: string): never => { throw new Refusal(pos(n), what) }
  const pos = (n: CN | undefined) => (n?.$at && own(n) ? `${path.basename(n.$at.file)}:${n.$at.line}:${n.$at.col}` : base)
  const src = (f: string) => { let s = srcs.get(f); if (s === undefined) { try { s = fs.readFileSync(path.resolve(f), 'utf8') } catch { s = '' }; srcs.set(f, s) } return s }
  const text = (n: CN) => (n.$b && n.$e && n.$b.file === n.$e.file && own(n) && n.$e.off + n.$e.tok >= n.$b.off ? src(n.$b.file).slice(n.$b.off, n.$e.off + n.$e.tok) || n.kind : n.kind)

  // The declarations: typedefs, records and enums of every file (a header's types are the file's too), the globals.
  const typedefs = new Map<string, {qual: string, desug?: string, rec?: string}>(), records = new Map<string, CN>(), tags = new Map<string, string>(), anon = new Map<string, string>()
  const enumConst = new Map<string, number>(), globals = new Map<string, CN>(), fields = new Map<string, {rec: string, i: number}>(), recName = new Map<string, string>()
  const declOf = (n: CN): {id: string, kind: string} | undefined => n.decl ?? (n.inner ?? []).map(declOf).find(Boolean)
  const visitDecl = (n: CN) => {
    if (n.kind === 'TypedefDecl' && n.name) {
      const d = declOf(n)
      typedefs.set(n.name, {qual: n.type!.qualType, ...(n.type!.desugaredQualType ? {desug: n.type!.desugaredQualType} : {}), ...(d && (d.kind === 'RecordDecl' || d.kind === 'CXXRecordDecl') ? {rec: d.id} : {})})
      if (d && !recName.has(d.id)) recName.set(d.id, n.name)
    } else if ((n.kind === 'RecordDecl' || n.kind === 'CXXRecordDecl') && n.completeDefinition) {
      records.set(n.id!, n)
      if (n.name) { tags.set(`${n.tagUsed} ${n.name}`, n.id!); if (cpp) tags.set(n.name, n.id!) }
      if (n.$at) anon.set(`${n.$at.line}:${n.$at.col}`, n.id!)
      let i = 0
      for (const f of n.inner ?? []) {
        if (f.kind === 'FieldDecl') fields.set(f.id!, {rec: n.id!, i: i++})
        else visitDecl(f)
      }
    } else if (n.kind === 'EnumDecl') {
      let v = -1
      for (const c of n.inner ?? []) if (c.kind === 'EnumConstantDecl') { const k = c.inner?.length ? fold(c.inner[0]!) : undefined; v = k ?? v + 1; enumConst.set(c.id!, v) }
    } else if (n.kind === 'VarDecl') globals.set(n.id!, n)
    else if (n.kind === 'LinkageSpecDecl' || n.kind === 'NamespaceDecl') for (const c of n.inner ?? []) visitDecl(c)
  }
  // A constant's value, where the node is one (literals, enum constants, a const global's, folded).
  const fold = (n: CN): number | undefined => {
    switch (n.kind) {
      case 'IntegerLiteral': case 'CharacterLiteral': return Number(n.value)
      case 'CXXBoolLiteralExpr': return n.value ? 1 : 0
      case 'ConstantExpr': return n.value !== undefined ? Number(n.value) : fold(n.inner![0]!)
      case 'ParenExpr': return fold(n.inner![0]!)
      case 'ImplicitCastExpr': case 'CStyleCastExpr': {
        const v = fold(n.inner![0]!), t = n.type ? T(tyOf(n.type)) : undefined
        if (v === undefined || t?.k !== 'int') return n.castKind === 'IntegralToBoolean' && v !== undefined ? +(v !== 0) : undefined
        const m = 2 ** t.bits!, w = ((v % m) + m) % m
        return t.signed && w >= m / 2 ? w - m : w
      }
      case 'UnaryOperator': { const v = fold(n.inner![0]!); return v === undefined ? undefined : n.opcode === '-' ? -v : n.opcode === '+' ? v : n.opcode === '!' ? +(v === 0) : undefined }
      case 'BinaryOperator': {
        const a = fold(n.inner![0]!), b = fold(n.inner![1]!)
        if (a === undefined || b === undefined) return undefined
        switch (n.opcode) {
          case '+': return a + b
          case '-': return a - b
          case '*': return a * b
          case '/': return b ? Math.trunc(a / b) : undefined
          case '%': return b ? a % b : undefined
          case '<<': return a * 2 ** b
        }
        return undefined
      }
      case 'DeclRefExpr': {
        const d = n.referencedDecl!
        if (d.kind === 'EnumConstantDecl') return enumConst.get(d.id)
        const g = globals.get(d.id)
        return g && /^const /.test(g.type!.qualType) && g.inner?.length ? fold(g.inner[0]!) : undefined
      }
    }
    return undefined
  }

  // --- types: the table Go's lowering reads (TT), from clang's spelled types ---------------------------------------------
  const ttab: TT[] = [], tkey = new Map<string, number>()
  const T = (t: number) => ttab[t]!
  const add = (key: string, t: TT): number => { const k = tkey.get(key); if (k !== undefined) return k; ttab.push(t); tkey.set(key, ttab.length - 1); return ttab.length - 1 }
  const ints: Record<string, [number, boolean]> = {
    char: [8, !target.charUnsigned], 'signed char': [8, true], 'unsigned char': [8, false], short: [target.short, true], 'short int': [target.short, true], 'unsigned short': [target.short, false], 'unsigned short int': [target.short, false],
    int: [target.int, true], signed: [target.int, true], 'signed int': [target.int, true], unsigned: [target.int, false], 'unsigned int': [target.int, false],
    long: [target.long, true], 'long int': [target.long, true], 'unsigned long': [target.long, false], 'unsigned long int': [target.long, false],
    'long long': [target.llong, true], 'long long int': [target.llong, true], 'unsigned long long': [target.llong, false], 'unsigned long long int': [target.llong, false],
    wchar_t: [32, true], char8_t: [8, false], char16_t: [16, false], char32_t: [32, false],
  }
  const intT = (go: string, bits: number, signed: boolean) => add(`int:${go}`, {k: 'int', go, bits, signed, ...(signed ? {ub: true} : {})})
  const boolT = add('bool', {k: 'bool', go: 'bool'})
  const recT = (id: string, spelled?: string): number => {
    const r = records.get(id)
    if (!r) return add(`opaque:${spelled}`, {k: 'opaque', go: spelled})
    const go = recName.get(id) ?? (r.name ? (cpp ? r.name : `${r.tagUsed} ${r.name}`) : spelled), key = `rec:${id}`
    if (tkey.has(key)) return tkey.get(key)!
    if (r.tagUsed === 'union') return add(key, {k: 'union', go})
    const t = add(key, {k: 'struct', own: true, name: go, go, fields: []})
    ttab[t]!.fields = (r.inner ?? []).filter(f => f.kind === 'FieldDecl').map(f => ({name: f.name ?? '', t: tyOf(f.type!), embedded: false}))
    return t
  }
  function tyOf(ty: {qualType: string, desugaredQualType?: string}): number { return parseT(ty.qualType, ty.desugaredQualType) }
  function parseT(s0: string, desug?: string): number {
    const s = s0.replace(/\b(const|volatile|restrict|__restrict)\b/g, '').replace(/\s+/g, ' ').replace(/ \*/g, '*').replace(/\*/g, ' *').replace(/\* \*/g, '**').trim()
    if (s === '_Bool' || s === 'bool') return boolT
    const arr = /^(.*?)\s*\[(\d+)\]$/.exec(s)
    if (arr) return add(`arr:${s}`, {k: 'array', go: s, elem: parseT(arr[1]!), len: Number(arr[2]), fixed: true})
    if (/\(\*\)|\(.*\)$/.test(s)) return add(`fn:${s}`, {k: 'func', go: s})
    if (/\*$/.test(s)) { const e = parseT(s.replace(/\s*\*$/, '')); return add(`ptr:${e}`, {k: 'ptr', go: s, elem: e}) }
    if (/&$/.test(s)) return add(`ref:${s}`, {k: 'ref', go: s})
    if (ints[s]) return intT(s, ...ints[s]!)
    if (s === 'float' || s === 'double' || s === 'long double') return add(`f:${s}`, {k: 'float', go: s})
    if (s === 'void') return add('void', {k: 'void', go: 'void'})
    const un = /^(struct|union|class) \((?:unnamed|anonymous) (?:struct|union|class) at .*:(\d+):(\d+)\)$/.exec(s)
    if (un) { const id = anon.get(`${un[2]}:${un[3]}`); return id ? recT(id) : add(`opaque:${s}`, {k: 'opaque', go: s}) }
    if (/^enum /.test(s)) return enumT(s)
    if (tags.has(s)) return recT(tags.get(s)!, s)
    const td = typedefs.get(s.replace(/^(struct|union|class) /, ''))
    if (td) {
      if (td.rec && records.has(td.rec)) return recT(td.rec, s)
      const inner = parseT(td.desug ?? td.qual), it = T(inner)
      // (an integer type keeps its name: the notes and the harness spell it so)
      return it.k === 'int' ? intT(s, it.bits!, it.signed!) : inner
    }
    if (desug && desug !== s0) return parseT(desug)
    return add(`opaque:${s}`, {k: 'opaque', go: s})
  }
  const enumT = (s: string): number => {
    const d = top.find(n => n.kind === 'EnumDecl' && `enum ${n.name}` === s), vals = (d?.inner ?? []).filter(c => c.kind === 'EnumConstantDecl').map(c => enumConst.get(c.id!) ?? 0)
    const signed = vals.some(v => v < 0)
    return intT(s, target.int, signed)
  }
  for (const n of top) if (!n.isImplicit) visitDecl(n)
  // (a typedef of a struct declared before its definition names the definition)
  for (const [name, td] of typedefs) { const id = tags.get(td.qual.replace(/^const /, '')); if (id && !recName.has(id)) recName.set(id, name); if (id && !(td.rec && records.has(td.rec))) td.rec = id }

  // --- expressions ---------------------------------------------------------------------------------------------------------
  const funcs = new Map<string, CN>()
  for (const n of top) if ((n.kind === 'FunctionDecl') && own(n) && n.inner?.some(c => c.kind === 'CompoundStmt')) funcs.set(n.name!, n)
  const entryRec = tags.get(`struct ${entry}`) ?? tags.get(entry) ?? typedefs.get(entry)?.rec
  const entryT = entryRec ? recT(entryRec, entry) : refuse(undefined, `no struct ${entry} in ${base}`)
  const params = (f: CN) => (f.inner ?? []).filter(c => c.kind === 'ParmVarDecl')
  // An out-parameter (a pointer to an integer or a bool, not the receiver): a pointer to a box of one field, `value`,
  // *p its field.
  const boxed = new Map<string, number>()
  const boxOf = (q: CN): number => {
    const t = tyOf(q.type!), pt = T(t)
    if (pt.k !== 'ptr' || !['int', 'bool'].includes(T(pt.elem!).k)) return t
    const e = pt.elem!, b = add(`box:${e}`, {k: 'struct', own: true, box: true, name: T(e).go, go: T(e).go, fields: [{name: 'value', t: e, embedded: false}]}), bp = add(`ptr:${b}`, {k: 'ptr', go: pt.go, elem: b})
    boxed.set(q.id!, bp)
    return bp
  }
  const recvOf = (f: CN) => { const p = params(f)[0], t = p ? T(tyOf(p.type!)) : undefined; return t?.k === 'ptr' && t.elem === entryT ? p : undefined }
  for (const f of funcs.values()) for (const q of params(f).slice(recvOf(f) ? 1 : 0)) boxOf(q)
  const strip = (n: CN): CN => (n.kind === 'ParenExpr' || (n.kind === 'UnaryOperator' && n.opcode === '__extension__') || ((n.kind === 'ImplicitCastExpr' || n.kind === 'CStyleCastExpr') && ['LValueToRValue', 'NoOp'].includes(n.castKind!)) ? strip(n.inner![0]!) : n)
  const at = (n: CN, t: number) => ({p: pos(n), t, text: text(n)})
  const no = (n: CN, why: string): GX => ({e: 'no', ...at(n, -1), why})
  const lit = (n: CN, v: number, t: number): GX => ({e: 'lit', ...at(n, t), c: {int: String(v)}})
  const isBoolish = (n0: CN): boolean => {
    const n = strip(n0)
    if (n.kind === 'BinaryOperator' && (CMP.has(n.opcode!) || n.opcode === '&&' || n.opcode === '||')) return true
    if (n.kind === 'UnaryOperator' && n.opcode === '!') return true
    if ((n.kind === 'ImplicitCastExpr' || n.kind === 'CStyleCastExpr') && n.castKind === 'IntegralCast') return isBoolish(n.inner![0]!)
    if (n.kind === 'CallExpr' && calleeName(n) === '__builtin_expect') return isBoolish(n.inner![1]!)
    return n.type ? T(tyOf(n.type)).k === 'bool' : false
  }
  // (a sum or product of promoted unsigned values and constants ≥ 0: at least 0, by its form)
  const nonneg = (n0: CN): boolean => {
    const n = strip(n0), k = fold(n)
    if (k !== undefined) return k >= 0
    if (n.kind === 'ImplicitCastExpr' && n.castKind === 'IntegralCast') return T(tyOf(n.inner![0]!.type!)).signed === false
    if (n.kind === 'BinaryOperator' && (n.opcode === '+' || n.opcode === '*')) return nonneg(n.inner![0]!) && nonneg(n.inner![1]!)
    return !!n.type && T(tyOf(n.type)).signed === false
  }
  const calleeName = (n: CN): string | undefined => { const c = strip(n.inner![0]!); const d = (c.kind === 'ImplicitCastExpr' ? strip(c.inner![0]!) : c).referencedDecl; return d?.kind === 'FunctionDecl' ? d.name : undefined }
  // A condition: a boolean as it is; a number compared with 0; a pointer with NULL.
  const cond = (n0: CN): GX => {
    const n = strip(n0)
    if (n.kind === 'CallExpr' && calleeName(n) === '__builtin_expect') return cond(n.inner![1]!)
    if ((n.kind === 'ImplicitCastExpr' || n.kind === 'CStyleCastExpr') && ['IntegralCast', 'IntegralToBoolean', 'PointerToBoolean'].includes(n.castKind!) && isBoolish(n.inner![0]!)) return cond(n.inner![0]!)
    if (n.kind === 'BinaryOperator' && CMP.has(n.opcode!)) return {e: 'bin', ...at(n, boolT), op: n.opcode, x: x(n.inner![0]!), y: x(n.inner![1]!)}
    if (n.kind === 'BinaryOperator' && (n.opcode === '&&' || n.opcode === '||')) return {e: 'bin', ...at(n, boolT), op: n.opcode, x: cond(n.inner![0]!), y: cond(n.inner![1]!)}
    if (n.kind === 'UnaryOperator' && n.opcode === '!') return {e: 'un', ...at(n, boolT), op: '!', x: cond(n.inner![0]!)}
    const v = (n.kind === 'ImplicitCastExpr' && (n.castKind === 'IntegralToBoolean' || n.castKind === 'PointerToBoolean')) ? n.inner![0]! : n, vt = v.type ? tyOf(v.type) : -1
    if (vt >= 0 && T(vt).k === 'bool') return x(v)
    const k = fold(v)
    if (k !== undefined) return {e: 'lit', ...at(n, boolT), c: {bool: k !== 0}}
    if (vt >= 0 && T(vt).k === 'ptr') return {e: 'bin', ...at(n, boolT), op: '!=', x: x(v), y: {e: 'id', ...at(n, vt), o: 'nil'}}
    if (vt >= 0 && T(vt).k === 'int') return {e: 'bin', ...at(n, boolT), op: '!=', x: x(v), y: lit(n, 0, vt)}
    return no(n, `${text(n)}: a condition of type ${n.type?.qualType}`)
  }
  const x = (n0: CN): GX => {
    const n = strip(n0), t = n.type ? tyOf(n.type) : -1, a = at(n, t), kids = n.inner ?? []
    const k = t >= 0 && T(t).k === 'int' ? fold(n) : undefined
    if (k !== undefined) return Number.isSafeInteger(k) ? lit(n, k, t) : no(n, `${text(n)}: the constant ${k} is past 2^53 (the rule's numbers stop there)`)
    switch (n.kind) {
      case 'CXXBoolLiteralExpr': return {e: 'lit', ...a, c: {bool: !!n.value}}
      case 'DeclRefExpr': {
        const d = n.referencedDecl!
        if (d.kind === 'ParmVarDecl') return {e: 'id', ...a, ...(boxed.has(d.id) ? {t: boxed.get(d.id)!} : {}), o: 'var', id: d.id, n: d.name}
        if (d.kind === 'VarDecl') return globals.has(d.id) ? no(n, `${d.name}: a ${globals.get(d.id)!.storageClass === 'static' ? 'static' : 'global'} variable (state every object shares)`) : {e: 'id', ...a, o: 'var', id: d.id, n: d.name}
        if (d.kind === 'FunctionDecl') return no(n, `${d.name}: a function used as a value`)
        return no(n, `${text(n)}: a ${d.kind}`)
      }
      case 'MemberExpr': {
        const f = fields.get(n.referencedMemberDecl!)
        if (!f) return no(n, `${text(n)}: a member that isn't a field of a struct read here`)
        if (records.get(f.rec)!.tagUsed === 'union') return no(n, `${text(n)}: a union's member (one storage read as several types)`)
        const b = kids[0]!
        return {e: 'sel', ...a, k: 'field', x: n.isArrow ? x(b) : place(b), path: [f.i]}
      }
      case 'ImplicitCastExpr': case 'CStyleCastExpr': {
        const ck = n.castKind!, inner = kids[0]!
        if (ck === 'IntegralCast') { const it = tyOf(inner.type!); if (T(it).k === 'bool') return {e: 'ite', ...a, x: cond(inner), y: lit(n, 1, t), b: lit(n, 0, t)}; return it === t ? x(inner) : {e: 'call', ...a, conv: true, a: [x(inner)]} }
        if (ck === 'IntegralToBoolean' || ck === 'PointerToBoolean') return cond(n)
        if (ck === 'NullToPointer') return {e: 'id', ...a, o: 'nil'}
        if (ck === 'ToVoid') return x(inner)
        if (ck === 'FunctionToPointerDecay' || ck === 'BuiltinFnToFnPtr') return x(inner)
        if (ck === 'BitCast' && T(t).k === 'ptr' && strip(inner).type && tyOf(strip(inner).type!) === t) return x(inner)
        return no(n, `${text(n)}: a ${ck} conversion${ck === 'IntegralToFloating' || ck.includes('Floating') ? ' (floats are outside the subset)' : ck.includes('Pointer') ? ' (a pointer made from other than the state\'s objects)' : ''}`)
      }
      case 'BinaryOperator': {
        const op = n.opcode!, [l, r] = kids as [CN, CN]
        if (CMP.has(op) || op === '&&' || op === '||') { const c = cond(n); return T(t).k === 'bool' ? c : {e: 'ite', ...a, x: c, y: lit(n, 1, t), b: lit(n, 0, t)} }
        if (op === '&') {
          // u & (2^k − 1): u's low k bits, u % 2^k for an unsigned u.
          const m = fold(r)
          // (of a signed x, two's complement: the floor remainder, ((x % 2^k) + 2^k) % 2^k by C's truncating %)
          if (m !== undefined && m > 0 && Number.isInteger(Math.log2(m + 1))) {
            const k = lit(r, m + 1, t), lo: GX = {e: 'bin', ...a, op: '%', x: x(l), y: k}
            return T(t).signed === false || nonneg(l) ? lo : {e: 'bin', ...a, op: '%', x: {e: 'bin', ...a, op: '+', x: lo, y: k}, y: k}
          }
        }
        if (ARITH.has(op)) return {e: 'bin', ...a, op: op === '^' ? '^' : op, x: x(l), y: x(r)}
        if (op === ',') return no(n, 'the comma operator')
        return no(n, `${text(n)}: an assignment inside an expression (the subset reads it as a statement)`)
      }
      case 'UnaryOperator': {
        const op = n.opcode!
        if (op === '!') return T(t).k === 'bool' ? cond(n) : {e: 'ite', ...a, x: cond(n), y: lit(n, 1, t), b: lit(n, 0, t)}
        if (op === '-' || op === '+') return {e: 'un', ...a, op, x: x(kids[0]!)}
        if (op === '~') return {e: 'un', ...a, op: '^', x: x(kids[0]!)}
        if (op === '&') return {e: 'un', ...a, op: '&', x: place(kids[0]!)}
        if (op === '*') { const r = strip(kids[0]!); return r.kind === 'DeclRefExpr' && boxed.has(r.referencedDecl!.id) ? {e: 'sel', ...a, k: 'field', x: x(r), path: [0]} : {e: 'star', ...a, x: x(kids[0]!)} }
        return no(n, `${text(n)}: ${op} inside an expression (the subset reads it as a statement)`)
      }
      case 'ConditionalOperator': return {e: 'ite', ...a, x: cond(kids[0]!), y: x(kids[1]!), b: x(kids[2]!)}
      case 'CallExpr': return call(n)
      case 'ArraySubscriptExpr': {
        // An index into an array of the state (its decay to a pointer undone); pointer arithmetic is outside.
        const b = strip(kids[0]!), arr = b.kind === 'ImplicitCastExpr' && b.castKind === 'ArrayToPointerDecay' ? b.inner![0]! : undefined
        return arr ? {e: 'index', ...a, x: place(arr), i: x(kids[1]!)} : no(n, `${text(n)}: an index into a pointer (pointer arithmetic)`)
      }
      case 'StringLiteral': return no(n, `${text(n)}: a string (char arrays are outside the subset)`)
      case 'FloatingLiteral': return no(n, `${text(n)}: a float (the subset reads integers)`)
      case 'UnaryExprOrTypeTraitExpr': return no(n, `${text(n)}: sizeof (the target's layout)`)
    }
    return no(n, `${text(n)}: an expression the subset doesn't read (${n.kind})`)
  }
  // A place: a local, a field (through a pointer: ->), *p.
  const place = (n0: CN): GX => {
    const n = strip(n0)
    if (n.kind === 'DeclRefExpr' || n.kind === 'MemberExpr' || (n.kind === 'UnaryOperator' && n.opcode === '*')) return x(n)
    if (n.kind === 'ArraySubscriptExpr') return x(n)
    return no(n, `${text(n)}: a place the subset doesn't write`)
  }
  const call = (n: CN): GX => {
    const t = n.type ? tyOf(n.type) : -1, a = at(n, t), name = calleeName(n), args = (n.inner ?? []).slice(1)
    if (!name) return no(n, `${text(n)}: a call through a function pointer`)
    if (FAIL[name]) return {e: 'call', ...a, builtin: 'panic', a: [], what: FAIL[name]}
    if (name === '__builtin_expect') return x(args[0]!)
    if (name === 'exit' || name === '_Exit') return no(n, `${name}: the process ends`)
    const f = funcs.get(name)
    if (!f) return no(n, `${name}: a function of another file or library (other code)`)
    if (recvOf(f) && args.length) return {e: 'call', ...a, f: {e: 'sel', ...at(n, -1), k: 'method', x: x(args[0]!), n: name, mtype: entry, mptr: true}, a: args.slice(1).map(x)}
    return {e: 'call', ...a, f: {e: 'id', ...at(n, -1), o: 'func', n: name}, a: args.map(x)}
  }

  // --- statements -------------------------------------------------------------------------------------------------------
  const sno = (n: CN, why: string): GS[] => [{s: 'no', p: pos(n), why}]
  const conv = (n: CN, to: number, v: GX): GX => ({e: 'call', ...at(n, to), conv: true, a: [v]})
  const ss = (ns: CN[]): GS[] => ns.flatMap(st)
  const block = (n: CN): GS[] => (n.kind === 'CompoundStmt' ? ss(n.inner ?? []) : st(n))
  const ends = (b: GS[]) => { const l = b.at(-1); return !!l && (l.s === 'return' || l.s === 'panic' || (l.s === 'branch' && l.tok === 'break')) }
  function st(n: CN): GS[] {
    const p = pos(n), kids = n.inner ?? []
    switch (n.kind) {
      case 'CompoundStmt': return [{s: 'block', p, b: ss(kids)}]
      case 'NullStmt': return []
      case 'DeclStmt': return kids.flatMap((d): GS[] => {
        if (d.kind !== 'VarDecl') return d.kind === 'RecordDecl' || d.kind === 'TypedefDecl' || d.kind === 'EnumDecl' ? [] : sno(d, `a ${d.kind} in a function`)
        if (d.storageClass === 'static') return sno(d, `${d.name}: a static local (state every call shares)`)
        const init = d.init ? (d.inner ?? []).find(c => !c.kind.endsWith('Attr')) : undefined
        if (!init) return []
        if (init.kind === 'InitListExpr') return sno(d, `${d.name}: an initializer list`)
        return [{s: 'decl', p, specs: [{names: [{name: d.name!, id: d.id!, t: tyOf(d.type!)}], v: [x(init)]}]}]
      })
      case 'ReturnStmt': return [{s: 'return', p, r: kids.length ? [x(kids[0]!)] : []}]
      case 'IfStmt': {
        if (n.hasInitStorage || n.hasVarStorage) return sno(n, 'an if with a declaration')
        const [c, th, el] = kids as [CN, CN, CN | undefined]
        return [{s: 'if', p, c: cond(c), then: block(th), ...(el ? {else: {s: 'block', p: pos(el), b: block(el)}} : {})}]
      }
      case 'SwitchStmt': return switchC(n)
      case 'BreakStmt': return [{s: 'branch', p, tok: 'break'}]
      case 'ContinueStmt': return sno(n, 'continue (loops are outside the subset)')
      case 'WhileStmt': case 'DoStmt': case 'ForStmt': return sno(n, `a loop (${n.kind === 'WhileStmt' ? 'while' : n.kind === 'DoStmt' ? 'do' : 'for'})`)
      case 'GotoStmt': case 'IndirectGotoStmt': return sno(n, 'goto')
      case 'LabelStmt': return sno(n, 'a label (goto)')
      case 'CaseStmt': case 'DefaultStmt': return sno(n, 'a case label inside a block of the switch')
      case 'AttributedStmt': return ss(kids.filter(c => !c.kind.endsWith('Attr')))
      case 'ParenExpr': return st(kids[0]!)
      case 'StmtExpr': return block(kids[0]!)
      case 'CStyleCastExpr': case 'ImplicitCastExpr': if (n.castKind === 'ToVoid') { const i = strip(kids[0]!); return ['DeclRefExpr', 'UnaryExprOrTypeTraitExpr', 'IntegerLiteral'].includes(i.kind) ? [] : st(i) } break
      case 'ConditionalOperator': return [{s: 'if', p, c: cond(kids[0]!), then: st(kids[1]!), else: {s: 'block', p, b: st(kids[2]!)}}]
      case 'BinaryOperator': {
        if (n.opcode === ',') return ss(kids)
        if (n.opcode !== '=') break
        const [l, r] = kids as [CN, CN], rs = strip(r)
        // a = b = c: b set first, then a to b's value.
        if (rs.kind === 'BinaryOperator' && rs.opcode === '=') return [...st(rs), {s: 'assign', p, op: '=', l: [place(l)], r: [conv2(r, tyOf(l.type!), x(rs.inner![0]!))]}]
        return [{s: 'assign', p, op: '=', l: [place(l)], r: [x(r)]}]
      }
      case 'CompoundAssignOperator': {
        const [l, r] = kids as [CN, CN], lt = tyOf(l.type!), ct = tyOf(n.computeLHSType!), op = n.opcode!.slice(0, -1)
        const m = op === '&' ? fold(r) : undefined, mask = m !== undefined && m > 0 && Number.isInteger(Math.log2(m + 1)) && T(ct).signed === false
        const y = mask ? lit(r, m + 1, ct) : x(r), bop = mask ? '%' : op
        if (ct === lt) return [{s: 'assign', p, op: `${bop}=`, l: [place(l)], r: [y]}]
        // computed at the wider type, then converted back: x = (T)((C)x op y)
        return [{s: 'assign', p, op: '=', l: [place(l)], r: [conv(n, lt, {e: 'bin', ...at(n, ct), op: bop, x: conv(l, ct, x(l)), y})]}]
      }
      case 'UnaryOperator': {
        if (n.opcode === '__extension__') return st(kids[0]!)
        if (!['++', '--'].includes(n.opcode!)) break
        const l = kids[0]!, lt = tyOf(l.type!), tt = T(lt)
        if (tt.k !== 'int') return sno(n, `${text(n)}: ${n.opcode} of a ${l.type!.qualType}`)
        if (tt.bits! >= target.int) return [{s: 'incdec', p, op: n.opcode, x: place(l)}]
        // (a narrow integer is promoted to int, the result converted back)
        const it = intT('int', target.int, true)
        return [{s: 'assign', p, op: '=', l: [place(l)], r: [conv(n, lt, {e: 'bin', ...at(n, it), op: n.opcode![0], x: conv(l, it, x(l)), y: lit(n, 1, it)})]}]
      }
      case 'CallExpr': return [{s: 'expr', p, x: call(n)}]
    }
    if (n.kind.endsWith('Expr') || n.kind.endsWith('Literal') || n.kind.endsWith('Operator')) return [{s: 'expr', p, x: x(n)}]
    return sno(n, `a statement the subset doesn't read (${n.kind})`)
  }
  const conv2 = (n: CN, to: number, v: GX): GX => (T(to).k === 'int' && v.t !== to ? conv(n, to, v) : v)
  // A switch: its body's labels, each a case of Go's shape; one that doesn't end in a break or a return runs into the next.
  function switchC(n: CN): GS[] {
    const kids = n.inner ?? [], tag = kids.at(-2)!, body = kids.at(-1)!, tt = tyOf(strip(tag).type!)
    if (kids.length > 2) return sno(n, 'a switch with a declaration')
    const cases: {list?: GX[], default?: boolean, b: GS[], p: string}[] = []
    const label = (c: CN): CN | undefined => {
      if (c.kind === 'CaseStmt') {
        if (c.inner!.length > 2) return void cases.push({p: pos(c), b: sno(c, 'a case range (a GNU extension)')}) as undefined
        const v = fold(c.inner![0]!)
        cases.push({p: pos(c), list: [v === undefined ? no(c, 'a case that isn\'t a constant') : lit(c, v, tt)], b: []})
        return c.inner![1]
      }
      if (c.kind === 'DefaultStmt') { cases.push({p: pos(c), default: true, b: []}); return c.inner![0] }
      return c
    }
    for (const c0 of body.kind === 'CompoundStmt' ? body.inner ?? [] : [body]) {
      let c: CN | undefined = c0
      while (c && (c.kind === 'CaseStmt' || c.kind === 'DefaultStmt')) { const s: CN | undefined = label(c); c = s === c ? undefined : s }
      if (c && cases.length) cases.at(-1)!.b.push(...st(c))
    }
    // (labels with nothing between them are one case: case 1: case 2: ...; one with the default is the default)
    for (let i = cases.length - 2; i >= 0; i--) {
      const a = cases[i]!, b = cases[i + 1]!
      if (a.b.length) continue
      if (a.default || b.default) cases.splice(i, 2, {...b, default: true, list: undefined, p: a.p})
      else cases.splice(i, 2, {...b, list: [...a.list!, ...b.list!], p: a.p})
    }
    for (const c of cases) if (c.default) delete c.list
    cases.forEach((c, i) => { if (i < cases.length - 1 && !ends(c.b)) c.b.push({s: 'branch', p: c.p, tok: 'fallthrough'}) })
    return [{s: 'switch', p: pos(n), tag: x(tag), cases}]
  }

  // --- the functions ----------------------------------------------------------------------------------------------------
  const out: GoFunc[] = []
  for (const [name, f] of funcs) {
    const ps = params(f), r = recvOf(f), body = f.inner!.find(c => c.kind === 'CompoundStmt')!, rt = parseT(f.type!.qualType.slice(0, retEnd(f.type!.qualType)))
    out.push({name, p: pos(f), span: [f.$b?.line ?? 0, f.$e?.line ?? 0],
      ...(r ? {recv: {t: tyOf(r.type!), ptr: true, type: entry, ...(r.name ? {name: r.name, id: r.id} : {})}} : {}),
      params: ps.slice(r ? 1 : 0).map(q => ({...(q.name ? {name: q.name, id: q.id} : {}), t: boxed.get(q.id!) ?? tyOf(q.type!), ts: q.type!.qualType})),
      results: T(rt).k === 'void' ? [] : [{t: rt}], body: ss(body.inner ?? []),
      ...(/\.\.\.\)$/.test(f.type!.qualType) ? {params: [{t: -1, variadic: true}]} : {}),
      static: f.storageClass === 'static'} as GoFunc)
  }
  const td = records.get(entryRec!)!
  const pkg: GoPkg = {lang: cpp ? 'cpp' : 'c', package: entry, files: [{name: base, imports: []}], funcs: out, types: [{name: entry, t: entryT, p: pos(td), span: [td.$b?.line ?? 0, td.$e?.line ?? 0]}], consts: [], vars: [], errors: [], ttab}
  const methods = out.filter((f, i) => f.recv && !(f as {static?: boolean}).static && mine([...funcs.values()][i]!)).map(f => f.name)
  return {pkg, methods, entry, cname: T(entryT).go!}
}
// Where a function type's result ends: before its parameter list (the last parenthesized group).
function retEnd(s: string): number {
  let d = 0
  for (let i = s.length - 1; i >= 0; i--) { if (s[i] === ')') d++; else if (s[i] === '(' && --d === 0) return i }
  return s.length
}
