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
import type {SafetySite} from '../extract-step.ts'
import {Refusal, readerRun, statedRefusal} from '../extract-read.ts'

type CN = {id?: string, kind: string, name?: string, inner?: CN[], type?: {qualType: string, desugaredQualType?: string, typeAliasDeclId?: string}, value?: string, opcode?: string, castKind?: string, isArrow?: boolean, isPostfix?: boolean,
  referencedDecl?: {id: string, kind: string, name: string, type?: {qualType: string}}, referencedMemberDecl?: string, previousDecl?: string, storageClass?: string, isImplicit?: boolean, completeDefinition?: boolean, tagUsed?: string, hasElse?: boolean,
  computeLHSType?: {qualType: string, desugaredQualType?: string}, computeResultType?: {qualType: string, desugaredQualType?: string}, init?: string, decl?: {id: string, kind: string}, loc?: L, range?: {begin: L, end: L}, $at?: At, $b?: At, $e?: At, $files?: Set<string>, $macroExpansions?: {spell: string, spellLine: number, expand: string, expandLine: number}[], [k: string]: unknown}
type L = {offset?: number, file?: string, line?: number, col?: number, tokLen?: number, spellingLoc?: L, expansionLoc?: L, includedFrom?: unknown}
type At = {file: string, line: number, col: number, off: number, tok: number}
export type CSafetyMacroConfig = {
  target: string,
  compiler?: string,
  std: string,
  stdcVersion: string,
  envScrubbed: boolean,
  includeDirs: readonly string[],
  flags: readonly string[],
  defines: readonly string[],
  ndebugDefined: boolean,
  optimizeDefined: boolean,
  debugDefined: boolean,
}
export type CSafetyClangMeta = {systemFiles: Set<string>, userFiles: Set<string>, macroConfig: CSafetyMacroConfig}
export type CTarget = {int: number, long: number, short: number, llong: number, charUnsigned: boolean, charBits?: number, safetyMeta?: CSafetyClangMeta}
// (consts: the project's enum constants by name, one of a name only, for the laws' terms)
// (globals: the file's own globals read as the state, the file's stem the entry: each global's name, those the
// request gives (read but never written here, another file's or the hardware's) apart)
export type CRead = {pkg: GoPkg, methods: string[], helpers?: string[], macroConfig?: CSafetyMacroConfig, entry: string, cname: string, consts: Record<string, number>, globals?: {state: string[], inputs: string[], types: Record<string, string>, externs: string[]}}
export class SafetyUncoveredRefusal extends Refusal {
  readonly coveredFunctions: readonly string[]
  readonly uncheckedFunctions: readonly string[]
  readonly macroConfig?: CSafetyMacroConfig
  constructor(where: string, what: string, coveredFunctions: readonly string[], uncheckedFunctions: readonly string[], macroConfig?: CSafetyMacroConfig) {
    super(where, what)
    this.coveredFunctions = coveredFunctions
    this.uncheckedFunctions = uncheckedFunctions
    this.macroConfig = macroConfig
  }
}
type CP = {
  execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string,
  spawnSync: (f: string, a: string[], o: Record<string, unknown>) => {status: number | null, stdout?: string, stderr?: string, error?: Error},
}
// (consecutive JSON values in one string, each with where it ends)
class JSONDecoder {
  decode(s: string, i: number): [unknown, number] {
    let d = 0, q = false, j = i
    for (; j < s.length; j++) { const c = s[j]; if (q) { if (c === '\\') j++; else if (c === '"') q = false } else if (c === '"') q = true; else if (c === '{' || c === '[') d++; else if ((c === '}' || c === ']') && --d === 0) break }
    return [JSON.parse(s.slice(i, j + 1)), j + 1]
  }
}
const proc = (globalThis as {process?: {getBuiltinModule?: (id: string) => unknown, env?: Record<string, string | undefined>}}).process
export const node = <T>(id: string): T => { const m = proc?.getBuiltinModule?.(id); if (!m) throw new Error(`the C front end runs clang through ${id} (Node 20.16 or later, or Bun)`); return m as T }

// Environment variables that can inject compiler include paths, options, or driver overrides into
// clang (CPATH, C_INCLUDE_PATH, CCC_OVERRIDE_OPTIONS, etc.). Unset on every clang invocation so
// system search directories and compilation cannot be tampered with through the environment.
export const SCRUBBED_CLANG_ENV_KEYS = new Set([
  'CPATH',
  'C_INCLUDE_PATH',
  'CPLUS_INCLUDE_PATH',
  'OBJC_INCLUDE_PATH',
  'OBJCPLUS_INCLUDE_PATH',
  'INCLUDE',
  'CCC_OVERRIDE_OPTIONS',
  'CCC_ADD_ARGS',
  'CCC_FALLBACK',
  'CLANG_CONFIG_FILE',
  'CLANG_CONFIG_FILE_USER_DIR',
  'CLANG_CONFIG_FILE_SYSTEM_DIR',
  'COMPILER_PATH',
  'LIBRARY_PATH',
  'GCC_EXEC_PREFIX',
  'CFLAGS',
  'CPPFLAGS',
  'CXXFLAGS',
  'LDFLAGS',
  'DEPENDENCIES_OUTPUT',
  'SUNPRO_DEPENDENCIES',
  'SDKROOT',
])

export function scrubbedClangEnv(extra?: Record<string, string>): Record<string, string> {
  const out: Record<string, string> = {}
  for (const [k, v] of Object.entries(proc?.env ?? {})) {
    if (v === undefined) continue
    if (SCRUBBED_CLANG_ENV_KEYS.has(k) || /^(?:CCC_|CLANG_CONFIG_)/i.test(k)) continue
    out[k] = v
  }
  if (extra) Object.assign(out, extra)
  return out
}

// --- running clang ------------------------------------------------------------------------------------------------------
// (C++: only the declarations named after the class, `-ast-dump-filter`: its standard headers' are hundreds of MB;
// clang writes them one after another, its locations' state going on from one to the next)
export function clangDump(file: string, flags: string[], clang = 'clang', cpp = false, filter?: string, safety = false): {tu: CN, target: CTarget} {
  const cp = node<CP>('node:child_process')
  const fs = node<{realpathSync: (p: string) => string}>('node:fs')
  const path = node<{resolve: (...p: string[]) => string, relative: (from: string, to: string) => string, isAbsolute: (p: string) => boolean}>('node:path')
  const lang = cpp ? ['-x', 'c++'] : ['-x', 'c']
  const realPath = (p: string): string => { try { return fs.realpathSync(p) } catch { return path.resolve(p) } }
  const clangEnv = scrubbedClangEnv()
  const run = (args: string[]) => {
    try { return cp.execFileSync(clang, args, {encoding: 'utf8', maxBuffer: 1 << 30, stdio: ['ignore', 'pipe', 'pipe'], env: clangEnv, ...readerRun()}) }
    catch (e) {
      const x = e as {code?: string, stderr?: string, message: string}
      const stated = statedRefusal(e)
      if (stated) throw new Refusal(file, stated)
      throw new Refusal(file, x.code === 'ENOENT' ? `no ${clang} to run: clang is needed to extract ${cpp ? 'C++' : 'C'}` : `clang doesn't compile it (${String(x.stderr ?? x.message).split('\n').filter(l => /error/.test(l)).slice(0, 3).join(' | ')})`)
    }
  }
  const runFull = (args: string[]): {stdout: string, stderr: string} => {
    const r = cp.spawnSync(clang, args, {encoding: 'utf8', maxBuffer: 1 << 30, stdio: ['ignore', 'pipe', 'pipe'], env: clangEnv, ...readerRun()})
    if (r.error) {
      const x = r.error as {code?: string, message: string}
      const stated = statedRefusal(r.error)
      if (stated) throw new Refusal(file, stated)
      throw new Refusal(file, x.code === 'ENOENT' ? `no ${clang} to run: clang is needed to extract ${cpp ? 'C++' : 'C'}` : x.message)
    }
    if (r.status !== 0)
      throw new Refusal(file, `clang doesn't compile it (${String(r.stderr ?? '').split('\n').filter(l => /error/.test(l)).slice(0, 3).join(' | ')})`)
    return {stdout: r.stdout ?? '', stderr: r.stderr ?? ''}
  }
  const dump = run([...lang, ...flags, '-Xclang', '-ast-dump=json', ...(filter ? ['-Xclang', `-ast-dump-filter=${filter}`] : []), '-fsyntax-only', file]), inner: CN[] = [], dec = new JSONDecoder()
  const tu = filter ? {kind: 'TranslationUnitDecl', inner} as CN : JSON.parse(dump) as CN
  if (filter) for (let i = dump.indexOf('{'); i >= 0; i = dump.indexOf('{', i)) { const [o, e] = dec.decode(dump, i); inner.push(o as CN); i = e }
  const defs = run([...lang, ...flags, '-dM', '-E', '/dev/null']), def = (k: string) => Number(new RegExp(`#define ${k} (\\d+)`).exec(defs)?.[1] ?? 0)
  let safetyMeta: CSafetyClangMeta | undefined
  if (safety && !cpp) {
    // Decide system-ness by PATH ONLY: read Clang's built-in and -isystem search directories
    // from `clang -E -v` (with user -I / -iquote flags stripped), never trusting linemarker
    // flag 3 (which `#pragma`/`_Pragma` GCC system_header sets and propagates to included files).
    const stripUserIncludes = (fsList: readonly string[]): string[] => {
      const out: string[] = []
      for (let i = 0; i < fsList.length; i++) {
        const f = fsList[i]!
        if (f === '-I' || f === '-iquote') { i++; continue }
        if (f.startsWith('-I') || f.startsWith('-iquote')) continue
        out.push(f)
      }
      return out
    }
    const probeV = runFull([...lang, ...stripUserIncludes(flags), '-E', '-v', '-o', '/dev/null', '/dev/null'])
    const targetTriple = /^Target:\s*(\S+)/m.exec(probeV.stderr)?.[1]?.trim() ?? 'unknown'
    const compilerMatch = /clang version\s+([^\s(]+)/.exec(probeV.stderr)
    const compiler = compilerMatch ? `clang ${compilerMatch[1]}` : undefined
    const systemDirs: string[] = []
    {
      let inAngle = false
      for (const rawLine of probeV.stderr.split('\n')) {
        const line = rawLine.replace(/\r$/, '')
        if (/^#include <\.\.\.> search starts here:\s*$/.test(line)) { inAngle = true; continue }
        if (inAngle) {
          if (/^End of search list\.\s*$/.test(line)) break
          const dir = line.trim().replace(/\s+\(framework directory\)$/, '')
          if (dir) systemDirs.push(realPath(dir))
        }
      }
    }
    const mainReal = realPath(file)
    const isUnderDir = (rp: string, dir: string): boolean => {
      const rel = path.relative(dir, rp)
      return rel !== '' && !rel.startsWith('..') && !path.isAbsolute(rel)
    }
    const isUnderSystemDir = (rawPath: string): boolean => {
      if (rawPath === '<built-in>') return true
      if (!rawPath || rawPath.startsWith('<')) return false
      const rp = realPath(rawPath)
      if (rp === mainReal) return false
      return systemDirs.some(dir => isUnderDir(rp, dir))
    }
    // Run `-E -H` once to collect actual physically included headers (immune to #line spoofing)
    // and audit all preprocessor linemarkers for system_header pragmas or filename changes.
    const ppRes = runFull([...lang, ...flags, '-E', '-H', file])
    const physicalFiles = new Set<string>([mainReal])
    for (const rawLine of ppRes.stderr.split('\n')) {
      const hm = /^\.+\s+(.+)$/.exec(rawLine.replace(/\r$/, ''))
      if (hm) physicalFiles.add(realPath(hm[1]!.trim()))
    }
    const isSystemPath = (rawPath: string): boolean => {
      if (rawPath === '<built-in>') return true
      if (!rawPath || rawPath.startsWith('<')) return false
      const rp = realPath(rawPath)
      if (rp === mainReal || !physicalFiles.has(rp)) return false
      return systemDirs.some(dir => isUnderDir(rp, dir))
    }
    const systemFiles = new Set<string>(['<built-in>'])
    const userFiles = new Set<string>([mainReal])
    for (const p of physicalFiles) {
      if (isSystemPath(p)) systemFiles.add(p)
      else userFiles.add(p)
    }
    // Audit Clang's linemarkers: refuse flag 3 on any non-system file (catches #pragma / _Pragma /
    // digraph / macro-expanded GCC system_header in all spellings) and refuse any filename change
    // from a user file without include enter/leave flags (catches #line / %:line / ??= linemarkers).
    const stack: string[] = [mainReal]
    for (const m of ppRes.stdout.matchAll(/^# \d+ "((?:[^"\\]|\\.)*)"(.*)$/gm)) {
      const rawPath = m[1]!.replace(/\\(["\\])/g, '$1')
      if (!rawPath) continue
      const nums = new Set(m[2]!.trim().split(/\s+/).filter(Boolean))
      if (!rawPath.startsWith('<')) {
        const rp = realPath(rawPath)
        const sys = isSystemPath(rawPath)
        if (nums.has('3') && !sys)
          throw new Refusal(rawPath, '#pragma GCC system_header or system-header linemarker in non-system file is outside the C safety subset')
        const prev = stack[stack.length - 1]
        if (nums.has('1')) {
          if (!physicalFiles.has(rp))
            throw new Refusal(prev ?? file, `linemarker references non-included file ${rawPath} (outside the C safety subset)`)
          stack.push(rp)
        } else if (nums.has('2')) {
          const idx = stack.lastIndexOf(rp)
          if (idx >= 0) stack.length = idx + 1
          else if (stack.length > 1) stack.pop()
        } else if (prev && !isSystemPath(prev) && rp !== prev) {
          throw new Refusal(prev, `#line or linemarker filename change to ${rawPath} is outside the C safety subset`)
        }
      } else {
        if (nums.has('1')) stack.push(rawPath)
        else if (nums.has('2')) {
          const idx = stack.lastIndexOf(rawPath)
          if (idx >= 0) stack.length = idx + 1
          else if (stack.length > 1) stack.pop()
        }
      }
    }
    const stdcVersion = /^#define __STDC_VERSION__\s+(\S+)/m.exec(defs)?.[1] ?? 'none'
    const strictAnsi = /^#define __STRICT_ANSI__(?:\s|$)/m.test(defs)
    const explicitStd = [...flags].reverse().find(f => f.startsWith('-std='))?.slice(5)
    const inferredStd = stdcVersion === '202311L' ? (strictAnsi ? 'c23' : 'gnu23')
      : stdcVersion === '201710L' ? (strictAnsi ? 'c17' : 'gnu17')
      : stdcVersion === '201112L' ? (strictAnsi ? 'c11' : 'gnu11')
      : stdcVersion === '199901L' ? (strictAnsi ? 'c99' : 'gnu99')
      : (strictAnsi ? 'c89' : 'gnu89')
    const ndebugMatch = /^#define NDEBUG(?:\s+(.*))?$/m.exec(defs)
    const ndebugDefined = !!ndebugMatch
    const ndebugVal = ndebugMatch?.[1]?.trim() ?? ''
    const optimizeDefined = /^#define __OPTIMIZE__(?:\s|$)/m.test(defs)
    const debugMatch = /^#define DEBUG(?:\s+(.*))?$/m.exec(defs)
    const debugDefined = !!debugMatch
    const debugVal = debugMatch?.[1]?.trim() ?? ''
    // Verify preprocessed user-code token stream is invariant across build-mode configurations
    // (NDEBUG defined vs undefined, -O0 vs -O2 for __OPTIMIZE__, and DEBUG defined vs undefined).
    // Comparing preprocessed tokens directly is immune to digraphs (%:), trigraphs, and macro pasting.
    const tokenizeUserCode = (pp: string): string => {
      const userChunks: string[] = []
      let inUser = true
      for (const line of pp.split('\n')) {
        const lm = /^# \d+ "((?:[^"\\]|\\.)*)"(.*)$/.exec(line)
        if (lm) {
          const rawPath = lm[1]!.replace(/\\(["\\])/g, '$1')
          inUser = !isUnderSystemDir(rawPath)
          continue
        }
        if (inUser) userChunks.push(line)
      }
      const text = userChunks.join('\n')
      const toks: string[] = []
      for (let i = 0; i < text.length; ) {
        const ch = text[i]!
        if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\n' || ch === '\f' || ch === '\v') { i++; continue }
        if (ch === '"' || ch === "'") {
          const q = ch
          let j = i + 1
          while (j < text.length) {
            if (text[j] === '\\') { j += 2; continue }
            if (text[j] === q) { j++; break }
            j++
          }
          toks.push(text.slice(i, j))
          i = j
          continue
        }
        if (/[A-Za-z0-9_$.]/.test(ch)) {
          let j = i + 1
          while (j < text.length) {
            const c = text[j]!
            if (c === "'" && /[0-9A-Za-z_]/.test(text[j + 1] ?? '') && /[0-9]/.test(text[i]!)) { j += 2; continue }
            if (/[A-Za-z0-9_$]/.test(c)) { j++; continue }
            break
          }
          toks.push(text.slice(i, j))
          i = j
          continue
        }
        toks.push(ch)
        i++
      }
      return toks.join(' ')
    }
    const baseTokens = tokenizeUserCode(ppRes.stdout)
    const alternates: {label: string, extra: string[]}[] = [
      ...(ndebugDefined ? [{label: 'NDEBUG', extra: ['-UNDEBUG']}] : []),
      ...(!ndebugDefined || ndebugVal !== '0' ? [{label: 'NDEBUG', extra: ['-DNDEBUG=0']}] : []),
      ...(!ndebugDefined || ndebugVal !== '1' ? [{label: 'NDEBUG', extra: ['-DNDEBUG=1']}] : []),
      ...(optimizeDefined ? [{label: '__OPTIMIZE__', extra: ['-O0']}] : []),
      {label: '__OPTIMIZE__', extra: ['-O2']},
      {label: '__OPTIMIZE_SIZE__', extra: ['-Os']},
      {label: '__SANITIZE_ADDRESS__/__SANITIZE_UNDEFINED__', extra: ['-fsanitize=address,undefined']},
      {label: '__SANITIZE_ADDRESS__/__SANITIZE_UNDEFINED__', extra: ['-D__SANITIZE_ADDRESS__=1', '-D__SANITIZE_UNDEFINED__=1']},
      ...(debugDefined ? [{label: 'DEBUG', extra: ['-UDEBUG']}] : []),
      ...(!debugDefined || debugVal !== '0' ? [{label: 'DEBUG', extra: ['-DDEBUG=0']}] : []),
      ...(!debugDefined || debugVal !== '1' ? [{label: 'DEBUG', extra: ['-DDEBUG=1']}] : []),
      ...(!debugDefined || debugVal !== '2' ? [{label: 'DEBUG', extra: ['-DDEBUG=2']}] : []),
    ]
    for (const alt of alternates) {
      const r = cp.spawnSync(clang, [...lang, ...flags, ...alt.extra, '-E', file], {encoding: 'utf8', maxBuffer: 1 << 30, stdio: ['ignore', 'pipe', 'pipe'], env: clangEnv, ...readerRun()})
      if (r.error || r.status !== 0)
        throw new Refusal(file, `preprocessed user code depends on ${alt.label} (preprocessing failed under ${alt.extra.join(' ')}; proof only holds for one build-mode configuration)`)
      if (tokenizeUserCode(r.stdout ?? '') !== baseTokens)
        throw new Refusal(file, `preprocessed user code depends on ${alt.label} (differs under ${alt.extra.join(' ')}; proof only holds for one build-mode configuration)`)
    }
    const includeDirs: string[] = []
    for (let i = 0; i < flags.length; i++) {
      const f = flags[i]!
      if (f === '-I' && i + 1 < flags.length) includeDirs.push(`-I${flags[++i]!}`)
      else if (f.startsWith('-I')) includeDirs.push(f)
    }
    const macroConfig: CSafetyMacroConfig = {
      target: targetTriple,
      ...(compiler ? {compiler} : {}),
      std: explicitStd ?? inferredStd,
      stdcVersion,
      envScrubbed: true,
      includeDirs,
      flags: [...flags],
      defines: flags.filter(f => f.startsWith('-D') || f.startsWith('-U')),
      ndebugDefined,
      optimizeDefined,
      debugDefined,
    }
    safetyMeta = {systemFiles, userFiles, macroConfig}
  }
  return {tu, target: {int: def('__SIZEOF_INT__') * 8, long: def('__SIZEOF_LONG__') * 8, short: def('__SIZEOF_SHORT__') * 8, llong: def('__SIZEOF_LONG_LONG__') * 8, charBits: def('__CHAR_BIT__'), charUnsigned: /#define __CHAR_UNSIGNED__/.test(defs), ...(safetyMeta ? {safetyMeta} : {})}}
}
// The values of names a law reads that the code defines as integer constants (a macro, an enum constant, a constexpr
// variable), folded by clang itself: each the value of an enumerator of a probe that includes the file. A name that
// isn't one (a field, a float, a string) doesn't compile there and is left out.
export function constantsOf(file: string, flags: string[], clang: string, cpp: boolean, names: string[]): Record<string, number> {
  const fs = node<{mkdtempSync: (p: string) => string, writeFileSync: (p: string, s: string) => void, rmSync: (p: string, o?: unknown) => void}>('node:fs'), os = node<{tmpdir: () => string}>('node:os'), path = node<{resolve: (p: string) => string}>('node:path'), cp = node<CP>('node:child_process')
  let left = [...new Set(names)].filter(n => /^[A-Za-z_]\w*(::[A-Za-z_]\w*)*$/.test(n) && (cpp || !n.includes('::')))
  if (!left.length) return {}
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-cconst-`), probe = `${work}/probe.${cpp ? 'cpp' : 'c'}`, out: Record<string, number> = {}
  try {
    for (let round = 0; round < 3 && left.length; round++) {
      fs.writeFileSync(probe, `#include ${JSON.stringify(path.resolve(file))}\n${left.map((n, i) => `enum gdp_k${i}_e ${cpp ? ': long long ' : ''}{ gdp_k${i} = (${n}) };`).join('\n')}\n`)
      let dump = ''
      try { dump = cp.execFileSync(clang, [...(cpp ? ['-x', 'c++'] : ['-x', 'c']), ...flags, '-w', '-ferror-limit=0', '-Xclang', '-ast-dump=json', '-Xclang', '-ast-dump-filter=gdp_k', '-fsyntax-only', probe], {encoding: 'utf8', maxBuffer: 1 << 28, stdio: ['ignore', 'pipe', 'pipe'], env: scrubbedClangEnv(), ...readerRun()}) }
      catch (e) {
        // (the lines that don't compile: their names left out, the rest tried again)
        const bad = new Set([...String((e as {stderr?: string}).stderr ?? '').matchAll(/probe\.c(?:pp)?:(\d+):\d+: error/g)].map(m => Number(m[1]) - 2))
        if (!bad.size) return out
        left = left.filter((_, i) => !bad.has(i))
        continue
      }
      for (const m of dump.matchAll(/"kind":\s*"EnumConstantDecl"[^]*?"name":\s*"gdp_k(\d+)"[^]*?"value":\s*"(-?\d+)"/g)) { const v = Number(m[2]); if (Number.isSafeInteger(v)) out[left[Number(m[1])]!] = v }
      break
    }
    return out
  } finally { try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ } }
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
  const at = (l: L | undefined, files?: Set<string>, pairs?: {spell: string, spellLine: number, expand: string, expandLine: number}[]): At | undefined => {
    if (!l) return undefined
    if (l.spellingLoc || l.expansionLoc) {
      const sp = at(l.spellingLoc, files, pairs), spFile = file, spLine = line
      const ex = at(l.expansionLoc, files, pairs), exFile = file, exLine = line
      if (pairs && spFile && exFile) pairs.push({spell: spFile, spellLine: spLine, expand: exFile, expandLine: exLine})
      return ex ?? sp
    }
    if (l.file !== undefined) file = l.file
    if (l.line !== undefined) line = l.line
    if (file && files) files.add(file)
    return l.offset === undefined ? undefined : {file, line, col: l.col ?? 0, off: l.offset, tok: l.tokLen ?? 0}
  }
  const walk = (n: CN) => {
    const files = new Set<string>()
    const pairs: {spell: string, spellLine: number, expand: string, expandLine: number}[] = []
    for (const k of Object.keys(n)) {
      if (k === 'loc') n.$at = at(n.loc, files, pairs)
      else if (k === 'range') { n.$b = at(n.range!.begin, files, pairs); n.$e = at(n.range!.end, files, pairs) }
      // (doc comments, FullComment and its parts, are no code)
      // (a for's absent parts are empty objects, kind-less)
      else if (k === 'inner' || k === 'array_filler') {
        const val = n[k]
        if (Array.isArray(val)) {
          const filtered = (val as CN[]).filter(c => !(c.kind ?? '').endsWith('Comment'))
          n[k] = filtered
          for (const c of filtered) walk(c)
        } else if (val && typeof val === 'object') walk(val as CN)
      }
    }
    n.$at ??= n.$b
    if (files.size) n.$files = files
    if (pairs.length) n.$macroExpansions = pairs
  }
  walk(root)
}

const CAST = new Set(['ImplicitCastExpr', 'CStyleCastExpr', 'CXXStaticCastExpr', 'CXXFunctionalCastExpr'])
const CMP = new Set(['==', '!=', '<', '<=', '>', '>=']), ARITH = new Set(['+', '-', '*', '/', '%', '<<', '>>', '&', '|', '^'])
const FAIL: Record<string, string> = {abort: 'abort()', __assert_rtn: 'an assertion failing', __assert_fail: 'an assertion failing', __assert: 'an assertion failing', _assert: 'an assertion failing', __builtin_trap: 'a trap', __builtin_unreachable: 'unreachable code reached (undefined behavior)'}

// --- the reading --------------------------------------------------------------------------------------------------------
// (`root`: the project's own files, whose functions are read too: a static inline helper of its header; by default the
// file's directory)
// (`picks`: an overloaded method's arity, the one read: `functions: ['throttle/1']`)
// (leave: globals the rule leaves out, an output the code writes for other code, never read into what it keeps)
// (cut: the file's own functions a call of which the request answers, as another file's)
export function readC(file: string, entry: string, tu: CN, target: CTarget, cpp = false, root?: string, picks: Record<string, number> = {}, pickNames: string[] = [], leave: string[] = [], cut: string[] = [], safety = false): CRead {
  const path = node<{resolve: (...p: string[]) => string, basename: (p: string) => string}>('node:path'), fs = node<{readFileSync: (p: string, e: string) => string, realpathSync: (p: string) => string}>('node:fs')
  const realPath = (p: string): string => { try { return fs.realpathSync(p) } catch { return path.resolve(p) } }
  const main = path.resolve(file), mainReal = realPath(file), base = path.basename(file), dir = `${path.resolve(root ?? main.replace(/\/[^/]*$/, ''))}/`, srcs = new Map<string, string>()
  locate(tu)
  const top = tu.inner ?? [], mine = (n: CN) => n.$at?.file === main || n.$at?.file === file, own = (n: CN) => mine(n) || (!!n.$at?.file && path.resolve(n.$at.file).startsWith(dir))
  const refuse = (n: CN | undefined, what: string): never => { throw new Refusal(pos(n), what) }
  const pos = (n: CN | undefined) => (n?.$at && own(n) ? `${path.basename(n.$at.file)}:${n.$at.line}:${n.$at.col}` : base)
  const src = (f: string) => { let s = srcs.get(f); if (s === undefined) { try { s = fs.readFileSync(path.resolve(f), 'utf8') } catch { s = '' }; srcs.set(f, s) } return s }
  const text = (n: CN) => (n.$b && n.$e && n.$b.file === n.$e.file && own(n) && n.$e.off + n.$e.tok >= n.$b.off ? src(n.$b.file).slice(n.$b.off, n.$e.off + n.$e.tok) || n.kind : n.kind)

  if (safety) {
    if (cpp) refuse(undefined, 'C++ is outside the checked C safety subset')
    if (leave.length || cut.length || Object.keys(picks).length) refuse(undefined, 'C safety does not allow erased state or call boundaries')
    if ((target.charBits ?? 8) !== 8 || target.int !== 32 || target.short !== 16) refuse(undefined, 'unsupported C integer ABI for safety lowering')
  }
  // The declarations: typedefs, records and enums of every file (a header's types are the file's too), the globals.
  const typedefs = new Map<string, {qual: string, desug?: string, rec?: string}>(), typedefNode = new Map<string, CN>(), records = new Map<string, CN>(), tags = new Map<string, string>(), anon = new Map<string, string>()
  const members = new Map<string, CN>(), fieldNode = new Map<string, CN>(), enums = new Map<string, CN>(), enumById = new Map<string, CN>(), cxx: CN[] = []
  const enumConst = new Map<string, number>(), named = new Map<string, number>(), globals = new Map<string, CN>(), globalByName = new Map<string, CN[]>(), redeclaredGlobals = new Set<string>(), fields = new Map<string, {rec: string, i: number}>(), recName = new Map<string, string>()
  const declOf = (n: CN): {id: string, kind: string} | undefined => n.decl ?? (n.inner ?? []).map(declOf).find(Boolean)
  const visitDecl = (n: CN) => {
    if (n.kind === 'TypedefDecl' && n.name) {
      if (n.id) typedefNode.set(n.id, n)
      const d = declOf(n)
      // (a typedef of an unnamed enum names it: clang 21 spells it `enum state_t`, desugared to the typedef's own name)
      const en = d?.kind === 'EnumDecl' ? enumById.get(d.id) : undefined
      if (en && !en.name) { for (const q of [n.name, `enum ${n.name}`]) enums.set(q, en); return }
      typedefs.set(n.name, {qual: n.type!.qualType, ...(n.type!.desugaredQualType ? {desug: n.type!.desugaredQualType} : {}), ...(d && (d.kind === 'RecordDecl' || d.kind === 'CXXRecordDecl') ? {rec: d.id} : {})})
      if (d && !recName.has(d.id)) recName.set(d.id, n.name)
    } else if ((n.kind === 'RecordDecl' || n.kind === 'CXXRecordDecl') && n.completeDefinition) {
      records.set(n.id!, n)
      if (n.name) { tags.set(`${n.tagUsed} ${n.name}`, n.id!); if (cpp) tags.set(n.name, n.id!) }
      if (n.$at) anon.set(`${n.$at.line}:${n.$at.col}`, n.id!)
      let i = 0, access = n.tagUsed === 'class' ? 'private' : 'public'
      for (const f of n.inner ?? []) {
        if (f.kind === 'FieldDecl') { fields.set(f.id!, {rec: n.id!, i: i++}); fieldNode.set(f.id!, f) }
        else if (f.kind === 'AccessSpecDecl') access = String(f.access)
        else if (/^CXX(Method|Constructor|Destructor|Conversion)Decl$/.test(f.kind)) { f.$rec = n.id; f.$access = access; members.set(f.id!, f); if (f.inner?.some(c => c.kind === 'CompoundStmt')) cxx.push(f) }
        else { if (f.kind === 'EnumDecl' && n.name) f.$outer = n.name; visitDecl(f) }
      }
    } else if (n.kind === 'EnumDecl') {
      enumById.set(n.id!, n)
      if (n.name) for (const q of [n.name, ...(n.$outer ? [`${n.$outer as string}::${n.name}`] : []), `enum ${n.name}`]) enums.set(q, n)
      let v = -1
      for (const c of n.inner ?? []) if (c.kind === 'EnumConstantDecl') { const k = c.inner?.length ? fold(c.inner[0]!) : undefined; v = k ?? v + 1; enumConst.set(c.id!, v); if (c.name) named.set(c.name, named.has(c.name) && named.get(c.name) !== v ? NaN : v) }
    } else if (n.kind === 'VarDecl') {
      globals.set(n.id!, n)
      if (n.previousDecl) { redeclaredGlobals.add(n.id!); redeclaredGlobals.add(String(n.previousDecl)) }
      if (n.name) {
        const list = globalByName.get(n.name) ?? []
        list.push(n); globalByName.set(n.name, list)
        if (list.length > 1) for (const d of list) if (d.id) redeclaredGlobals.add(d.id)
      }
    }
    else if (n.kind === 'LinkageSpecDecl' || n.kind === 'NamespaceDecl') for (const c of n.inner ?? []) visitDecl(c)
    // (a method defined outside its class: its class by the declaration's context)
    else if (/^CXX(Method|Constructor|Destructor)Decl$/.test(n.kind) && n.inner?.some(c => c.kind === 'CompoundStmt')) { n.$rec = n.parentDeclContextId as string; n.$access = members.get(n.previousDecl as string)?.$access ?? 'public'; cxx.push(n) }
  }
  // A literal's value exactly, through parentheses.
  const exact = (n: CN): bigint | undefined => n.kind === 'IntegerLiteral' ? BigInt(String(n.value)) : n.kind === 'ParenExpr' ? exact(n.inner![0]!) : undefined
  // A constant's value, where the node is one (literals, enum constants, a const global's, folded).
  const fold = (n: CN): number | undefined => {
    switch (n.kind) {
      // (a literal a double can't hold exactly: NaN, past 2^53, unless a cast takes it exactly)
      case 'IntegerLiteral': case 'CharacterLiteral': { const v = Number(n.value); return Number.isSafeInteger(v) ? v : NaN }
      case 'CXXBoolLiteralExpr': return n.value ? 1 : 0
      case 'CallExpr': { const m = /numeric_limits<\s*(.+?)\s*>::(max|min|lowest)\)?\s*\(\s*\)$/.exec(text(n)), it = m ? T(parseT(m[1]!)) : undefined; if (!it || it.k !== 'int') return undefined; const hi = it.signed ? 2 ** (it.bits! - 1) - 1 : 2 ** it.bits! - 1; return m![2] === 'max' ? hi : it.signed ? -hi - 1 : 0 }
      case 'ConstantExpr': return n.value !== undefined ? Number(n.value) : fold(n.inner![0]!)
      case 'ParenExpr': return fold(n.inner![0]!)
      case 'ImplicitCastExpr': case 'CStyleCastExpr': case 'CXXStaticCastExpr': case 'CXXFunctionalCastExpr': {
        const b = exact(n.inner![0]!), v = b !== undefined ? Number(b) : fold(n.inner![0]!), t = n.type ? T(tyOf(n.type)) : undefined
        if (v === undefined || t?.k !== 'int') return n.castKind === 'IntegralToBoolean' && v !== undefined ? +(v !== 0) : undefined
        if (b === undefined && !Number.isFinite(v)) return NaN
        // (exactly: at 64 bits 2^64 + 1 is 2^64 in a double)
        const m = 1n << BigInt(t.bits!), w = (((b ?? BigInt(Math.trunc(v))) % m) + m) % m
        return Number(t.signed && w >= m / 2n ? w - m : w)
      }
      case 'UnaryOperator': { const v = fold(n.inner![0]!); return v === undefined ? undefined : n.opcode === '-' ? -v : n.opcode === '+' ? v : n.opcode === '!' ? +(v === 0) : undefined }
      case 'BinaryOperator': {
        const a = fold(n.inner![0]!), b = fold(n.inner![1]!)
        if (a === undefined || b === undefined) return undefined
        switch (n.opcode ?? '') {
          case '+': return a + b
          case '-': return a - b
          case '*': return a * b
          case '/': return b ? Math.trunc(a / b) : undefined
          case '%': return b ? a % b : undefined
          case '<<': return a * 2 ** b
          default: return undefined
        }
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
    // (the standard's fixed widths, for a dump that holds no typedefs: C++'s, filtered)
    int8_t: [8, true], int16_t: [16, true], int32_t: [32, true], int64_t: [64, true], uint8_t: [8, false], uint16_t: [16, false], uint32_t: [32, false], uint64_t: [64, false],
    size_t: [target.long, false], ssize_t: [target.long, true], ptrdiff_t: [target.long, true], intptr_t: [target.long, true], uintptr_t: [target.long, false],
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
    // (a void * field: a flag where the code only sets it to NULL or not and tests it against NULL, CANopen's CO_FLAG;
    // any other use of it refused where it is)
    ttab[t]!.fields = (r.inner ?? []).filter(f => f.kind === 'FieldDecl').map(f => { const ft = tyOf(f.type!), pt = T(ft); return {name: f.name ?? '', t: pt.k === 'ptr' && T(pt.elem!).k === 'void' ? add(`nullflag:${f.type!.qualType}`, {k: 'bool', go: f.type!.qualType, nullflag: true}) : ft, embedded: false} })
    return t
  }
  function tyOf(ty: {qualType: string, desugaredQualType?: string}): number { return parseT(ty.qualType, ty.desugaredQualType) }
  function parseT(s0: string, desug?: string): number {
    const s = s0.replace(/\b(const|volatile|restrict|__restrict)\b/g, '').replace(/\s+/g, ' ').replace(/ \*/g, '*').replace(/\*/g, ' *').replace(/\* \*/g, '**').trim()
    if (safety && !s.includes('*') && typedefs.has(s)) {
      const td = typedefs.get(s)!, underlying = td.desug ?? td.qual
      if (!td.rec || /[*[]/.test(underlying)) {
        const it = T(parseT(underlying))
        if (it.k === 'int') return intT(s, it.bits!, it.signed!)
        return it.k === 'bool' ? boolT : parseT(underlying)
      }
    }
    if (s === '_Bool' || s === 'bool') return boolT
    const arr = /^(.*?)\s*\[(\d+)\]$/.exec(s)
    if (arr) return add(`arr:${s}`, {k: 'array', go: s, elem: parseT(arr[1]!), len: Number(arr[2]), fixed: true})
    // (an unnamed struct's spelling, `struct (unnamed struct at f.c:3:8)`, is no function type)
    const un0 = /^(struct|union|class) \((?:unnamed|anonymous) (?:struct|union|class) at .*:(\d+):(\d+)\)$/.exec(s)
    if (un0) { const id = anon.get(`${un0[2]}:${un0[3]}`); return id ? recT(id) : add(`opaque:${s}`, {k: 'opaque', go: s}) }
    if (/\(\*\)|\(.*\)$/.test(s)) return add(`fn:${s}`, {k: 'func', go: s})
    if (/\*$/.test(s)) { const e = parseT(s.replace(/\s*\*$/, '')); return add(`ptr:${e}`, {k: 'ptr', go: s, elem: e}) }
    if (/&$/.test(s)) return add(`ref:${s}`, {k: 'ref', go: s})
    if (ints[s]) return intT(s, ...ints[s]!)
    if (cpp && /^std::\w+$/.test(s) && ints[s.slice(5)]) return intT(s.slice(5), ...ints[s.slice(5)]!)
    if (s === 'float' || s === 'double' || s === 'long double') return add(`f:${s}`, {k: 'float', go: s})
    if (s === 'void') return add('void', {k: 'void', go: 'void'})
    const un = /^(struct|union|class) \((?:unnamed|anonymous) (?:struct|union|class) at .*:(\d+):(\d+)\)$/.exec(s)
    if (un) { const id = anon.get(`${un[2]}:${un[3]}`); return id ? recT(id) : add(`opaque:${s}`, {k: 'opaque', go: s}) }
    const std = /^std::(?:__1::|__cxx11::)?(array<(.+), (\d+)>|mutex|recursive_mutex|timed_mutex|shared_mutex)$/.exec(s)
    if (std) return std[2] ? add(`arr:${s}`, {k: 'array', go: s, elem: parseT(std[2]), len: Number(std[3]), fixed: true}) : add(`mutex:${s}`, {k: 'ext', mutex: true, go: s})
    if (enums.has(s)) return enumT(s)
    if (tags.has(s)) return recT(tags.get(s)!, s)
    // (C++: a class named with its namespaces, as `this`'s type is)
    if (cpp && /::/.test(s) && tags.has(s.replace(/^(\w+::)+/, ''))) return recT(tags.get(s.replace(/^(\w+::)+/, ''))!, s)
    const td = typedefs.get(s.replace(/^(struct|union|class) /, ''))
    if (td) {
      if (td.rec && !/[*[]/.test(td.desug ?? td.qual) && records.has(td.rec)) return recT(td.rec, s)
      const inner = parseT(td.desug ?? td.qual), it = T(inner)
      // (an integer type keeps its name: the notes and the harness spell it so)
      return it.k === 'int' ? intT(s, it.bits!, it.signed!) : inner
    }
    // (an integer typedef the dump doesn't hold, already met desugared: a field's)
    if (tkey.has(`int:${s}`)) return tkey.get(`int:${s}`)!
    if (desug && desug !== s0) { const it = parseT(desug); return T(it).k === 'int' && !/[<:]/.test(s) ? intT(s, T(it).bits!, T(it).signed!) : it }
    return add(`opaque:${s}`, {k: 'opaque', go: s})
  }
  // An enum is its integer type: its fixed one (C++), else int, unsigned where no enumerator is negative (clang's).
  const enumT = (s: string): number => {
    const d = enums.get(s), vals = (d?.inner ?? []).filter(c => c.kind === 'EnumConstantDecl').map(c => enumConst.get(c.id!) ?? 0)
    const fixed = (d?.fixedUnderlyingType as {qualType: string} | undefined)?.qualType, ft = fixed ? T(parseT(fixed)) : undefined
    // (C++, no fixed type: its values are those of the smallest bit-field holding every enumerator, another one
    // undefined to make, the sanitizer's trap where it is read)
    if (cpp && !ft) {
      const lo = Math.min(0, ...vals), hi = Math.max(0, ...vals)
      let b = 1
      if (lo < 0) while (-(2 ** (b - 1)) > lo || hi > 2 ** (b - 1) - 1) b++
      else while (hi > 2 ** b - 1) b++
      return add(`int:${s}`, {k: 'int', go: s, bits: b, signed: lo < 0, ub: true})
    }
    return intT(s, ft?.bits ?? target.int, ft ? ft.signed! : vals.some(v => v < 0))
  }
  for (const n of top) if (!n.isImplicit) visitDecl(n)
  // (a typedef of a struct declared before its definition names the definition)
  for (const [name, td] of typedefs) { const id = tags.get(td.qual.replace(/^const /, '')); if (id && !recName.has(id)) recName.set(id, name); if (id && !(td.rec && records.has(td.rec))) td.rec = id }

  // --- expressions ---------------------------------------------------------------------------------------------------------
  const funcs = new Map<string, CN>()
  for (const n of top) if ((n.kind === 'FunctionDecl') && own(n) && n.inner?.some(c => c.kind === 'CompoundStmt')) funcs.set(n.name!, n)
  const entryRec = tags.get(`struct ${entry}`) ?? tags.get(entry) ?? typedefs.get(entry)?.rec
  const params = (f: CN) => (f.inner ?? []).filter(c => c.kind === 'ParmVarDecl')
  // C++: the class's methods (this the receiver; an overload refused where it is called), its constructor.
  const ctors: CN[] = [], overloaded = new Set<string>()
  for (const m of cxx) {
    if (m.$rec !== entryRec) continue
    // (a constructor the check can't call, private or protected: refused, the object is made with it)
    if (m.kind === 'CXXConstructorDecl') { if (!/\((const )?\w+ &&?\)/.test(m.type!.qualType) || params(m).length !== 1) { if (m.$access !== 'public') refuse(m, `${entry}: its constructor is ${String(m.$access)} (the check makes the object with it)`); ctors.push(m) } continue }
    if (m.kind !== 'CXXMethodDecl' || /^operator/.test(m.name!)) continue
    m.$m = true
    if (picks[m.name!] !== undefined) { if (params(m).length === picks[m.name!]) funcs.set(m.name!, m); continue }
    if (funcs.has(m.name!)) overloaded.add(m.name!)
    funcs.set(m.name!, m)
  }
  // The file's globals as the state (C, the entry the file's stem, no struct of that name): each global its functions
  // read or write a field of one object, `this`, every function of the file a method of it. A global the functions
  // only read that the file doesn't own (extern, volatile, or another file's to write: not static) is the request's:
  // the value each request finds there, set by the check before the call (read once a request).
  const stem = base.replace(/\.[^.]*$/, ''), gmode = !entryRec && !cpp && entry === stem
  const gfield = new Map<string, number>(), ginput = new Set<string>(), gnodes: CN[] = [], fnReads = new Map<string, Set<string>>(), left = new Set<string>()
  if (gmode) {
    const reads = new Set<string>(), writes = new Set<string>(), all = new Set<string>()
    const bare = (n: CN): CN => ((n.kind === 'ParenExpr' || CAST.has(n.kind) && ['LValueToRValue', 'NoOp'].includes(n.castKind!)) && n.inner?.length ? bare(n.inner[0]!) : n)
    const root = (n0: CN): CN | undefined => { const n = bare(n0); return n.kind === 'DeclRefExpr' ? n : n.kind === 'MemberExpr' || n.kind === 'ArraySubscriptExpr' ? root(n.inner![0]!) : (CAST.has(n.kind) && n.castKind === 'ArrayToPointerDecay') ? root(n.inner![0]!) : undefined }
    const scan = (n: CN) => {
      const w = n.kind === 'BinaryOperator' && n.opcode === '=' || n.kind === 'CompoundAssignOperator' ? root(n.inner![0]!) : n.kind === 'UnaryOperator' && ['++', '--', '&'].includes(n.opcode!) ? root(n.inner![0]!) : undefined
      const d = w?.referencedDecl
      if (d?.kind === 'VarDecl' && globals.has(d.id)) writes.add(d.id)
      if (n.kind === 'DeclRefExpr' && n.referencedDecl?.kind === 'VarDecl' && globals.has(n.referencedDecl.id)) { reads.add(n.referencedDecl.id); all.add(n.referencedDecl.id) }
      for (const c of n.inner ?? []) scan(c)
    }
    for (const [name, f] of funcs) { const r0 = new Set(reads); reads.clear(); scan(f); fnReads.set(name, new Set(reads)); for (const id of r0) reads.add(id) }
    // (and the functions each one calls, read through)
    const callees = (f: CN, out = new Set<string>()): Set<string> => { const w = (n: CN) => { if (n.kind === 'DeclRefExpr' && n.referencedDecl?.kind === 'FunctionDecl' && funcs.has(n.referencedDecl.name) && !out.has(n.referencedDecl.name)) { out.add(n.referencedDecl.name); w(funcs.get(n.referencedDecl.name)!) } for (const c of n.inner ?? []) w(c) }; w(f); return out }
    for (const [name, f] of funcs) for (const g of callees(f)) for (const id of fnReads.get(g) ?? []) fnReads.get(name)!.add(id)
    for (const [id, g] of globals) {
      if (!all.has(id)) continue
      if (leave.includes(g.name!)) { left.add(id); continue }
      const qt = g.type!.qualType
      if (!safety && /^const /.test(qt) && !writes.has(id)) continue
      if (safety && /\bconst\b/.test(qt) && /\[\d+\]/.test(qt) && g.init && !writes.has(id)) continue
      if (/\[\]$/.test(qt.trim())) refuse(g, `${g.name}: an array of unknown size (its length is another file's)`)
      if (!safety && !writes.has(id) && (g.storageClass === 'extern' || /\bvolatile\b/.test(qt) || g.storageClass !== 'static')) ginput.add(id)
      gfield.set(id, gnodes.length); gnodes.push(g)
    }
    if (!safety && !gnodes.length) refuse(undefined, `no global of ${base} its functions read or write (the state, when the file keeps it in globals)`)
  }
  const entryT = entryRec ? recT(entryRec, entry) : gmode ? add(`globals:${entry}`, {k: 'struct', own: true, name: entry, go: 'gdp_G', fields: gnodes.map(g => ({name: g.name!, t: tyOf(g.type!), embedded: false}))}) : refuse(undefined, `no ${cpp ? 'class' : 'struct'} ${entry} in ${base}${cpp ? ' (a class template is outside the subset)' : ''}${!cpp && entry !== stem ? ` (a file that keeps its state in globals: name ${stem}, its stem)` : ''}`)
  const ptrT = add(`ptr:${entryT}`, {k: 'ptr', go: `${entry} *`, elem: entryT}), self0 = (n: CN): GX => ({e: 'id', ...at(n, ptrT), o: 'var', id: 'this', n: 'this'})
  // An out-parameter (a pointer to an integer or a bool, not the receiver): a pointer to a box of one field, `value`,
  // *p its field.
  const boxed = new Map<string, number>(), byValue = new Map<string, number>(), refs = new Set<string>(), structRefs = new Set<string>()
  const boxOf = (q: CN): number => {
    // (a const reference to an integer is its value: an input)
    if (/^const [^*&]*&$/.test(q.type!.qualType.trim())) { const v = parseT(q.type!.qualType.trim().slice(0, -1), q.type!.desugaredQualType?.trim().replace(/&$/, '')); byValue.set(q.id!, v); return v }
    const ref = /[^&]&$/.test(q.type!.qualType.trim()), t = ref ? parseT(q.type!.qualType.trim().slice(0, -1), q.type!.desugaredQualType?.trim().replace(/&$/, '')) : tyOf(q.type!), pt = ref ? {k: 'ptr', elem: t, go: q.type!.qualType} : T(t)
    // (C++: a reference to a struct, the caller's object, read as a pointer to it)
    if (ref && T(t).k === 'struct') { const r = add(`ref:${t}`, {k: 'ptr', go: q.type!.qualType, elem: t}); byValue.set(q.id!, r); structRefs.add(q.id!); return r }
    if (pt.k !== 'ptr' || !['int', 'bool'].includes(T(pt.elem!).k)) return tyOf(q.type!)
    if (ref) refs.add(q.id!)
    const e = pt.elem!, b = add(`box:${e}`, {k: 'struct', own: true, box: true, name: T(e).go, go: T(e).go, fields: [{name: 'value', t: e, embedded: false}]}), bp = add(`ptr:${b}`, {k: 'ptr', go: pt.go, elem: b})
    boxed.set(q.id!, bp)
    return bp
  }
  const THIS = {kind: 'ParmVarDecl', id: 'this', name: 'this', type: {qualType: `${entry} *`}} as CN
  const recvOf = (f: CN) => { if (gmode) return THIS; if (f.$m) return f.storageClass === 'static' ? undefined : THIS; const p = params(f)[0], t = p ? T(tyOf(p.type!)) : undefined; return t?.k === 'ptr' && t.elem === entryT ? p : undefined }
  const args0 = (f: CN) => (f.$m || gmode ? params(f) : params(f).slice(recvOf(f) ? 1 : 0))
  for (const f of [...funcs.values(), ...ctors]) for (const q of args0(f)) boxOf(q)
  const strip = (n: CN): CN => ((['ParenExpr', 'MaterializeTemporaryExpr', 'ExprWithCleanups', 'CXXBindTemporaryExpr', 'CXXDefaultInitExpr'].includes(n.kind) || (n.kind === 'UnaryOperator' && n.opcode === '__extension__') || (CAST.has(n.kind) && ['LValueToRValue', 'NoOp'].includes(n.castKind!))) && n.inner?.length ? strip(n.inner[0]!) : n)
  // A default member initializer's use (CXXDefaultInitExpr): clang 19 dumps the initializer inside it, clang 18 and
  // earlier nothing (nor the field), so a constructor's is given its field's own (an empty one elsewhere is refused).
  const fillDefault = (n: CN, f: CN | undefined): CN => {
    if (n.kind === 'CXXDefaultInitExpr' && !n.inner?.length && f?.inner?.length && !f.inner[0]!.kind.endsWith('Attr')) n.inner = [f.inner[0]!]
    return n
  }
  const at = (n: CN, t: number) => ({p: pos(n), t, text: text(n)})
  // Use the AST node's source range, not the wording or position of an emitted diagnostic.
  // In safety mode, sites are inventoried before lowering and frozen so lowering cannot silently create or drop sites.
  const sites = new Map<CN, SafetySite>(), locations = new Map<string, number>()
  let sitesFrozen = false, activeSites: SafetySite[] | undefined
  const siteOf = (n: CN, kind: SafetySite['kind']): SafetySite => {
    const old = sites.get(n)
    if (old) {
      if (old.kind !== kind) refuse(n, `mismatched C safety site kind (${old.kind} vs ${kind})`)
      if (activeSites && !activeSites.includes(old)) activeSites.push(old)
      return old
    }
    if (sitesFrozen) refuse(n, 'lowering requested an uninventoried C safety site')
    const start = n.$b ?? refuse(n, 'a checked C operation without a source range')
    const loc = `${path.basename(start.file)}:${start.line}:${start.col}`
    const idx = (locations.get(loc) ?? 0) + 1
    locations.set(loc, idx)
    const site = {where: idx === 1 ? loc : `${loc}#${idx}`, kind}
    sites.set(n, site)
    if (activeSites) activeSites.push(site)
    return site
  }
  const checked = (n: CN, t: number, op: string): Pick<GX, 'checkedType' | 'site'> => {
    if (!safety || !['+', '-', '*', '/', '%', '&'].includes(op)) return {}
    const kind = op === '/' || op === '%' ? 'division' : op !== '&' && T(t).signed ? 'overflow' : undefined
    return {checkedType: t, ...(kind ? {site: siteOf(n, kind)} : {})}
  }
  // Clang's JSON AST emits array_filler as [filler, ...semanticInits] with no inner key when an
  // InitListExpr has an array filler (partial or designated initializers). Handle both that form
  // and a separated array_filler + inner form, and refuse unknown/union shapes.
  const initListChildren = (n: CN): {elems: CN[], filler?: CN} | undefined => {
    if (n.kind !== 'InitListExpr' || 'field' in n) return undefined
    const rawFiller = n.array_filler as CN[] | CN | undefined
    if (rawFiller === undefined) return {elems: n.inner ?? []}
    if (Array.isArray(rawFiller)) {
      if (!rawFiller.length) return undefined
      if (n.inner === undefined) return {filler: rawFiller[0]!, elems: rawFiller.slice(1)}
      if (rawFiller.length === 1) return {filler: rawFiller[0]!, elems: n.inner}
      return undefined
    }
    if (typeof rawFiller === 'object' && rawFiller !== null && 'kind' in rawFiller && n.inner !== undefined)
      return {filler: rawFiller, elems: n.inner}
    return undefined
  }
  const isAllZeroInit = (n0: CN): boolean => {
    const n = strip(n0)
    if (n.kind === 'ImplicitValueInitExpr') return true
    if (n.kind === 'InitListExpr') {
      const il = initListChildren(n)
      if (!il) return false
      if (il.filler && strip(il.filler).kind !== 'ImplicitValueInitExpr') return false
      return il.elems.every(isAllZeroInit)
    }
    return fold(n) === 0
  }
  const fitsIn = (v: bigint, t: TT): boolean => {
    if (t.k === 'bool') return v === 0n || v === 1n
    if (t.k !== 'int' || !t.bits || t.bits < 1 || t.bits > 32) return false
    const lo = t.signed ? -(1n << BigInt(t.bits - 1)) : 0n
    const hi = t.signed ? (1n << BigInt(t.bits - 1)) - 1n : (1n << BigInt(t.bits)) - 1n
    return v >= lo && v <= hi
  }
  const exactConstInit = (n0: CN, et: TT): number | undefined => {
    const n = strip(n0)
    if (n.kind === 'ImplicitValueInitExpr') return 0
    if (n.kind === 'ConstantExpr' && n.inner?.length === 1) return exactConstInit(n.inner[0]!, et)
    if (n.kind === 'ImplicitCastExpr' && n.inner?.length === 1) {
      if (n.castKind === 'NoOp') return exactConstInit(n.inner[0]!, et)
      if (n.castKind === 'IntegralCast') {
        const ct = n.type ? T(tyOf(n.type)) : undefined
        if (!ct) return undefined
        const v = exactConstInit(n.inner[0]!, ct)
        return v !== undefined && fitsIn(BigInt(v), et) ? v : undefined
      }
      if (n.castKind === 'IntegralToBoolean') {
        const it = n.inner[0]?.type ? T(tyOf(n.inner[0].type)) : undefined
        if (!it) return undefined
        const v = exactConstInit(n.inner[0]!, it)
        return v === undefined ? undefined : (v === 0 ? 0 : 1)
      }
      return undefined
    }
    if (n.kind === 'CXXBoolLiteralExpr') return n.value ? 1 : 0
    let v: bigint | undefined
    if (n.kind === 'IntegerLiteral' && n.value !== undefined) v = BigInt(n.value)
    else if (n.kind === 'UnaryOperator' && (n.opcode === '-' || n.opcode === '+') && n.inner?.length === 1) {
      const inner = strip(n.inner[0]!)
      if (inner.kind === 'IntegerLiteral' && inner.value !== undefined) v = n.opcode === '-' ? -BigInt(inner.value) : BigInt(inner.value)
    }
    if (v === undefined) return undefined
    if (n.type && !fitsIn(v, T(tyOf(n.type)))) return undefined
    if (et.k === 'bool') return v === 0n ? 0 : 1
    if (!fitsIn(v, et)) return undefined
    return Number(v)
  }
  type SafetyTable = {g: CN, dims: number[], idx: CN[], nodes: CN[], vals: number[], elemT: number}
  const constTableOf = (n: CN): SafetyTable | undefined => {
    const idx: CN[] = [], nodes: CN[] = []
    let b: CN = n
    while (b.kind === 'ArraySubscriptExpr') {
      nodes.unshift(b); idx.unshift(b.inner![1]!)
      b = strip(b.inner![0]!)
      if (CAST.has(b.kind) && b.castKind === 'ArrayToPointerDecay') b = strip(b.inner![0]!)
    }
    const d = b.kind === 'DeclRefExpr' ? b.referencedDecl : undefined
    if (d?.kind !== 'VarDecl' || !globals.has(d.id)) return undefined
    const g = globals.get(d.id)!, qt = g.type?.qualType ?? ''
    if (!/\bconst\b/.test(qt) || /\b(?:volatile|_Atomic|enum)\b/.test(`${qt} ${g.type?.desugaredQualType ?? ''}`)) return undefined
    if (g.storageClass !== 'static' || g.tls || !mine(g) || !g.init || g.inner?.length !== 1 || g.inner.some(k => k.kind.endsWith('Attr'))) return undefined
    if (g.previousDecl || redeclaredGlobals.has(g.id!) || (g.name && (globalByName.get(g.name)?.length ?? 0) > 1)) return undefined
    const dims = [...qt.matchAll(/\[(\d+)\]/g)].map(m => Number(m[1]))
    if (!dims.length || dims.length !== idx.length || dims.some(k => !Number.isSafeInteger(k) || k <= 0)) return undefined
    const total = dims.reduce((u, v) => u * v, 1)
    if (!Number.isSafeInteger(total) || total <= 0 || total > 256) return undefined
    const elemT = n.type ? tyOf(n.type) : -1, et = T(elemT)
    if (!et || et.nullflag || !(et.k === 'bool' || et.k === 'int' && et.bits! > 0 && et.bits! <= 32)) return undefined
    const vals: number[] = []
    const fill = (v: CN | undefined, dim: number): boolean => {
      if (!v) return false
      const s0 = strip(v)
      if (dim === dims.length) {
        const k = exactConstInit(s0, et)
        if (k === undefined) return false
        vals.push(k); return true
      }
      if (s0.kind === 'ImplicitValueInitExpr') {
        const count = dims.slice(dim).reduce((u, w) => u * w, 1)
        for (let i = 0; i < count; i++) vals.push(0)
        return true
      }
      const il = initListChildren(s0)
      if (!il) return false
      const {elems, filler} = il
      if (elems.length > dims[dim]! || elems.some(k => k.kind === 'DesignatedInitExpr' || k.kind === 'DesignatedInitUpdateExpr' || k.kind === 'NoInitExpr')) return false
      if (filler && strip(filler).kind !== 'ImplicitValueInitExpr') return false
      if (elems.length < dims[dim]! && !filler) return false
      for (let i = 0; i < dims[dim]!; i++) if (!fill(i < elems.length ? elems[i] : filler, dim + 1)) return false
      return true
    }
    if (!fill(g.inner[0], 0) || vals.length !== total) return undefined
    return {g, dims, idx, nodes, vals, elemT}
  }
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
  // (a pointer flag's field, read where a flag is: tested, compared with NULL)
  const flagOf = (n0: CN): CN | undefined => { let n = strip(n0); while (CAST.has(n.kind) && ['BitCast', 'NoOp', 'LValueToRValue'].includes(n.castKind!)) n = strip(n.inner![0]!); const f = n.kind === 'MemberExpr' ? fields.get(n.referencedMemberDecl!) : undefined; return f && T(T(recT(f.rec)).fields![f.i]!.t).nullflag ? n : undefined }
  const isNull = (n0: CN): boolean => { const n = strip(n0); return (CAST.has(n.kind) && (n.castKind === 'NullToPointer' || ((n.castKind === 'IntegralToPointer' || n.castKind === 'BitCast') && isNull(n.inner![0]!)))) || fold(n) === 0 || n.kind === 'CXXNullPtrLiteralExpr' || n.kind === 'GNUNullExpr' }
  let flagRead = false
  const readFlag = (n: CN): GX => { flagRead = true; try { return x(n) } finally { flagRead = false } }
  // A condition: a boolean as it is; a number compared with 0; a pointer with NULL.
  const cond = (n0: CN): GX => {
    const n = strip(n0)
    const fl = flagOf(n.kind === 'ImplicitCastExpr' && n.castKind === 'PointerToBoolean' ? n.inner![0]! : n)
    if (fl) return readFlag(fl)
    if (n.kind === 'BinaryOperator' && (n.opcode === '==' || n.opcode === '!=') && (flagOf(n.inner![0]!) || flagOf(n.inner![1]!))) {
      const [f, o] = flagOf(n.inner![0]!) ? [flagOf(n.inner![0]!)!, n.inner![1]!] : [flagOf(n.inner![1]!)!, n.inner![0]!]
      if (!isNull(o)) return no(n, `${text(n)}: a pointer flag compared with other than NULL`)
      const v = readFlag(f)
      return n.opcode === '!=' ? v : {e: 'un', ...at(n, boolT), op: '!', x: v}
    }
    if (n.kind === 'CallExpr' && calleeName(n) === '__builtin_expect') return cond(n.inner![1]!)
    if ((n.kind === 'ImplicitCastExpr' || n.kind === 'CStyleCastExpr') && ['IntegralCast', 'IntegralToBoolean', 'PointerToBoolean'].includes(n.castKind!) && isBoolish(n.inner![0]!)) return cond(n.inner![0]!)
    if (n.kind === 'BinaryOperator' && CMP.has(n.opcode!)) return {e: 'bin', ...at(n, boolT), op: n.opcode, x: x(n.inner![0]!), y: x(n.inner![1]!)}
    if (n.kind === 'BinaryOperator' && (n.opcode === '&&' || n.opcode === '||')) return {e: 'bin', ...at(n, boolT), op: n.opcode, x: cond(n.inner![0]!), y: guard(() => cond(n.inner![1]!))}
    if (n.kind === 'UnaryOperator' && n.opcode === '!') return {e: 'un', ...at(n, boolT), op: '!', x: cond(n.inner![0]!)}
    const v = ((n.kind === 'ImplicitCastExpr' || safety && n.kind === 'CStyleCastExpr') && (n.castKind === 'IntegralToBoolean' || n.castKind === 'PointerToBoolean')) ? n.inner![0]! : n, vt = v.type ? tyOf(v.type) : -1
    if (vt >= 0 && T(vt).k === 'bool') return x(v)
    const k = safety ? undefined : fold(v)
    if (k !== undefined) return {e: 'lit', ...at(n, boolT), c: {bool: k !== 0}}
    if (vt >= 0 && T(vt).k === 'ptr') return {e: 'bin', ...at(n, boolT), op: '!=', x: x(v), y: {e: 'id', ...at(n, vt), o: 'nil'}}
    if (vt >= 0 && T(vt).k === 'int') return {e: 'bin', ...at(n, boolT), op: '!=', x: x(v), y: lit(n, 0, vt)}
    return no(n, `${text(n)}: a condition of type ${n.type?.qualType}`)
  }
  // A side effect inside an expression (an assignment, ++ or --, `if (--timer > 0)`): its statement run before the
  // statement it is in, the expression its value; where it runs only on some paths (the right of && or ||, a branch of
  // ?:), refused.
  let pending: GS[] | undefined, guarded = 0, temps = 0
  const guard = <T>(f: () => T): T => { guarded++; try { return f() } finally { guarded-- } }
  const effect = (n: CN, value: () => GX, before: GS[] = []): GX => {
    if (!pending || guarded) return no(n, `${text(n)}: ${guarded ? 'a side effect on some paths of an expression (the right of && or ||, a branch of ?:)' : 'a side effect inside an expression (the subset reads it as a statement)'}`)
    pending.push(...before, ...st(n))
    return value()
  }
  const pre = <T>(f: () => T): [GS[], T] => { const outer = pending, og = guarded; pending = []; guarded = 0; try { const v = f(); return [pending, v] } finally { pending = outer; guarded = og } }
  // (a float's value: left out, a value nothing the rule keeps may read; one read into an integer, a condition or a
  // comparison is refused there. Its operands are the code's measurements: an assignment or a call of the file's own
  // inside it is refused, its effect would be lost.)
  // A constant table read at indices (a transition table, a lookup; a const or constexpr array, a class's static one):
  // its entry by cases on the indices, each index outside its dimension undefined behavior, the step's failure (checked
  // before the statement, so the index must be free of side effects and read where the statement surely reads it).
  const table = (n: CN): GX | undefined => {
    const idx: CN[] = []
    let b: CN = n
    while (b.kind === 'ArraySubscriptExpr') { idx.unshift(b.inner![1]!); b = strip(b.inner![0]!); if (CAST.has(b.kind) && b.castKind === 'ArrayToPointerDecay') b = strip(b.inner![0]!) }
    const d = b.kind === 'DeclRefExpr' ? b.referencedDecl : undefined
    if (d?.kind !== 'VarDecl' || !globals.has(d.id)) return undefined
    const g0 = globals.get(d.id)!, g = g0.init ? g0 : [...globals.values()].find(v => v.name === g0.name && v.init) ?? g0, qt = g.type!.qualType
    if (!/^(const |constexpr )|\bconst\b/.test(qt) || !g.init) return undefined
    const init = (g.inner ?? []).find(c => !c.kind.endsWith('Attr'))
    if (!init) return undefined
    const t = n.type ? tyOf(n.type) : -1, a = at(n, t)
    // (the table's values, nested by dimension; an entry not given is 0)
    const dims: number[] = [...qt.matchAll(/\[(\d+)\]/g)].map(m => Number(m[1]))
    if (dims.length !== idx.length || !['int', 'bool'].includes(T(t).k)) return no(n, `${text(n)}: a table read other than at every one of its dimensions`)
    const val = (v: CN | undefined, path: number[], k: number): number => {
      if (!v) return NaN
      const s0 = strip(v)
      if (s0.kind === 'ImplicitValueInitExpr') return 0
      if (k === dims.length) { const f = fold(s0); return f ?? NaN }
      const il = initListChildren(s0)
      if (!il) return NaN
      const {elems, filler} = il
      if (elems.length > dims[k]! || elems.some(c => c.kind === 'DesignatedInitExpr' || c.kind === 'DesignatedInitUpdateExpr' || c.kind === 'NoInitExpr')) return NaN
      if (filler && strip(filler).kind !== 'ImplicitValueInitExpr') return NaN
      if (elems.length < dims[k]! && !filler) return NaN
      const i = path[k]!
      return val(i < elems.length ? elems[i] : filler, path, k + 1)
    }
    if (idx.some(effects)) return no(n, `${text(n)}: a table read at an index with a side effect`)
    if (!pending || guarded) return no(n, `${text(n)}: a table read on some paths of an expression (the right of && or ||, a branch of ?:)`)
    const ix = idx.map(i => x(i)), ty = (i: number) => (ix[i]!.t >= 0 ? ix[i]!.t : intT('int', target.int, true))
    const inRange = ix.map((v, i): GX => ({e: 'bin', ...at(idx[i]!, boolT), op: '&&', x: {e: 'bin', ...at(idx[i]!, boolT), op: '<=', x: lit(idx[i]!, 0, ty(i)), y: v}, y: {e: 'bin', ...at(idx[i]!, boolT), op: '<', x: v, y: lit(idx[i]!, dims[i]!, ty(i))}}))
    pending.push({s: 'if', p: pos(n), c: {e: 'un', ...at(n, boolT), op: '!', x: inRange.reduce((l, r) => ({e: 'bin', ...at(n, boolT), op: '&&', x: l, y: r}))}, then: [{s: 'expr', p: pos(n), x: {e: 'call', ...at(n, -1), builtin: 'panic', a: [], what: `${text(n)}: an index past the table (undefined behavior)`}}]})
    // (by cases: each dimension's index against each of its values, the last value the rest)
    const build = (k: number, path: number[]): GX => {
      if (k === dims.length) { const v = val(init, path, 0); if (!Number.isSafeInteger(v)) return no(n, `${text(n)}: an entry that isn't a constant integer`); return T(t).k === 'bool' ? {e: 'lit', ...a, c: {bool: v !== 0}} : lit(n, v, t) }
      let out = build(k + 1, [...path, dims[k]! - 1])
      for (let j = dims[k]! - 2; j >= 0; j--) out = {e: 'ite', ...a, x: {e: 'bin', ...at(idx[k]!, boolT), op: '==', x: ix[k]!, y: lit(idx[k]!, j, ty(k))}, y: build(k + 1, [...path, j]), b: out}
      return out
    }
    return build(0, [])
  }
  let placing = false
  // (a place in a global left out, or its address)
  // (a field of the entry left out, `leave`, or anything reached through one: an object other code owns, a buffer the
  // code writes for it)
  const leftField = (n: CN) => { const f = fields.get(n.referencedMemberDecl ?? ''); return !!f && f.rec === entryRec && leave.includes(String(n.name)) }
  const leftOut = (n0: CN): boolean => { const n = strip(n0); if (n.kind === 'DeclRefExpr') return left.has(n.referencedDecl?.id ?? ''); if (n.kind === 'MemberExpr' && leftField(n)) return true; if (n.kind === 'MemberExpr' || n.kind === 'ArraySubscriptExpr' || (n.kind === 'UnaryOperator' && n.opcode === '&') || (CAST.has(n.kind) && n.castKind === 'ArrayToPointerDecay')) return leftOut(n.inner![0]!); return false }
  const effects = (n: CN): boolean => (n.kind === 'CallExpr' && funcs.has(calleeName(n) ?? '')) || ['CompoundAssignOperator'].includes(n.kind) || (n.kind === 'BinaryOperator' && n.opcode === '=') || (n.kind === 'UnaryOperator' && ['++', '--'].includes(n.opcode!)) || (n.inner ?? []).some(effects)
  const x = (n0: CN): GX => {
    const n = strip(n0), t = n.type ? tyOf(n.type) : -1, a = at(n, t), kids = n.inner ?? []
    const asPlace = placing; placing = false
    if ((left.size || leave.length) && leftOut(n)) return {e: 'opaque', ...a, why: `${text(n)}: left out (leave: an output for other code, never read into the rule)`}
    if (t >= 0 && T(t).k === 'float' && !asPlace) return effects(n) ? no(n, `${text(n)}: a float computed with an effect of the file's own code (floats are left out)`) : {e: 'opaque', ...a, why: `${text(n)}: a float (left out of the rule: a binary fraction that rounds)`}
    const k = !safety && t >= 0 && T(t).k === 'int' ? fold(n) : undefined
    if (k !== undefined) return Number.isSafeInteger(k) ? lit(n, k, t) : no(n, `${text(n)}: the constant ${n.kind === 'IntegerLiteral' ? n.value : k} is past 2^53 (the rule's numbers stop there)`)
    switch (n.kind) {
      case 'IntegerLiteral': if (safety) return {e: 'lit', ...a, c: {int: n.value!}}; break
      case 'ConstantExpr': if (safety && kids.length === 1) return x(kids[0]!); break
      case 'CXXBoolLiteralExpr': return {e: 'lit', ...a, c: {bool: !!n.value}}
      case 'CXXThisExpr': return {e: 'id', ...a, o: 'var', id: 'this', n: 'this'}
      case 'CXXNullPtrLiteralExpr': return {e: 'id', ...a, o: 'nil'}
      case 'CXXThrowExpr': return {e: 'call', ...a, builtin: 'panic', a: [], what: 'an exception thrown'}
      case 'CXXMemberCallExpr': return memberCall(n)
      case 'CXXOperatorCallExpr': {
        // std::array's [] (its other operators, and every other class's, are other code)
        const o = strip(kids[1] ?? n), ot = o.type ? T(tyOf(o.type)) : undefined
        if (strip(strip(kids[0]!).inner?.[0] ?? kids[0]!).referencedDecl?.name === 'operator[]' && ot?.fixed) return {e: 'index', ...a, x: place(o), i: x(kids[2]!)}
        return no(n, `${text(n)}: an overloaded operator (other code)`)
      }
      case 'DeclRefExpr': {
        const d = n.referencedDecl!
        // (a reference to the caller's struct: the object it points to)
        if (d.kind === 'ParmVarDecl' && structRefs.has(d.id)) return {e: 'star', ...a, x: {e: 'id', ...a, t: byValue.get(d.id)!, o: 'var', id: d.id, n: d.name}}
        if (d.kind === 'ParmVarDecl') { const v: GX = {e: 'id', ...a, ...(boxed.has(d.id) ? {t: boxed.get(d.id)!} : {}), o: 'var', id: d.id, n: d.name}; return refs.has(d.id) ? {e: 'sel', ...a, k: 'field', x: v, path: [0]} : v }
        if (d.kind === 'VarDecl' && /&$/.test(d.type?.qualType ?? '')) return no(n, `${d.name}: a reference held in a local (a second name for a place)`)
        if (d.kind === 'VarDecl' && gfield.has(d.id)) return {e: 'sel', ...a, k: 'field', x: self0(n), path: [gfield.get(d.id)!]}
        if (d.kind === 'VarDecl' && left.has(d.id)) return {e: 'opaque', ...a, why: `${d.name}: left out (leave: an output for other code, never read into the rule)`}
        if (d.kind === 'VarDecl') return globals.has(d.id) ? no(n, `${d.name}: a ${globals.get(d.id)!.storageClass === 'static' ? 'static' : 'global'} variable (state every object shares)`) : {e: 'id', ...a, o: 'var', id: d.id, n: d.name}
        if (d.kind === 'FunctionDecl') return no(n, `${d.name}: a function used as a value`)
        return no(n, `${text(n)}: a ${d.kind}`)
      }
      case 'MemberExpr': {
        const f = fields.get(n.referencedMemberDecl!)
        if (f && !flagRead && !asPlace && T(T(recT(f.rec)).fields![f.i]!.t).nullflag) return no(n, `${text(n)}: a void * read as a pointer (the subset reads one as a flag: set to NULL or not, tested against NULL)`)
        if (!f) return no(n, `${text(n)}: a member that isn't a field of a struct read here`)
        if (records.get(f.rec)!.tagUsed === 'union') return no(n, `${text(n)}: a union's member (one storage read as several types)`)
        const b = kids[0]!
        return {e: 'sel', ...a, k: 'field', x: n.isArrow ? x(b) : place(b), path: [f.i]}
      }
      case 'ImplicitCastExpr': case 'CStyleCastExpr': case 'CXXStaticCastExpr': case 'CXXFunctionalCastExpr': {
        const ck = n.castKind!, inner = kids[0]!
        if (ck === 'IntegralCast') { const it = tyOf(inner.type!); if (T(it).k === 'bool') return {e: 'ite', ...a, x: cond(inner), y: lit(n, 1, t), b: lit(n, 0, t)}; return it === t ? x(inner) : {e: 'call', ...a, conv: true, a: [x(inner)]} }
        if (ck === 'IntegralToBoolean' || ck === 'PointerToBoolean') return cond(n)
        if (ck === 'NullToPointer') return {e: 'id', ...a, o: 'nil'}
        if (ck === 'ToVoid') return x(inner)
        if (ck === 'FunctionToPointerDecay' || ck === 'BuiltinFnToFnPtr') return x(inner)
        if (ck === 'BitCast' && T(t).k === 'ptr' && strip(inner).type && tyOf(strip(inner).type!) === t) return x(inner)
        // (a pointer to the state made a void * or another pointer type, given to other code: still a pointer to the
        // state, which that code may change; anything read through it here is refused)
        if (ck === 'BitCast' && T(t).k === 'ptr' && strip(inner).type && T(tyOf(strip(inner).type!)).k === 'ptr') return x(inner)
        return no(n, `${text(n)}: a ${ck} conversion${ck === 'IntegralToFloating' || ck.includes('Floating') ? ' (floats are outside the subset)' : ck.includes('Pointer') ? ' (a pointer made from other than the state\'s objects)' : ''}`)
      }
      case 'BinaryOperator': {
        const op = n.opcode!, [l, r] = kids as [CN, CN]
        if (CMP.has(op) || op === '&&' || op === '||') { const c = cond(n); return T(t).k === 'bool' ? c : {e: 'ite', ...a, x: c, y: lit(n, 1, t), b: lit(n, 0, t)} }
        if (!safety && op === '&') {
          // u & (2^k − 1): u's low k bits, u % 2^k for an unsigned u.
          const m = fold(r)
          // (of a signed x, two's complement: the floor remainder, ((x % 2^k) + 2^k) % 2^k by C's truncating %)
          if (m !== undefined && m > 0 && Number.isInteger(Math.log2(m + 1))) {
            const k = lit(r, m + 1, t), lo: GX = {e: 'bin', ...a, op: '%', x: x(l), y: k}
            return T(t).signed === false || nonneg(l) ? lo : {e: 'bin', ...a, op: '%', x: {e: 'bin', ...a, op: '+', x: lo, y: k}, y: k}
          }
        }
        if (ARITH.has(op)) return {e: 'bin', ...a, ...checked(n, t, op), op, x: x(l), y: x(r)}
        if (op === ',') return no(n, 'the comma operator')
        if (op === '=') return effect(n, () => x(l))
        return no(n, `${text(n)}: an assignment inside an expression (the subset reads it as a statement)`)
      }
      case 'UnaryOperator': {
        const op = n.opcode!
        if (op === '!') return T(t).k === 'bool' ? cond(n) : {e: 'ite', ...a, x: cond(n), y: lit(n, 1, t), b: lit(n, 0, t)}
        if (op === '-' || op === '+') return {e: 'un', ...a, ...checked(n, t, op === '-' ? '-' : ''), op, x: x(kids[0]!)}
        if (op === '~') return {e: 'un', ...a, op: '^', x: x(kids[0]!)}
        if (op === '&') return {e: 'un', ...a, op: '&', x: place(kids[0]!)}
        if (op === '*') { const r = strip(kids[0]!); return r.kind === 'DeclRefExpr' && boxed.has(r.referencedDecl!.id) ? {e: 'sel', ...a, k: 'field', x: x(r), path: [0]} : {e: 'star', ...a, x: x(kids[0]!)} }
        // (x++ inside an expression: x's value before it, a local; ++x: x after it)
        if (op === '++' || op === '--') {
          if (!n.isPostfix) return effect(n, () => x(kids[0]!))
          const id = `$t${++temps}`, v = x(kids[0]!)
          return effect(n, () => ({e: 'id', ...a, o: 'var', id, n: id}), [{s: 'decl', p: pos(n), specs: [{names: [{name: id, id, t: tyOf(kids[0]!.type!)}], v: [v]}]}])
        }
        return no(n, `${text(n)}: ${op} inside an expression (the subset reads it as a statement)`)
      }
      case 'ConditionalOperator': return {e: 'ite', ...a, x: cond(kids[0]!), y: guard(() => x(kids[1]!)), b: guard(() => x(kids[2]!))}
      case 'CompoundAssignOperator': return effect(n, () => x(kids[0]!))
      case 'CallExpr': return call(n)
      case 'CompoundLiteralExpr': return x(kids[0]!)
      case 'InitListExpr': {
        // A struct's initializer: clang's semantic form lists every field, one not given an implicit zero.
        if (n.array_filler !== undefined) return no(n, `${text(n)}: an array initializer of a ${n.type!.qualType}`)
        const tt = T(t)
        // (a scalar's braces, C++'s {v} and {})
        if ((tt.k === 'int' || tt.k === 'bool') && kids.length <= 1) return kids.length ? x(kids[0]!) : lit(n, 0, t)
        if (tt.k !== 'struct') return no(n, `${text(n)}: an initializer of a ${n.type!.qualType}`)
        return {e: 'comp', ...a, elts: kids.flatMap((k, i) => (k.kind === 'ImplicitValueInitExpr' ? [] : [{field: tt.fields![i]!.name, v: x(k)}]))}
      }
      case 'ArraySubscriptExpr': {
        if (safety) {
          const ct = constTableOf(n)
          if (ct) return {e: 'table', ...a, sites: ct.nodes.map(k => siteOf(k, 'bounds')), dims: ct.dims, vals: ct.vals, indices: ct.idx.map(x)}
        }
        const tb = safety ? undefined : table(n)
        if (tb) return tb
        // An index into an array of the state (its decay to a pointer undone); pointer arithmetic is outside.
        const b = strip(kids[0]!), arr = b.kind === 'ImplicitCastExpr' && b.castKind === 'ArrayToPointerDecay' ? b.inner![0]! : undefined
        return arr ? {e: 'index', ...a, ...(safety ? {site: siteOf(n, 'bounds')} : {}), x: place(arr), i: x(kids[1]!)} : no(n, `${text(n)}: an index into a pointer (pointer arithmetic)`)
      }
      case 'StringLiteral': return no(n, `${text(n)}: a string (char arrays are outside the subset)`)
      case 'FloatingLiteral': return no(n, `${text(n)}: a float (the subset reads integers)`)
      case 'UnaryExprOrTypeTraitExpr': return no(n, `${text(n)}: sizeof (the target's layout)`)
    }
    return no(n, `${text(n)}: an expression the subset doesn't read (${n.kind})`)
  }
  // A place: a local, a field (through a pointer: ->), *p.
  const place = (n0: CN): GX => {
    const n = strip(n0), at0 = (): GX => { const was = placing; placing = true; try { return x(n) } finally { placing = was } }
    if (n.kind === 'DeclRefExpr' || n.kind === 'MemberExpr' || n.kind === 'CXXOperatorCallExpr' || (n.kind === 'UnaryOperator' && n.opcode === '*')) return at0()
    if (n.kind === 'ArraySubscriptExpr') return at0()
    return no(n, `${text(n)}: a place the subset doesn't write`)
  }
  // Other code called with different constants (CO_isError(em, BUS_OFF), CO_isError(em, HB_CONSUMER)): a question per
  // constant arguments, each its own answer, named by them (CO_isError_x_18: x where an argument isn't a constant).
  const asked = new Map<string, Set<string>>()
  const sig = (args: CN[]) => args.map(a => { const k = fold(a); return k === undefined || !Number.isSafeInteger(k) ? 'x' : String(k).replace('-', 'm') }).join('_')
  const scanCalls = (n: CN) => { if (n.kind === 'CallExpr') { const nm = calleeName(n); if (nm && (!funcs.has(nm) || cut.includes(nm))) (asked.get(nm) ?? asked.set(nm, new Set()).get(nm)!).add(sig((n.inner ?? []).slice(1))) } for (const c of n.inner ?? []) scanCalls(c) }
  for (const f of funcs.values()) scanCalls(f)
  const keyed = (name: string, args: CN[]) => ((asked.get(name)?.size ?? 0) > 1 && /\d/.test(sig(args)) ? `${name}_${sig(args)}` : name)
  const call = (n: CN): GX => {
    const t = n.type ? tyOf(n.type) : -1, a = at(n, t), name = calleeName(n), args = (n.inner ?? []).slice(1)
    if (!name) return no(n, `${text(n)}: a call through a function pointer`)
    if (FAIL[name]) return {e: 'call', ...a, builtin: 'panic', a: [], what: FAIL[name]}
    if (name === '__builtin_expect') return x(args[0]!)
    if (name === 'exit' || name === '_Exit') return no(n, `${name}: the process ends`)
    if (cpp && (name === 'min' || name === 'max') && args.length === 2) return {e: 'call', ...a, builtin: name, a: args.map(x)}
    // (one of the file's own the caller answers, `answers`: read as other code's, its value the request's)
    const f = cut.includes(name) ? undefined : funcs.get(name)
    if (f?.$m) return no(n, `${name}: a static method`)
    // (another file's or a library's function: at the boundary where it is inferred, with its end, where the check
    // stubs an answered one in a copy of the file)
    if (!f) return {e: 'call', ...a, f: {e: 'sel', ...at(n, -1), k: 'qual', pkg: '', n: keyed(name, args), why: `${name}: a function of another file or library (other code)`}, a: args.map(x), ...(n.$e && own(n) ? {end: `${n.$e.line}:${n.$e.col + n.$e.tok}`} : {})}
    if (gmode) return {e: 'call', ...a, f: {e: 'sel', ...at(n, -1), k: 'method', x: self0(n), n: name, mtype: entry, mptr: true}, a: args.map(x)}
    if (recvOf(f) && args.length) return {e: 'call', ...a, f: {e: 'sel', ...at(n, -1), k: 'method', x: x(args[0]!), n: name, mtype: entry, mptr: true}, a: args.slice(1).map(x)}
    return {e: 'call', ...a, f: {e: 'id', ...at(n, -1), o: 'func', n: name}, a: args.map(x)}
  }

  // obj.m(...) and this->m(...): a method of the class, inlined with its receiver (a pointer to the object); std::array's
  // size() its length; any other class's method is other code.
  const memberCall = (n: CN): GX => {
    const me = strip(n.inner![0]!), m = members.get(me.referencedMemberDecl ?? ''), b = me.inner?.[0], t = n.type ? tyOf(n.type) : -1
    const bt = b?.type ? T(tyOf(b.type)) : undefined
    if (me.name === 'size' && bt?.fixed) return lit(n, bt.len!, t)
    // (another class's method with no body here: other code at the boundary, as a function of another file, its value
    // the request's where it is read; from where the call begins, so the check stubs the whole call)
    if (b && (!m || m.$rec !== entryRec) && m?.name && (!own(m) || (!(m.inner ?? []).some(c => c.kind === 'CompoundStmt') && !cxx.some(k => k.previousDecl === m.id)))) {
      const p0 = n.$b && own(n) ? `${path.basename(n.$b.file)}:${n.$b.line}:${n.$b.col}` : pos(n)
      return {e: 'call', ...at(n, t), p: p0, f: {e: 'sel', ...at(n, -1), k: 'qual', pkg: '', n: m.name, why: `${text(n)}: a method of another class (other code)`}, a: (n.inner ?? []).slice(1).map(x), ...(n.$e && own(n) ? {end: `${n.$e.line}:${n.$e.col + n.$e.tok}`} : {})}
    }
    if (!m || m.$rec !== entryRec || !b) return no(n, `${text(n)}: a method of another class (other code)`)
    if (overloaded.has(m.name!) || (picks[m.name!] !== undefined && params(m).length !== picks[m.name!])) return no(n, `${m.name}: an overloaded method`)
    if (members.get(me.referencedMemberDecl!)?.virtual || (funcs.get(m.name!) as CN | undefined)?.virtual) return no(n, `${m.name}: a virtual method (its dispatch)`)
    if (!funcs.has(m.name!)) return no(n, `${m.name}: a method with no body here`)
    return {e: 'call', ...at(n, t), f: {e: 'sel', ...at(n, -1), k: 'method', x: me.isArrow ? x(b) : {e: 'un', ...at(b, add(`ptr:${entryT}`, {k: 'ptr', go: `${entry} *`, elem: entryT})), op: '&', x: place(b)}, n: m.name, mtype: entry, mptr: true}, a: (n.inner ?? []).slice(1).map(x)}
  }

  // --- statements -------------------------------------------------------------------------------------------------------
  const topStmts = new Set<string>()
  const sno = (n: CN, why: string): GS[] => [{s: 'no', p: pos(n), why}]
  const conv = (n: CN, to: number, v: GX): GX => ({e: 'call', ...at(n, to), conv: true, a: [v]})
  const ss = (ns: CN[]): GS[] => ns.flatMap(st)
  const block = (n: CN): GS[] => (n.kind === 'CompoundStmt' ? ss(n.inner ?? []) : st(n))
  const ends = (b: GS[]) => { const l = b.at(-1); return !!l && (l.s === 'return' || l.s === 'panic' || (l.s === 'branch' && l.tok === 'break')) }
  function st(n: CN): GS[] {
    const p = pos(n), kids = n.inner ?? []
    // (a write into a global left out: its value computed, the write not kept)
    if ((left.size || leave.length) && (n.kind === 'CompoundAssignOperator' || (n.kind === 'BinaryOperator' && n.opcode === '=') || (n.kind === 'UnaryOperator' && ['++', '--'].includes(n.opcode!))) && leftOut(kids[0]!)) {
      if (n.kind === 'UnaryOperator') return []
      const [ps, v] = pre(() => x(kids[1]!))
      return [...ps, {s: 'expr', p, x: v}]
    }
    switch (n.kind) {
      case 'CompoundStmt': return [{s: 'block', p, b: ss(kids)}]
      case 'NullStmt': return []
      case 'DeclStmt': return kids.flatMap((d): GS[] => {
        if (d.kind !== 'VarDecl') return ['RecordDecl', 'TypedefDecl', 'EnumDecl', 'StaticAssertDecl', 'TypeAliasDecl', 'UsingDecl'].includes(d.kind) ? [] : sno(d, `a ${d.kind} in a function`)
        if (d.storageClass === 'static') return sno(d, `${d.name}: a static local (state every call shares)`)
        // std::lock_guard, std::scoped_lock, std::unique_lock of one of the object's mutexes, in the function's own
        // block: Go's Lock with its deferred Unlock (the step atomic)
        if (/^std::(?:__1::)?(lock_guard|scoped_lock|unique_lock)</.test(d.type!.qualType)) {
          const c = (d.inner ?? []).find(k => k.kind === 'CXXConstructExpr'), mu = c?.inner?.length === 1 ? strip(c.inner[0]!) : undefined
          if (!mu || !topStmts.has(n.id!) || mu.kind !== 'MemberExpr' || !T(tyOf(mu.type!)).mutex) return sno(d, `${d.name}: a lock of other than one mutex of the object, or inside a block (the subset makes the whole step atomic)`)
          const lk = (op: string): GX => ({e: 'call', ...at(d, -1), f: {e: 'sel', ...at(d, -1), k: 'method', x: x(mu), n: op}, a: []})
          return [{s: 'expr', p, x: lk('Lock')}, {s: 'defer', p, x: lk('Unlock')}]
        }
        const init = d.init ? (d.inner ?? []).find(c => !c.kind.endsWith('Attr')) : undefined
        if (!init) return []
        const [ps, v] = pre(() => x(init))
        return [...ps, {s: 'decl', p, specs: [{names: [{name: d.name!, id: d.id!, t: tyOf(d.type!)}], v: [v]}]}]
      })
      case 'ReturnStmt': { if (!kids.length) return [{s: 'return', p, r: []}]; const [ps, v] = pre(() => x(kids[0]!)); return [...ps, {s: 'return', p, r: [v]}] }
      case 'IfStmt': {
        if (n.hasInitStorage || n.hasVarStorage) return sno(n, 'an if with a declaration')
        const [c, th, el] = kids as [CN, CN, CN | undefined]
        const [ps, cc] = pre(() => cond(c))
        return [...ps, {s: 'if', p, c: cc, then: block(th), ...(el ? {else: {s: 'block', p: pos(el), b: block(el)}} : {})}]
      }
      case 'SwitchStmt': return switchC(n)
      case 'BreakStmt': return [{s: 'branch', p, tok: 'break'}]
      case 'ContinueStmt': return sno(n, 'continue (loops are outside the subset)')
      case 'CXXTryStmt': return sno(n, 'try and catch (an exception is the step\'s refusal)')
      case 'ExprWithCleanups': return st(kids[0]!)
      case 'CXXForRangeStmt': return sno(n, 'a loop (for over a range)')
      case 'WhileStmt': case 'DoStmt': case 'ForStmt': {
        // (an endless loop nothing leaves, an assertion's trap or a wait for the watchdog's reset: the code stops there,
        // the step's failure)
        const c0 = n.kind === 'ForStmt' ? (kids[2]?.kind ? kids[2] : undefined) : n.kind === 'DoStmt' ? kids[1] : kids.find(k => k.kind && k.kind !== 'NullStmt' && !k.kind.endsWith('Stmt'))
        const body = n.kind === 'DoStmt' ? kids[0] : kids.at(-1), leaves = (b: CN): boolean => ['BreakStmt', 'ReturnStmt', 'GotoStmt', 'IndirectGotoStmt'].includes(b.kind) || (b.inner ?? []).some(leaves) || (b.kind === 'CallExpr' && !FAIL[calleeName(b) ?? ''])
        const k = c0 && c0.kind !== 'NullStmt' ? fold(c0) : n.kind === 'ForStmt' ? 1 : undefined
        if (k !== undefined && k !== 0 && body && !leaves(body)) return [{s: 'expr', p, x: {e: 'call', ...at(n, -1), builtin: 'panic', a: [], what: 'an endless loop (the code stops there)'}}]
        // (do { ... } while (0), a macro's one statement: its body once, where nothing in it breaks or continues it)
        const exits = (b: CN): boolean => ['BreakStmt', 'ContinueStmt'].includes(b.kind) || (!['WhileStmt', 'DoStmt', 'ForStmt', 'SwitchStmt'].includes(b.kind) && (b.inner ?? []).some(exits))
        if (n.kind === 'DoStmt' && k === 0 && body && !(body.inner ?? []).some(exits)) return block(body)
        return sno(n, `a loop (${n.kind === 'WhileStmt' ? 'while' : n.kind === 'DoStmt' ? 'do' : 'for'})`)
      }
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
        // (a pointer flag set: NULL its false, a constant other than 0 its true)
        if (flagOf(l)) {
          const k = isNull(r) ? 0 : (() => { let v = strip(r); while (CAST.has(v.kind)) v = strip(v.inner![0]!); return fold(v) })()
          if (k === undefined) return sno(n, `${text(n)}: a pointer flag set to other than NULL or a constant`)
          return [{s: 'assign', p, op: '=', l: [place(l)], r: [{e: 'lit', ...at(r, boolT), c: {bool: k !== 0}}]}]
        }
        // a = b = c: b set first, then a to b's value.
        if (rs.kind === 'BinaryOperator' && rs.opcode === '=') return [...st(rs), {s: 'assign', p, op: '=', l: [place(l)], r: [conv2(r, tyOf(l.type!), x(rs.inner![0]!))]}]
        const [ps, rv] = pre(() => x(r))
        return [...ps, {s: 'assign', p, op: '=', l: [place(l)], r: [rv]}]
      }
      case 'CompoundAssignOperator': {
        const [l, r] = kids as [CN, CN], lt = tyOf(l.type!), ct = tyOf(n.computeLHSType!), op = n.opcode!.slice(0, -1)
        if (safety) {
          const result = n.computeResultType as CN['type'], ot = result ? tyOf(result) : refuse(n, 'missing C compound-assignment result type')
          // The validator limits this to scalar places with total, effect-free address computation.
          return [{s: 'assign', p, op: '=', l: [place(l)], r: [conv2(n, lt, {e: 'bin', ...at(n, ot), ...checked(n, ot, op), op, x: conv2(l, ot, x(l)), y: conv2(r, ot, x(r))})]}]
        }
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
        if (safety) {
          const it = tt.bits! >= target.int ? lt : intT('int', target.int, true), op = n.opcode![0]!
          return [{s: 'assign', p, op: '=', l: [place(l)], r: [conv2(n, lt, {e: 'bin', ...at(n, it), ...checked(n, it, op), op, x: conv2(l, it, x(l)), y: lit(n, 1, it)})]}]
        }
        if (tt.bits! >= target.int) return [{s: 'incdec', p, op: n.opcode, x: place(l)}]
        // (a narrow integer is promoted to int, the result converted back)
        const it = intT('int', target.int, true)
        return [{s: 'assign', p, op: '=', l: [place(l)], r: [conv(n, lt, {e: 'bin', ...at(n, it), op: n.opcode![0], x: conv(l, it, x(l)), y: lit(n, 1, it)})]}]
      }
      case 'CallExpr': case 'CXXMemberCallExpr': { const [ps, cx] = pre(() => (n.kind === 'CallExpr' ? call(n) : memberCall(n))); return [...ps, {s: 'expr', p, x: cx}] }
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
        cases.push({p: pos(c), list: [v === undefined ? no(c, 'a case that isn\'t a constant') : !Number.isSafeInteger(v) ? no(c, 'a case past 2^53 (the rule\'s numbers stop there)') : lit(c, v, tt)], b: []})
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
    const [ps, tx] = pre(() => x(tag))
    return [...ps, {s: 'switch', p: pos(n), tag: tx, cases}]
  }

  // --- the functions ----------------------------------------------------------------------------------------------------
  const out: GoFunc[] = [], td0 = () => (gmode ? top.find(n => mine(n)) ?? top[0]! : records.get(entryRec!)!)
  // (the requests: the file's non-static functions, or those named; each given the globals the request gives)
  const requests = new Set(gmode ? (Object.keys(picks).length || pickNames.length ? pickNames : [...funcs].filter(([, f]) => f.storageClass !== 'static' && mine(f)).map(([n]) => n)) : [])
  const fn = (name: string, f: CN, pre0: GS[] = []): GoFunc => {
    // (a request of the file's globals: each global the request gives set from its argument of that name first)
    const gin = gmode && requests.has(name) ? gnodes.filter(g => ginput.has(g.id!) && fnReads.get(name)?.has(g.id!)) : []
    for (const q of params(f)) if (gin.some(g => g.name === q.name)) refuse(q, `${name}: its parameter ${q.name} has a global's name the request gives`)
    const pre = [...pre0, ...gin.map((g): GS => ({s: 'assign', p: pos(f), op: '=', l: [{e: 'sel', ...at(f, tyOf(g.type!)), k: 'field', x: self0(f), path: [gfield.get(g.id!)!]}], r: [{e: 'id', ...at(f, tyOf(g.type!)), o: 'var', id: `in:${g.id}`, n: g.name}]}))]
    const r = recvOf(f), body = f.inner!.find(c => c.kind === 'CompoundStmt')!, rt = f.kind === 'CXXConstructorDecl' ? parseT('void') : parseT(f.type!.qualType.slice(0, retEnd(f.type!.qualType)))
    for (const c of body.inner ?? []) topStmts.add(c.id!)
    return {name, p: pos(f), span: [f.$b?.line ?? 0, f.$e?.line ?? 0],
      ...(r ? {recv: {t: gmode ? ptrT : tyOf(r.type!), ptr: true, type: entry, ...(r.name ? {name: r.name, id: r.id} : {})}} : {}),
      params: [...args0(f).map(q => ({...(q.name ? {name: q.name, id: q.id} : {}), t: boxed.get(q.id!) ?? byValue.get(q.id!) ?? tyOf(q.type!), ts: q.type!.qualType})), ...gin.map(g => ({name: g.name!, id: `in:${g.id}`, t: tyOf(g.type!), ts: g.type!.qualType}))],
      results: T(rt).k === 'void' ? [] : [{t: rt}], body: [...pre, ...ss(body.inner ?? [])],
      ...(/\.\.\.\)$/.test(f.type!.qualType) ? {params: [{t: -1, variadic: true}]} : {}),
      static: f.storageClass === 'static', ...(f.virtual ? {why: `${name}: a virtual method (its dispatch)`} : {})} as GoFunc
  }
  const validated = new Set<string>(), validatedHelpers = new Set<string>()
  const methodSites = new Map<string, SafetySite[]>(), ctorSites: SafetySite[] = []
  // Validate the Clang AST before any lowering can erase a construct. Only pure expressions are admitted;
  // where C does not order operands, at most one may fault. Assignments may have a faulting lvalue OR RHS.
  // Inventory every typed safety site during validation and freeze the inventory before lowering.
  if (safety) {
    function bad(n: CN, why: string): never { return refuse(n, `${why} (outside the C safety subset)`) }
    const stripComments = (s: string) => s.replace(/\/\*[\s\S]*?\*\//g, ' ').replace(/\/\/[^\n]*/g, ' ')
    const hasMacroLoc = (l?: L): boolean => Boolean(l?.expansionLoc || l?.spellingLoc)
    const scalar = (n: CN, t = n.type ? tyOf(n.type) : -1) => {
      const q = T(t), raw = n.type?.desugaredQualType ?? n.type?.qualType ?? ''
      if (/\b(?:volatile|_Atomic|enum)\b/.test(`${n.type?.qualType ?? ''} ${raw}`) || !q || q.nullflag || !(q.k === 'bool' || q.k === 'int' && q.bits! > 0 && q.bits! <= 32)) bad(n, `unmodeled scalar type ${raw}`)
      return q
    }
    const validatePointerTypedef = (aliasId: string, n: CN) => {
      const seen = new Set<string>()
      let cur: string | undefined = aliasId
      while (cur) {
        if (seen.has(cur)) bad(n, 'cyclic typedef in pointer declarator')
        seen.add(cur)
        const td = typedefNode.get(cur)
        if (!td || td.inner?.some(k => k.kind.endsWith('Attr')) || hasMacroLoc(td.loc)) bad(n, 'uninspectable pointer typedef declarator')
        const raw = `${td.type?.qualType ?? ''} ${td.type?.desugaredQualType ?? ''}`
        if (/[[\]()]/.test(raw) || /\b(?:volatile|_Atomic)\b/.test(raw)) bad(n, 'adjusted array or variably-modified pointer typedef')
        cur = td.type?.typeAliasDeclId
      }
    }
    const validateParamDecl = (q: CN, kind: 'receiver' | 'scalar' | 'out') => {
      if (!q.id || !q.name || q.name === '_' || q.inner?.some(k => k.kind.endsWith('Attr'))) bad(q, 'a parameter with unmodeled binding or attributes')
      if (!q.$at || !q.$b || !q.$e || !mine(q) || q.$b.file !== main || q.$e.file !== main) bad(q, 'a parameter without inspectable source range in main file')
      if (hasMacroLoc(q.loc) || hasMacroLoc(q.range?.end)) bad(q, 'a macro-expanded parameter declarator')
      if (hasMacroLoc(q.range?.begin)) {
        const sp = q.range?.begin?.spellingLoc
        const okBool = kind === 'scalar' && q.type?.qualType === 'bool' && !!sp?.file && /(?:^|\/)stdbool\.h$/.test(sp.file)
        if (!okBool) bad(q, 'a macro-expanded parameter declarator')
      }
      if (q.$e.off !== q.$at.off || q.$e.tok !== q.$at.tok) bad(q, 'an adjusted or variably-modified parameter declarator')
      const rawDecl = stripComments(src(main).slice(q.$b.off, q.$e.off + q.$e.tok)).trim()
      if (!rawDecl || /[[\]()]/.test(rawDecl) || /\b(?:volatile|_Atomic)\b/.test(`${rawDecl} ${q.type?.qualType ?? ''} ${q.type?.desugaredQualType ?? ''}`))
        bad(q, 'an adjusted, variably-modified, or qualified parameter declarator')
      if (kind === 'scalar') {
        if (rawDecl.includes('*')) bad(q, 'a pointer declarator for a scalar parameter')
        scalar(q)
      } else {
        const aliasId = q.type?.typeAliasDeclId
        if (aliasId) {
          validatePointerTypedef(aliasId, q)
          if (!/^(?:const\s+)?[A-Za-z_]\w*(?:\s+(?:const|restrict|__restrict))*\s+[A-Za-z_]\w*$/.test(rawDecl))
            bad(q, 'a non-plain pointer-typedef parameter declarator')
        } else if (!/^(?:const\s+)?(?:(?:struct|signed|unsigned|short|long)\s+)*[A-Za-z_]\w*\s*\*\s*(?:(?:const|restrict|__restrict)\s+)*[A-Za-z_]\w*$/.test(rawDecl)) {
          bad(q, 'an adjusted or non-plain pointer parameter declarator')
        }
        if (kind === 'out') {
          const pt = T(tyOf(q.type!))
          if (pt.k !== 'ptr') bad(q, 'an out-parameter that is not a pointer')
          scalar(q, pt.elem!)
        }
      }
    }
    const checkNoRedeclaredGlobal = (g: CN) => {
      if (g.previousDecl || redeclaredGlobals.has(g.id!) || (g.name && (globalByName.get(g.name)?.length ?? 0) > 1))
        bad(g, `global ${g.name ?? ''} has multiple declarations in its linkage chain`)
    }
    const field = (n: CN, receiver: string | undefined) => {
      const f = fields.get(n.referencedMemberDecl ?? ''), b = n.inner?.[0] && strip(n.inner[0])
      if (!f || f.rec !== entryRec || !n.isArrow || b?.kind !== 'DeclRefExpr' || !receiver || b.referencedDecl?.id !== receiver) bad(n, 'a member not directly in the event receiver')
    }
    const isOutDeref = (n: CN, outParams: Set<string>): boolean => {
      if (n.kind !== 'UnaryOperator' || n.opcode !== '*' || !n.inner?.length) return false
      const r = strip(n.inner[0]!)
      return r.kind === 'DeclRefExpr' && !!r.referencedDecl?.id && outParams.has(r.referencedDecl.id)
    }
    const direct = (n: CN, receiver: string | undefined, outParams: Set<string>, allowArray = false, inInit = false) => {
      if (n.kind === 'MemberExpr') field(n, receiver)
      else if (n.kind === 'DeclRefExpr') {
        const d = n.referencedDecl
        if (!d || !['VarDecl', 'ParmVarDecl'].includes(d.kind) || d.id === receiver || outParams.has(d.id) || (globals.has(d.id) && (inInit || !gfield.has(d.id)))) bad(n, 'a reference to an unmodeled declaration')
      } else if (!allowArray && isOutDeref(n, outParams)) {
        // valid direct scalar out-parameter dereference
      } else bad(n, 'an indirect or computed place')
      if (!allowArray) scalar(n)
    }
    const access = (n: CN, receiver: string | undefined, outParams: Set<string>, inInit = false): true => {
      scalar(n)
      const b = strip(n.inner![0]!), arr = b.kind === 'ImplicitCastExpr' && b.castKind === 'ArrayToPointerDecay' && b.inner?.[0]
      if (!arr) return bad(n, 'array access through a pointer or an unknown extent')
      const a = strip(arr)
      direct(a, receiver, outParams, true, inInit)
      const t = T(tyOf(a.type!))
      if (!t.fixed || !Number.isSafeInteger(t.len) || t.len! <= 0) bad(a, 'array without a known positive extent')
      expr(n.inner![1]!, receiver, outParams, inInit)
      siteOf(n, 'bounds')
      return true
    }
    const unordered = (n: CN, a: boolean, b: boolean) => {
      if (a && b) bad(n, 'unspecified order between two potentially faulting operands')
      return a || b
    }
    const safeConstVal = (n0: CN): bigint | undefined => {
      const n = strip(n0)
      if (n.kind === 'ConstantExpr' && n.inner?.length === 1) return safeConstVal(n.inner[0]!)
      if (n.kind === 'IntegerLiteral' && n.value !== undefined && n.type) {
        const t = T(tyOf(n.type))
        if (t.k !== 'int' || !t.bits || t.bits > 32) return undefined
        const v = BigInt(n.value), hi = 2n ** BigInt(t.bits - Number(t.signed)) - 1n
        return v >= 0n && v <= hi ? v : undefined
      }
      if (n.kind === 'UnaryOperator' && (n.opcode === '+' || n.opcode === '-') && n.inner?.length === 1 && n.type) {
        const v = safeConstVal(n.inner[0]!), t = T(tyOf(n.type))
        if (v === undefined || t.k !== 'int' || !t.bits || t.bits > 32) return undefined
        const r = n.opcode === '-' ? -v : v
        if (t.signed) { const lo = -(2n ** BigInt(t.bits - 1)), hi = -lo - 1n; return r >= lo && r <= hi ? r : undefined }
        const m = 2n ** BigInt(t.bits); return ((r % m) + m) % m
      }
      if (n.kind === 'BinaryOperator' && n.inner?.length === 2 && n.type) {
        const a = safeConstVal(n.inner[0]!), b = safeConstVal(n.inner[1]!), t = T(tyOf(n.type))
        if (a === undefined || b === undefined || t.k !== 'int' || !t.bits || t.bits > 32) return undefined
        const lo = t.signed ? -(2n ** BigInt(t.bits - 1)) : 0n, hi = t.signed ? -lo - 1n : (2n ** BigInt(t.bits)) - 1n
        let r: bigint | undefined
        if (n.opcode === '+') r = a + b
        else if (n.opcode === '-') r = a - b
        else if (n.opcode === '*') r = a * b
        else if (n.opcode === '/' || n.opcode === '%') {
          if (b === 0n || (t.signed && a === lo && b === -1n)) return undefined
          r = n.opcode === '/' ? a / b : a % b
        } else return undefined
        if (t.signed) return r >= lo && r <= hi ? r : undefined
        const m = 2n ** BigInt(t.bits); return ((r % m) + m) % m
      }
      return undefined
    }
    const helperInfo = new Map<string, {sites: SafetySite[], canFault: boolean, mutates: boolean}>(), activeCallStack = new Set<string>()
    let activeMutates = false
    const isStatePlace = (n0: CN, outParams: Set<string>): boolean => {
      const n = strip(n0)
      if (n.kind === 'MemberExpr' || n.kind === 'ArraySubscriptExpr') return true
      if (isOutDeref(n, outParams)) return true
      if (n.kind === 'DeclRefExpr' && n.referencedDecl?.id && gfield.has(n.referencedDecl.id)) return true
      return false
    }
    const validateCall = (n: CN, receiver: string | undefined, outParams: Set<string>, inInit: boolean, allowMutate: boolean): boolean => {
      if (inInit) return bad(n, 'a call inside a global initializer')
      const kids = n.inner ?? [], cname = calleeName(n), callee = cname && !FAIL[cname] ? funcs.get(cname) : undefined
      if (!callee || !mine(callee)) return bad(n, `call to ${cname ?? 'indirect function'}`)
      if (activeCallStack.has(cname!)) return bad(n, `recursive call to ${cname}`)
      const callArgs = kids.slice(1), cRecv = recvOf(callee), cParams = args0(callee)
      let argFault = false
      if (!gmode && cRecv) {
        if (callArgs.length !== cParams.length + 1) return bad(n, `arity mismatch calling ${cname}`)
        const r0 = strip(callArgs[0]!)
        if (r0.kind !== 'DeclRefExpr' || !receiver || r0.referencedDecl?.id !== receiver) return bad(n, `helper ${cname} called without the event receiver`)
        for (let i = 0; i < cParams.length; i++) {
          const ca = callArgs[i + 1]!, cp = cParams[i]!
          if (boxed.has(cp.id!)) {
            const ar = strip(ca)
            if (ar.kind !== 'DeclRefExpr' || !ar.referencedDecl?.id || !outParams.has(ar.referencedDecl.id)) return bad(ca, `helper ${cname} out-parameter must forward a direct out-parameter`)
          } else argFault = unordered(n, argFault, expr(ca, receiver, outParams, inInit))
        }
      } else {
        if (callArgs.length !== cParams.length) return bad(n, `arity mismatch calling ${cname}`)
        for (let i = 0; i < cParams.length; i++) {
          const ca = callArgs[i]!, cp = cParams[i]!
          if (boxed.has(cp.id!)) {
            const ar = strip(ca)
            if (ar.kind !== 'DeclRefExpr' || !ar.referencedDecl?.id || !outParams.has(ar.referencedDecl.id)) return bad(ca, `helper ${cname} out-parameter must forward a direct out-parameter`)
          } else argFault = unordered(n, argFault, expr(ca, receiver, outParams, inInit))
        }
      }
      const info = validateFunc(cname!, callee, false)
      if (info.mutates) {
        if (!allowMutate) bad(n, `call to state-mutating helper ${cname} inside an expression`)
        activeMutates = true
      }
      for (const s of info.sites) if (activeSites && !activeSites.includes(s)) activeSites.push(s)
      return argFault || info.canFault
    }
    const expr = (n: CN, receiver?: string, outParams: Set<string> = new Set(), inInit = false): boolean => {
      const kids = n.inner ?? [], [l, r] = kids
      if (n.kind === 'ParenExpr') return expr(l!, receiver, outParams, inInit)
      if (n.kind === 'ConstantExpr' && kids.length === 1) return expr(l!, receiver, outParams, inInit)
      if (CAST.has(n.kind)) {
        if (n.castKind !== 'ToVoid') scalar(n)
        if (!['LValueToRValue', 'NoOp', 'IntegralCast', 'IntegralToBoolean', 'ToVoid'].includes(n.castKind!)) return bad(n, `a ${n.castKind} conversion`)
        return expr(l!, receiver, outParams, inInit)
      }
      const t = scalar(n)
      switch (n.kind) {
        case 'IntegerLiteral': {
          const v = BigInt(n.value!), hi = 2n ** BigInt(t.bits! - Number(t.signed)) - 1n
          if (v < 0 || v > hi) bad(n, 'an integer literal outside its exact Clang type range')
          return false
        }
        case 'DeclRefExpr': case 'MemberExpr': direct(n, receiver, outParams, false, inInit); return false
        case 'ArraySubscriptExpr': {
          const ct = constTableOf(n)
          if (ct) {
            checkNoRedeclaredGlobal(ct.g)
            let anyFault = false
            for (let k = 0; k < ct.idx.length; k++) {
              const f = expr(ct.idx[k]!, receiver, outParams, inInit)
              // Earlier subscript bounds check already may fault; later index expressions are unordered with it.
              if (k > 0) unordered(ct.nodes[k]!, true, f)
              else anyFault = f
              siteOf(ct.nodes[k]!, 'bounds')
            }
            void anyFault
            return true
          }
          return access(n, receiver, outParams, inInit)
        }
        case 'BinaryOperator': {
          const op = n.opcode!, a = expr(l!, receiver, outParams, inInit), b = expr(r!, receiver, outParams, inInit)
          if (op === '&&' || op === '||') return a || b
          const child = unordered(n, a, b)
          if (CMP.has(op)) return child
          if (op === '&') {
            const m = fold(r!)
            if (m === undefined || m <= 0 || m + 1 > 2 ** 31 || !Number.isInteger(Math.log2(m + 1))) bad(n, 'bitwise & with other than a positive power-of-two constant mask')
            return child
          }
          if (['+', '-', '*', '/', '%'].includes(op)) {
            if (op === '/' || op === '%') siteOf(n, 'division')
            else if (t.signed === true) siteOf(n, 'overflow')
            if (!child && safeConstVal(n) !== undefined) return false
            return child || t.signed === true || op === '/' || op === '%'
          }
          return bad(n, `a ${op} expression`)
        }
        case 'UnaryOperator':
          if (n.opcode === '*' && isOutDeref(n, outParams)) return false
          if (['+', '-', '!'].includes(n.opcode!)) {
            const child = expr(l!, receiver, outParams, inInit)
            if (n.opcode === '-' && t.signed === true) siteOf(n, 'overflow')
            return child || (n.opcode === '-' && t.signed === true && strip(l!).kind !== 'IntegerLiteral')
          }
          return bad(n, `a ${n.opcode} expression`)
        case 'ConditionalOperator': return kids.map(k => expr(k, receiver, outParams, inInit)).some(Boolean)
        case 'InitListExpr': if (n.array_filler === undefined && kids.length <= 1) return !!l && expr(l, receiver, outParams, inInit); break
        case 'CallExpr': return validateCall(n, receiver, outParams, inInit, false)
      }
      return bad(n, n.kind)
    }
    const placeFault = (n: CN, receiver: string | undefined, outParams: Set<string>) => {
      const v = strip(n)
      if (isStatePlace(v, outParams)) activeMutates = true
      if (v.kind === 'ArraySubscriptExpr') return access(v, receiver, outParams)
      direct(v, receiver, outParams)
      return false
    }
    const stmt = (n: CN, receiver: string | undefined, outParams: Set<string>): boolean => {
      const kids = n.inner ?? [], [l, r] = kids
      switch (n.kind) {
        case 'CompoundStmt': return kids.map(k => stmt(k, receiver, outParams)).some(Boolean)
        case 'NullStmt': return false
        case 'ParenExpr': return stmt(l!, receiver, outParams)
        case 'CallExpr': return validateCall(n, receiver, outParams, false, true)
        case 'WhileStmt': case 'ForStmt': case 'DoStmt': return bad(n, 'a loop (while/for/do)')
        case 'SwitchStmt': case 'GotoStmt': case 'BreakStmt': case 'ContinueStmt': case 'LabelStmt': return bad(n, `a ${n.kind} statement`)
        case 'ReturnStmt': return kids.map(k => expr(k, receiver, outParams)).some(Boolean)
        case 'IfStmt': {
          if (n.hasInitStorage || n.hasVarStorage || (kids.length !== 2 && kids.length !== 3)) return bad(n, 'an if with extra context')
          const c = expr(l!, receiver, outParams), arms = kids.slice(1).map(k => stmt(k, receiver, outParams)).some(Boolean)
          return c || arms
        }
        case 'DeclStmt': {
          let f = false
          for (const d of kids) {
            if (d.kind !== 'VarDecl' || d.name === '_' || (d.storageClass && d.storageClass !== 'auto' && d.storageClass !== 'register') || !d.init || d.inner?.length !== 1) return bad(d, 'a local without a modeled automatic scalar initializer')
            scalar(d); if (expr(d.inner[0]!, receiver, outParams)) f = true
          }
          return f
        }
        case 'BinaryOperator':
          if (n.opcode === '=') return unordered(n, placeFault(l!, receiver, outParams), expr(r!, receiver, outParams))
          if (n.opcode === ',') return kids.map(k => stmt(k, receiver, outParams)).some(Boolean)
          break
        case 'CompoundAssignOperator': {
          if (!['+=', '-=', '*=', '/=', '%='].includes(n.opcode!) || placeFault(l!, receiver, outParams)) return bad(n, 'a compound assignment to other than a direct scalar place or an unsupported operator')
          const op = n.opcode!.slice(0, -1), rf = expr(r!, receiver, outParams)
          const result = n.computeResultType, ot = result ? tyOf(result) : bad(n, 'missing C compound-assignment result type')
          if (op === '/' || op === '%') { siteOf(n, 'division'); return true }
          if (T(ot).signed === true) { siteOf(n, 'overflow'); return true }
          return rf
        }
        case 'UnaryOperator':
          if (['++', '--'].includes(n.opcode!)) {
            if (placeFault(l!, receiver, outParams)) return bad(n, 'increment/decrement of other than a direct scalar place')
            const lt = tyOf(l!.type!), tt = scalar(l!, lt)
            if (tt.k !== 'int') return bad(n, 'increment/decrement of a non-integer place')
            const it = tt.bits! >= target.int ? lt : intT('int', target.int, true)
            if (T(it).signed === true) { siteOf(n, 'overflow'); return true }
            return false
          }
          break
      }
      return expr(n, receiver, outParams)
    }
    const validateFunc = (name: string, f: CN, isEntry: boolean): {sites: SafetySite[], canFault: boolean, mutates: boolean} => {
      const cached = helperInfo.get(name)
      if (cached) { if (isEntry) validated.add(name); else validatedHelpers.add(name); return cached }
      if (!mine(f) || f.variadic || f.inner?.some(k => k.kind.endsWith('Attr')) || hasMacroLoc(f.loc)) bad(f, 'a definition outside the main file, or an attributed, macro-spelled, or variadic function')
      const recv = recvOf(f)
      if (!gmode && recv) validateParamDecl(recv, 'receiver')
      else if (!gmode && isEntry) bad(f, 'an entry method without a receiver')
      const ret = parseT(f.type!.qualType.slice(0, retEnd(f.type!.qualType)))
      if (T(ret).k !== 'void') scalar(f, ret)
      const outParams = new Set<string>()
      for (const q of args0(f)) {
        if (boxed.has(q.id!)) { validateParamDecl(q, 'out'); outParams.add(q.id!) }
        else validateParamDecl(q, 'scalar')
      }
      const prevSites = activeSites, prevMutates = activeMutates, fnSites: SafetySite[] = []
      activeSites = fnSites
      activeMutates = false
      activeCallStack.add(name)
      let canFault = false, mutates = false
      try {
        canFault = stmt(f.inner!.find(c => c.kind === 'CompoundStmt')!, gmode ? undefined : recv?.id, outParams)
        mutates = activeMutates
      } finally {
        activeCallStack.delete(name)
        activeSites = prevSites
        activeMutates = prevMutates
      }
      const info = {sites: fnSites, canFault, mutates}
      helperInfo.set(name, info)
      methodSites.set(name, fnSites)
      if (isEntry) validated.add(name)
      else validatedHelpers.add(name)
      return info
    }
    const state = (d: CN) => {
      const q = T(tyOf(d.type!)), raw = `${d.type!.qualType} ${d.type!.desugaredQualType ?? ''}`
      if (/\b(?:volatile|_Atomic)\b/.test(raw) || d.isBitfield || !d.name || d.inner?.some(k => k.kind.endsWith('Attr'))) bad(d, 'state with unmodeled qualifiers, attributes or layout')
      if (q.k === 'array' && q.fixed) {
        if (!Number.isSafeInteger(q.len) || q.len! <= 0 || d.init) bad(d, 'an array without a modeled fixed zero start')
        scalar(d, q.elem)
      } else scalar(d)
    }
    if (entryRec) {
      const rec = records.get(entryRec)!
      if (rec.tagUsed !== 'struct' || rec.inner?.some(k => k.kind.endsWith('Attr'))) bad(rec, 'an entry other than a plain struct')
      for (const f of rec.inner ?? []) if (f.kind === 'FieldDecl') state(f)
    }
    activeSites = ctorSites
    for (const g of gnodes) {
      checkNoRedeclaredGlobal(g)
      state(g)
      if (g.storageClass !== 'static' || g.tls || !mine(g)) bad(g, 'state not defined as file-local in this translation unit')
      if (g.init) {
        if (g.inner?.length !== 1) bad(g, 'global initializer with unexpected structure')
        expr(g.inner[0]!, undefined, new Set(), true)
      }
    }
    activeSites = undefined
    for (const [name, f] of funcs) {
      if (gmode ? !requests.has(name) : !recvOf(f) || (pickNames.length ? !pickNames.includes(name) : !mine(f) || f.storageClass === 'static')) continue
      validateFunc(name, f, true)
    }
    if (pickNames.length) {
      for (const want of pickNames) if (!validated.has(want)) bad(td0(), `selected method ${want} is missing or lacks a modeled receiver`)
    }
    // Closed-TU function coverage & symbol/preprocessor audit:
    // - System headers are classified strictly by resolved path under Clang's built-in or -isystem
    //   search directories (never linemarker flag 3); every non-system file in the TU (including
    //   headers under root, relative ../, or -I) is audited identically to own code.
    // - Every non-system function body must be a selected validated method or an inlined
    //   file-local static helper; any other body (even static, inline, or __-prefixed) is refused
    //   and named.
    // - Symbol export/alias/attribute escapes (__attribute__((alias/weak/constructor/destructor)),
    //   #pragma weak, _Pragma("weak ..."), file-scope __asm__, post-definition redeclarations),
    //   system_header pragmas and #line/linemarker directives in all spellings (#, %:, ??=, _Pragma),
    //   global initializers referencing functions in any non-system file, pointer/fn-ptr struct
    //   fields in globals, and user-code build-mode divergence (checked in clangDump) are refused.
    const meta = target.safetyMeta
    const systemFiles = meta?.systemFiles
    const userFiles = meta?.userFiles ?? new Set<string>([mainReal])
    const isSystemFile = (f?: string): boolean => {
      if (!f) return false
      if (f === '<built-in>') return true
      if (f === '<command line>') return false
      const rp = realPath(f)
      if (userFiles.has(rp) || rp === mainReal) return false
      if (systemFiles) return systemFiles.has(rp)
      return !own({$at: {file: f, line: 0, col: 0, off: 0, tok: 0}} as CN)
    }
    // A node is system ONLY if BOTH its expansion location AND every spelling/expansion file in
    // its loc/range chain are system files (never trusting expansionLoc alone when a user or -D
    // macro is expanded inside a system header).
    const isSystemNode = (n: CN): boolean => {
      if (!isSystemFile(n.$at?.file)) return false
      if (n.$files) {
        for (const f of n.$files) if (!isSystemFile(f)) return false
      }
      return true
    }
    // Whole-class refusal: refuse any user-defined (or -D command-line) macro expanded inside a
    // system header anywhere in the TU (prevents hiding functions, attributes, aliases, or globals
    // inside system header locations via macro hijacking such as `#define ptrdiff_t ...`).
    const auditMacroExpansions = (n: CN): void => {
      for (const {spell, spellLine, expand, expandLine} of n.$macroExpansions ?? []) {
        if (expand !== '<built-in>' && isSystemFile(expand) && !isSystemFile(spell)) {
          const where = spell === '<command line>' ? '<command line>' : `${path.basename(spell)}:${spellLine}:1`
          throw new Refusal(where, `user-defined macro expanded inside system header ${path.basename(expand)}:${expandLine} is outside the C safety subset`)
        }
      }
      for (const c of n.inner ?? []) auditMacroExpansions(c)
    }
    auditMacroExpansions(tu)
    // Strip C comments (and optionally string/char literals) while preserving line numbers so
    // directive and _Pragma scans over user files never match inside comments or literals.
    const stripForPreproc = (raw: string, keepStrings = false): string => {
      let out = ''
      const isIdent = (c: string | undefined) => !!c && /[A-Za-z0-9_$]/.test(c)
      const isDigit = (c: string | undefined) => !!c && c >= '0' && c <= '9'
      for (let i = 0; i < raw.length; i++) {
        const ch = raw[i]!
        if ((isDigit(ch) && !isIdent(raw[i - 1])) || (ch === '.' && isDigit(raw[i + 1]))) {
          let j = i + (ch === '.' ? 2 : 1)
          while (j < raw.length) {
            const c = raw[j]!
            if ((c === 'e' || c === 'E' || c === 'p' || c === 'P') && (raw[j + 1] === '+' || raw[j + 1] === '-')) { j += 2; continue }
            if (c === "'" && /[0-9A-Za-z_]/.test(raw[j + 1] ?? '')) { j += 2; continue }
            if (/[0-9A-Za-z_.]/.test(c)) { j++; continue }
            break
          }
          out += raw.slice(i, j)
          i = j - 1
        } else if (ch === '"' || ch === "'") {
          const q = ch
          out += keepStrings ? q : ' '
          for (i++; i < raw.length; i++) {
            const c = raw[i]!
            if (c === '\\') {
              out += keepStrings ? '\\' : ' '
              i++
              if (i < raw.length) out += keepStrings ? raw[i]! : (raw[i] === '\n' ? '\n' : ' ')
              continue
            }
            if (c === '\n') { out += '\n'; break }
            out += keepStrings ? c : ' '
            if (c === q) break
          }
        } else if (ch === '/' && raw[i + 1] === '/') {
          out += '  '
          for (i += 2; i < raw.length; i++) {
            if (raw[i] === '\\' && (raw[i + 1] === '\n' || (raw[i + 1] === '\r' && raw[i + 2] === '\n'))) {
              out += raw[i + 1] === '\r' ? ' \n' : '\n'
              i += raw[i + 1] === '\r' ? 2 : 1
              continue
            }
            if (raw[i] === '\n') { out += '\n'; break }
            out += ' '
          }
        } else if (ch === '/' && raw[i + 1] === '*') {
          out += '  '
          for (i += 2; i < raw.length; i++) {
            if (raw[i] === '*' && raw[i + 1] === '/') { out += '  '; i++; break }
            out += raw[i] === '\n' ? '\n' : ' '
          }
        } else {
          out += ch
        }
      }
      return out
    }
    const FORBIDDEN_OP_PRAGMA_RE = /\b_Pragma\s*\(\s*(?:L|u8|u|U)?\s*"(?:[^"\\]|\\.)*(?:system_header|\bweak\b|\bredefine_extname\b)(?:[^"\\]|\\.)*"\s*\)/
    for (const uf of userFiles) {
      const rawSrc = src(uf).replace(/\?\?\//g, '\\')
      const noComments = stripForPreproc(rawSrc, true)
      const opHit = FORBIDDEN_OP_PRAGMA_RE.exec(noComments)
      if (opHit) {
        const lineNo = noComments.slice(0, opHit.index).split('\n').length
        throw new Refusal(`${path.basename(uf)}:${lineNo}:1`, `_Pragma(${opHit[0].includes('system_header') ? 'GCC system_header' : 'weak/redefine_extname'}) is outside the C safety subset`)
      }
      const cleaned = stripForPreproc(rawSrc, false).split('\n')
      for (let idx = 0; idx < cleaned.length; idx++) {
        let line = cleaned[idx]!.replace(/\r$/, '')
        const startLine = idx + 1
        while (line.endsWith('\\') && idx + 1 < cleaned.length) {
          line = line.slice(0, -1) + cleaned[++idx]!.replace(/\r$/, '')
        }
        const trimmed = line.trimStart()
        const prefixLen = trimmed.startsWith('#') ? 1 : trimmed.startsWith('%:') ? 2 : trimmed.startsWith('??=') ? 3 : 0
        if (!prefixLen) continue
        const body = trimmed.slice(prefixLen).trimStart()
        const where = `${path.basename(uf)}:${startLine}:1`
        if (/^(?:line\b|\d+(?:\s|$))/.test(body))
          throw new Refusal(where, '#line or linemarker directive is outside the C safety subset')
        if (/^pragma\s+(?:(?:GCC|clang)\s+)?system_header\b/.test(body))
          throw new Refusal(where, '#pragma GCC/clang system_header in user file is outside the C safety subset')
        if (/^pragma\s+(?:weak|redefine_extname)\b/.test(body))
          throw new Refusal(where, '#pragma weak/redefine_extname symbol alias is outside the C safety subset')
      }
    }
    const hasUnsafePtrType = (raw: string): boolean => /\bvoid\s*\*|\(\s*\*|\*\s*\*/.test(raw)
    const typeIdxMentionsEntry = (start: number): boolean => {
      if (!entryRec || start < 0) return false
      const seen = new Set<number>()
      const check = (idx: number): boolean => {
        if (seen.has(idx)) return false
        seen.add(idx)
        if (idx === entryT) return true
        const q = T(idx)
        if (!q) return false
        if (q.elem !== undefined && check(q.elem)) return true
        if (q.fields?.some(fl => check(fl.t))) return true
        return false
      }
      return check(start)
    }
    const typeIdxHasPtrOrFunc = (start: number): boolean => {
      if (start < 0) return false
      const seen = new Set<number>()
      const check = (idx: number): boolean => {
        if (seen.has(idx)) return false
        seen.add(idx)
        const q = T(idx)
        if (!q) return false
        if (q.k === 'ptr' || q.k === 'func' || q.k === 'ref' || q.k === 'opaque' || q.k === 'union' || q.nullflag) return true
        if (q.elem !== undefined && check(q.elem)) return true
        if (q.fields?.some(fl => check(fl.t))) return true
        return false
      }
      return check(start)
    }
    const typeMentionsEntry = (ty?: {qualType: string, desugaredQualType?: string}): boolean =>
      !!entryRec && !!ty && typeIdxMentionsEntry(tyOf(ty))
    const uncheckedFns: {name: string, node: CN}[] = []
    for (const [name, f] of funcs) {
      if (validated.has(name)) continue
      if (f.storageClass === 'static' && validatedHelpers.has(name)) continue
      uncheckedFns.push({name, node: f})
    }
    for (const n of top) {
      if (n.kind === 'FunctionDecl' && !n.isImplicit && !own(n) && n.inner?.some(c => c.kind === 'CompoundStmt')) {
        if (!isSystemNode(n)) uncheckedFns.push({name: n.name ?? '<anonymous>', node: n})
      }
    }
    if (uncheckedFns.length) {
      const names = uncheckedFns.map(u => u.name)
      const covered = [...validated]
      throw new SafetyUncoveredRefusal(
        pos(uncheckedFns[0]!.node),
        `unchecked function${names.length === 1 ? '' : 's'} in translation unit: ${names.join(', ')} (every function with a body must be covered by C safety; covered: ${covered.length ? covered.join(', ') : 'none'})`,
        covered,
        names,
        meta?.macroConfig,
      )
    }
    // Reject file-scope asm, attributed/aliased/weak/constructor/destructor/post-definition
    // function declarations, bodyless external prototypes that could write state, non-system
    // globals with attributes/extern/pointers/fn-ptrs (including inside struct/array fields) or
    // function-referencing initializers, and system-header declarations referencing modeled state.
    const scanForeignStateAccess = (n: CN, fnName: string): void => {
      if (n.kind === 'MemberExpr' && entryRec && fields.get(n.referencedMemberDecl ?? '')?.rec === entryRec)
        bad(n, `external header function ${fnName} accesses entry struct ${entry}`)
      if (n.kind === 'DeclRefExpr' && n.referencedDecl?.kind === 'VarDecl' && gfield.has(n.referencedDecl.id))
        bad(n, `external header function ${fnName} accesses modeled global state`)
      if ((n.kind === 'ParmVarDecl' || n.kind === 'VarDecl') && typeMentionsEntry(n.type))
        bad(n, `external header function ${fnName} references entry struct ${entry}`)
      for (const c of n.inner ?? []) scanForeignStateAccess(c, fnName)
    }
    const definedFns = new Set<string>()
    for (const n of top) {
      if (n.kind === 'FileScopeAsmDecl')
        bad(n, 'file-scope inline assembly is outside the closed translation unit')
      if (n.kind === 'FunctionDecl' && !n.isImplicit) {
        const hasBody = !!n.inner?.some(c => c.kind === 'CompoundStmt')
        const nonSys = !isSystemNode(n)
        const fnName = n.name ?? '<anonymous>'
        if (nonSys) {
          if (n.inner?.some(c => c.kind.endsWith('Attr')))
            bad(n, `attributed function declaration ${fnName} (alias/weak/constructor/destructor) is outside the closed translation unit`)
          if (!hasBody && n.name && definedFns.has(n.name))
            bad(n, `post-definition redeclaration of function ${fnName} is outside the closed translation unit`)
        }
        if (hasBody && n.name) definedFns.add(n.name)
        if (!hasBody && !(n.name && funcs.has(n.name))) {
          const ps = params(n)
          const qt = n.type?.qualType ?? ''
          const retIdx = qt ? parseT(qt.slice(0, retEnd(qt))) : -1
          if (typeIdxMentionsEntry(retIdx) || ps.some(q => typeMentionsEntry(q.type)))
            bad(n, `external function prototype ${fnName} references entry struct ${entry} with no body in this translation unit`)
          if (nonSys) {
            if (n.variadic || (ps.length === 0 && /\(\s*\)$/.test(qt)))
              bad(n, `external function prototype ${fnName} has no body and an unclosed parameter list`)
            if (retIdx >= 0 && !['void', 'bool', 'int'].includes(T(retIdx).k))
              bad(n, `external function prototype ${fnName} returns non-scalar type ${T(retIdx).go ?? T(retIdx).k} with no body in this translation unit`)
            for (const q of ps) {
              const raw = `${q.type?.qualType ?? ''} ${q.type?.desugaredQualType ?? ''}`
              const pt = q.type ? T(tyOf(q.type)) : undefined
              if (hasUnsafePtrType(raw) || !pt || !['int', 'bool'].includes(pt.k))
                bad(q, `external function prototype ${fnName} takes pointer or non-scalar parameter ${q.name ?? ''} with no body in this translation unit`)
            }
          }
        } else if (hasBody && !own(n)) {
          scanForeignStateAccess(n, fnName)
        }
      }
      if (n.kind === 'VarDecl' && !n.isImplicit) {
        if (!isSystemNode(n)) {
          if (!gfield.has(n.id!)) {
            const raw = `${n.type?.qualType ?? ''} ${n.type?.desugaredQualType ?? ''}`
            if (n.inner?.some(c => c.kind.endsWith('Attr')))
              bad(n, `attributed global ${n.name ?? ''} is outside the closed translation unit`)
            if (n.storageClass === 'extern')
              bad(n, `extern global ${n.name ?? ''} is outside the closed translation unit`)
            if (typeMentionsEntry(n.type))
              bad(n, `global ${n.name ?? ''} references entry struct ${entry}`)
            if (hasUnsafePtrType(raw) || (n.type && typeIdxHasPtrOrFunc(tyOf(n.type))))
              bad(n, `pointer, function-pointer, or unmodeled aggregate global ${n.name ?? ''} is outside the closed translation unit`)
          }
          if (n.init) {
            const scanInit = (c: CN): void => {
              if (c.kind === 'DeclRefExpr' && c.referencedDecl?.kind === 'FunctionDecl')
                bad(c, `global ${n.name ?? ''} initializer references function ${c.referencedDecl.name}`)
              for (const k of c.inner ?? []) scanInit(k)
            }
            scanInit(n)
          }
        } else if (typeMentionsEntry(n.type)) {
          bad(n, `external header global ${n.name ?? ''} references entry struct ${entry}`)
        }
      }
    }
    sitesFrozen = true
  }
  let ctor: GoFunc | undefined
  for (const [name, f] of funcs) if (!safety || validated.has(name) || validatedHelpers.has(name)) {
    const gf = fn(name, f)
    if (safety) gf.safetySites = methodSites.get(name) ?? []
    out.push(gf)
  }
  // (the globals' start: each one's initializer, where it has one; C's zero where not)
  if (gmode) {
    const pre: GS[] = []
    for (const g of gnodes) {
      const v = g.init ? (g.inner ?? []).find(c => !c.kind.endsWith('Attr')) : undefined, t = tyOf(g.type!)
      const empty = !v || isAllZeroInit(v)
      // (C's zero, leaf by leaf: each integer and boolean of it 0, an array a list of zeros already)
      const zeros = (tt: number, place: GX) => {
        const k = T(tt).k
        if (k === 'int' || k === 'bool') pre.push({s: 'assign', p: pos(g), op: '=', l: [place], r: [k === 'int' ? lit(g, 0, tt) : {e: 'lit', ...at(g, tt), c: {bool: false}}]})
        else if (k === 'struct') T(tt).fields!.forEach((f, i) => zeros(f.t, {e: 'sel', ...at(g, f.t), k: 'field', x: place, path: [i]}))
      }
      const place: GX = {e: 'sel', ...at(v ?? g, t), k: 'field', x: self0(v ?? g), path: [gfield.get(g.id!)!]}
      if (empty) zeros(t, place)
      else pre.push({s: 'assign', p: pos(v!), op: '=', l: [place], r: [x(v!)]})
    }
    ctor = {name: '$ctor', p: pos(td0()), span: [0, 0], recv: {t: ptrT, ptr: true, type: entry, name: 'this', id: 'this'}, params: [], results: [], body: pre, ...(safety ? {safetySites: ctorSites} : {})} as GoFunc
  }
  // The constructor (C++): its member initializers (each field's own in-class one where it has no other), then its body;
  // the rule starts where it leaves the object, its parameters the rule's.
  if (cpp) {
    if (ctors.length > 1) refuse(ctors[1], `${entry}: ${ctors.length} constructors (the C++ front end reads a class with one)`)
    const c = ctors[0], inits = new Map<string, CN>()
    for (const f of fieldNode.values()) if (fields.get(f.id!)!.rec === entryRec && f.inner?.length && !f.inner[0]!.kind.endsWith('Attr')) inits.set(f.id!, f.inner[0]!)
    for (const k of c?.inner ?? []) if (k.kind === 'CXXCtorInitializer') { const d = k.anyInit as {id: string} | undefined; if (d && k.inner?.length) inits.set(d.id, fillDefault(k.inner[0]!, fieldNode.get(d.id))) }
    const pre: GS[] = []
    for (const [id, v0] of inits) {
      const f = fieldNode.get(id)!, ft = T(tyOf(f.type!)), v = strip(v0)
      if (ft.mutex || (v.kind === 'InitListExpr' && isAllZeroInit(v))) continue
      if (v.kind === 'CXXConstructExpr' && !v.inner?.length) continue
      pre.push({s: 'assign', p: pos(v0), op: '=', l: [{e: 'sel', ...at(v0, tyOf(f.type!)), k: 'field', x: {e: 'id', ...at(v0, add(`ptr:${entryT}`, {k: 'ptr', go: `${entry} *`, elem: entryT})), o: 'var', id: 'this', n: 'this'}, path: [fields.get(id)!.i]}], r: [x(v)]})
    }
    ctor = c ? fn('$ctor', Object.assign(c, {$m: true}), pre) : {name: '$ctor', p: pos(td0()), span: [0, 0], recv: {t: add(`ptr:${entryT}`, {k: 'ptr', go: `${entry} *`, elem: entryT}), ptr: true, type: entry, name: 'this', id: 'this'}, params: [], results: [], body: pre} as GoFunc
  }
  const td = td0()
  const pkg: GoPkg = {lang: cpp ? 'cpp' : 'c', ...(safety ? {safety: true as const} : {}), package: entry, files: [{name: base, imports: []}], funcs: out, types: [{name: entry, t: entryT, p: pos(td), span: [td.$b?.line ?? 0, td.$e?.line ?? 0]}], consts: [], vars: [], errors: [], ttab, ...(ctor ? {ctor} : {})}
  // (by default: the file's non-static functions taking the struct; a class's public methods)
  const methods = safety ? [...validated] : gmode ? [...requests] : out.filter((f, i) => { const n = [...funcs.values()][i]!; return f.recv && !(f as {static?: boolean}).static && (n.$m ? n.$access === 'public' : mine(n)) }).map(f => f.name)
  // (the class's qualified name, which the harness spells: `this`'s type, as clang prints it)
  const thisOf = (n: CN): string | undefined => (n.kind === 'CXXThisExpr' ? n.type!.qualType : (n.inner ?? []).map(thisOf).find(Boolean))
  const self = cpp ? cxx.filter(m => m.$rec === entryRec).map(thisOf).find(Boolean)?.replace(/^const /, '').replace(/ \*$/, '') : undefined
  return {pkg, methods, ...(safety && validatedHelpers.size ? {helpers: [...validatedHelpers]} : {}), ...(safety && target.safetyMeta ? {macroConfig: target.safetyMeta.macroConfig} : {}), entry, cname: self ?? T(entryT).go!, consts: Object.fromEntries([...named].filter(([, v]) => Number.isSafeInteger(v))),
    ...(gmode ? {globals: {state: gnodes.map(g => g.name!), inputs: gnodes.filter(g => ginput.has(g.id!)).map(g => g.name!), types: Object.fromEntries(gnodes.map(g => [g.name!, g.type!.qualType])),
      // (declared only, another file's to define: the check defines it, zero at the start)
      externs: gnodes.filter(g => ![...globals.values()].some(d => d.name === g.name && (d.storageClass !== 'extern' || d.init))).map(g => g.name!)}} : {})}
}
// Where a function type's result ends: before its parameter list (the last parenthesized group).
function retEnd(s: string): number {
  let d = 0
  for (let i = s.length - 1; i >= 0; i--) { if (s[i] === ')') d++; else if (s[i] === '(' && --d === 0) return i }
  return s.length
}
