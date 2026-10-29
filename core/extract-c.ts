// The extractor's C front end (`gdp-wired/extract-c`): a struct of a C file and the functions that take it by pointer,
// read through clang (core/c/reader.ts: its JSON dump, with the project's flags or its compile_commands.json), put in
// the typed shape Go's reader prints and lowered by Go's lowering into the shared step IR (core/extract-go.ts, then
// core/extract-step.ts): one lowering for both, C's semantics written as explicit nodes where clang's types say so.
// The check compiles the file as it ships with a generated harness (it #includes the file, so its static functions are
// called as they are, with the same flags and the undefined-behavior sanitizer trapping), drives the functions with
// the rule's requests and compares every state (core/extract-go-check.ts's `speak`, Go's own driver).
//
//   const x = extractC('src/bucket.c', {entry: 'bucket', fails: {bucket_take: '< 0'}, flags: ['-Iinclude']})
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
import {Refusal} from './extract-read.ts'
import type {Rule} from './dsl.ts'
import type {Sorts} from './extract-print.ts'
import type {Coverage} from './extract-check.ts'
import {type GoOptions, type GoPkg, type GoRead, readGo, unsignedDomains} from './extract-go.ts'
import {type GoCheckOptions, type GoEvidence, type GoLeaf, speak} from './extract-go-check.ts'
import {type CRead, clangDump, flagsFor, node, readC} from './c/reader.ts'

export type COptions = {
  // The struct, and the functions read as its requests (by default each non-static one whose first parameter points to it).
  entry: string, functions?: string[],
  // The project's flags (-I, -D, -std), or its compile_commands.json (the file's entry's), and the clang to run.
  flags?: string[], compileCommands?: string, clang?: string,
  // The project's own files (their functions are read too: a header's static inline ones); by default the file's directory.
  root?: string,
  // A function's result that is its failure where it compares so: {take: '< 0'} (the step's refusal there).
  fails?: Record<string, string>,
  onError?: 'refuse' | 'discard', domains?: Record<string, 'nat' | 'int'>, check?: GoCheckOptions,
}
type FS = {mkdtempSync: (p: string) => string, writeFileSync: (p: string, s: string) => void, rmSync: (p: string, o?: unknown) => void, mkdirSync: (p: string, o?: unknown) => void}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}

export function readCFile(file: string, opts: COptions, cpp = false): {c: CRead, flags: string[]} {
  const flags = [...flagsFor(file, opts.compileCommands), ...(opts.flags ?? [])], {tu, target} = clangDump(file, flags, opts.clang, cpp)
  return {c: readC(file, opts.entry, tu, target, cpp, opts.root), flags}
}
export function extractC(file: string, opts: COptions, cpp = false): Extraction & {leaves?: GoLeaf[]} {
  const notes: string[] = []
  let read: GoRead, c: CRead, flags: string[]
  try {
    ;({c, flags} = readCFile(file, opts, cpp))
    read = readGo(c.pkg, {entry: opts.entry, methods: opts.functions ?? c.methods, ...(opts.onError ? {onError: opts.onError} : {}), ...(opts.fails ? {fails: opts.fails} : {})} as GoOptions)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  const x = fromModel(read.model, `${opts.entry}.${cpp ? 'cpp' : 'c'}`, {...unsignedDomains(read), ...signedDomains(c.pkg, read), ...opts.domains}, notes, (rule, sorts) => checkC(file, flags, c, read, rule, sorts, opts, cpp))
  return {...x, leaves: read.leaves}
}

// A signed field (and a signed result) is an integer, never inferred a natural: its range law reads below 0.
function signedDomains(pkg: GoPkg, read: GoRead): Record<string, 'int'> {
  const out: Record<string, 'int'> = {}
  for (const l of read.leaves) if (l.kind === 'int' && ty(pkg, l.t).signed !== false) out[l.name] = 'int'
  for (const l of read.leaves) if (l.kind === 'list' && ty(pkg, ty(pkg, l.t).elem!).k === 'int' && ty(pkg, ty(pkg, l.t).elem!).signed !== false) out[`${l.name}.$item`] = 'int'
  for (const m of read.methods) if (m.results[0] !== undefined && ty(pkg, m.results[0]).k === 'int' && ty(pkg, m.results[0]).signed !== false) out[`${m.name}_result`] = 'int'
  return out
}

// --- the harness: C (or C++) that #includes the file, sets and prints the state's leaves as JSON lines -------------------
const ty = (pkg: GoPkg, t: number) => pkg.ttab[t] ?? {k: 'invalid'}
export function harnessC(file: string, c: CRead, read: GoRead, opts: COptions, cpp: boolean): string {
  const pkg = c.pkg, T = (t: number) => ty(pkg, t), acc = (path: string[]) => `o->${path.join('.')}`, q = JSON.stringify
  const get: string[] = [], set: string[] = []
  const intOut = (e: string, t: number) => (T(t).signed === false ? `gdp_putf("\\"%llu\\"", (unsigned long long)(${e}))` : `gdp_putf("\\"%lld\\"", (long long)(${e}))`)
  const intIn = (dst: string, raw: string, t: number, err: string) => `{ long long s_; unsigned long long u_; if (!gdp_int(${raw}, ${T(t).bits ?? 64}, ${T(t).signed === false ? 0 : 1}, &s_, &u_)) ${err}; ${dst} = (${T(t).go})(${T(t).signed === false ? 'u_' : 's_'}); }`
  for (const l of read.leaves) {
    const a = acc(l.path), k = q(l.name)
    if (l.kind === 'int') { get.push(`gdp_putf("%s\\"%s\\":", sep, ${k}); sep = ","; ${intOut(a, l.t)};`); set.push(`if ((v = gdp_key(st, ${k}))) ${intIn(a, 'v', l.t, `return "${l.name} outside its type"`)}`) }
    else if (l.kind === 'list') {
      // (a fixed array: all its items, exactly its length set)
      const at = T(l.t), n = at.len!, et = at.elem!, item = (e: string) => (T(et).k === 'int' ? intOut(e, et) : `gdp_putf("%s", ${e} ? "true" : "false")`)
      get.push(`gdp_putf("%s\\"%s\\":[", sep, ${k}); sep = ","; for (int i = 0; i < ${n}; i++) { if (i) gdp_putf(","); ${item(`${a}[i]`)}; } gdp_putf("]");`)
      set.push(`if ((v = gdp_key(st, ${k}))) { for (int i = 0; i < ${n}; i++) { const char *e = gdp_idx(v, i); if (!e) return "${l.name}: not ${n} items"; ${T(et).k === 'int' ? intIn(`${a}[i]`, 'e', et, `return "${l.name}: an item outside its type"`) : `${a}[i] = !strncmp(e, "true", 4);`} } if (gdp_idx(v, ${n})) return "${l.name}: not ${n} items"; }`)
    } else if (l.kind === 'bool') { get.push(`gdp_putf("%s\\"%s\\":%s", sep, ${k}, ${a} ? "true" : "false"); sep = ",";`); set.push(`if ((v = gdp_key(st, ${k}))) { if (!strncmp(v, "true", 4)) ${a} = 1; else if (!strncmp(v, "false", 5)) ${a} = 0; else return "${l.name}: not a boolean"; }`) }
  }
  const frames = read.leaves.filter(l => l.kind === 'frame')
  const calls = read.methods.map(meth => {
    const lines: string[] = [], args: string[] = ['o']
    meth.params.forEach((pa, i) => {
      const t = T(pa.t), raw = `gdp_idx(a, ${i})`
      if (pa.arg.k === 'input') {
        lines.push(`${t.go} a${i}; memset(&a${i}, 0, sizeof a${i}); const char *r${i} = ${raw}; if (!r${i}) return "no argument ${i}";`)
        lines.push(t.k === 'int' ? intIn(`a${i}`, `r${i}`, pa.t, `return "argument ${i} outside its type"`) : `a${i} = !strncmp(r${i}, "true", 4);`)
        args.push(`a${i}`)
      } else if (pa.arg.k === 'rec') {
        const byValue = t.k !== 'ptr', st = byValue ? t : T(t.elem!)
        lines.push(`${st.go} a${i}; memset(&a${i}, 0, sizeof a${i}); const char *r${i} = ${raw}; if (!r${i}) return "no argument ${i}";`)
        for (const [f] of pa.arg.fields) {
          const ft = st.fields!.find(g => g.name === f)!.t
          lines.push(`if ((v = gdp_key(r${i}, ${q(f)}))) ${T(ft).k === 'int' ? intIn(`a${i}.${f}`, 'v', ft, `return "argument ${i}.${f} outside its type"`) : `a${i}.${f} = !strncmp(v, "true", 4);`}`)
        }
        args.push(byValue ? `a${i}` : `&a${i}`)
      } else lines.push(`return "an argument the harness can't make";`)
    })
    const rt = meth.results[0], fails = opts.fails?.[meth.name]?.trim()
    const invoke = rt === undefined ? `${meth.name}(${args.join(', ')});` : `${T(rt).go} r0 = ${meth.name}(${args.join(', ')}); gdp_has = 1; ${T(rt).k === 'int' ? `gdp_outv = ${T(rt).signed === false ? '(long long)' : ''}r0; gdp_outu = ${T(rt).signed === false ? 1 : 0};` : 'gdp_outb = r0; gdp_isb = 1;'}`
    const failed = fails !== undefined && rt !== undefined ? `if (r0 ${fails.replace(/^(==|!=|<=|>=|<|>)\s*/, '$1 ')}) gdp_err = 1;` : ''
    return `if (!strcmp(m, ${q(meth.name)})) {\n    ${lines.join('\n    ')}\n    gdp_T pre = *o;\n    int sg = sigsetjmp(gdp_jb, 1);\n    if (!sg) { gdp_armed = 1; ${invoke} ${failed} gdp_armed = 0; } else gdp_sig = sg;\n    return gdp_after(o, &pre);\n  }`
  })
  return `// Generated by gdp-wired's ${cpp ? 'C++' : 'C'} check (core/extract-c.ts): the file's code is called as it is.
#define main gdp_orig_main
#include ${q(file)}
#undef main
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <signal.h>
#include <setjmp.h>
#include <errno.h>
${cpp ? '' : '#include <stdbool.h>\n'}
typedef ${c.cname} gdp_T;
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
static int gdp_sig, gdp_err, gdp_has, gdp_outu, gdp_isb; static long long gdp_outv; static bool gdp_outb;
static void gdp_on(int s) { if (gdp_armed) { gdp_armed = 0; siglongjmp(gdp_jb, s); } signal(s, SIG_DFL); raise(s); }
static const char *gdp_frame(gdp_T *o, gdp_T *pre) {
  (void)o; (void)pre;
  ${frames.map(l => `if (memcmp(&o->${l.path.join('.')}, &pre->${l.path.join('.')}, sizeof o->${l.path.join('.')})) return ${q(l.path.join('.'))};`).join('\n  ')}
  return 0;
}
static const char *gdp_after(gdp_T *o, gdp_T *pre) {
  const char *f = gdp_frame(o, pre);
  if (f) { gdp_putf(",\\"frame\\":\\"%s\\"", f); }
  if (gdp_sig) gdp_putf(",\\"panic\\":\\"%s\\"", gdp_sig == SIGABRT ? "SIGABRT (abort, or an assertion failing)" : gdp_sig == SIGTRAP || gdp_sig == SIGILL ? "undefined behavior (the sanitizer's trap)" : "a signal");
  else if (gdp_err) gdp_putf(",\\"err\\":\\"its result is its failure (%lld)\\"", gdp_outv);
  if (!gdp_sig && gdp_has) { if (gdp_isb) gdp_putf(",\\"out\\":%s,\\"hasOut\\":true", gdp_outb ? "true" : "false"); else if (gdp_outu) gdp_putf(",\\"out\\":\\"%llu\\",\\"hasOut\\":true", (unsigned long long)gdp_outv); else gdp_putf(",\\"out\\":\\"%lld\\",\\"hasOut\\":true", gdp_outv); }
  if (${opts.onError === 'discard' ? 1 : 0} && (gdp_sig || gdp_err)) *o = *pre;
  gdp_putf(",\\"state\\":"); gdp_get(o);
  return 0;
}
static const char *gdp_call(gdp_T *o, const char *m, const char *a) {
  const char *v; (void)v; (void)a;
  gdp_sig = gdp_err = gdp_has = gdp_outu = gdp_isb = 0; gdp_outv = 0;
  ${calls.join('\n  ')}
  return "no such function";
}
int main(int argc, char **argv) {
  if (argc < 3) return 2;
  FILE *in = fopen(argv[1], "r"), *out = fopen(argv[2], "w");
  if (!in || !out) return 2;
  int sigs[] = {SIGABRT, SIGTRAP, SIGILL, SIGFPE, SIGSEGV, SIGBUS};
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
    if (op && !strncmp(op, "\\"new\\"", 5)) { objs = (gdp_T **)realloc(objs, ++nobj * sizeof *objs); objs[nobj - 1] = (gdp_T *)calloc(1, sizeof(gdp_T)); gdp_putf("{\\"id\\":%zu}", nobj); }
    else if (op && !strncmp(op, "\\"at\\"", 4)) {
      gdp_T *o = (gdp_T *)calloc(1, sizeof(gdp_T)); const char *st = gdp_key(line, "state"), *bad = st ? gdp_set(o, st) : "no state";
      if (bad) { gdp_putf("{\\"bad\\":\\"%s\\"}", bad); free(o); }
      else { objs = (gdp_T **)realloc(objs, ++nobj * sizeof *objs); objs[nobj - 1] = o; gdp_putf("{\\"id\\":%zu}", nobj); }
    }
    else if (op && !strncmp(op, "\\"get\\"", 5)) { gdp_putf("{\\"state\\":"); gdp_get(objs[k - 1]); gdp_putf("}"); }
    else if (op && !strncmp(op, "\\"call\\"", 6)) {
      const char *mv = gdp_key(line, "m"), *av = gdp_key(line, "a"); char m[256] = {0};
      if (mv && *mv == '"') { const char *e = strchr(mv + 1, '"'); size_t n = e ? (size_t)(e - mv - 1) : 0; if (n > 255) n = 255; memcpy(m, mv + 1, n); }
      gdp_putf("{\\"ok\\":true");
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
// --- the check ------------------------------------------------------------------------------------------------------------
export function checkC(file: string, flags: string[], c: CRead, read: GoRead, r: Rule, sorts: Sorts, opts: COptions, cpp: boolean): GoEvidence {
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string, platform: () => string}>('node:os'), path = node<{resolve: (p: string) => string}>('node:path')
  const work = fs.mkdtempSync(`${os.tmpdir()}/gdp-ccheck-`), code = harnessC(path.resolve(file), c, read, opts, cpp), b0 = performance.now()
  const empty = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, buildMs: 0, runMs: 0}
  try {
    const h = `${work}/harness.${cpp ? 'cpp' : 'c'}`
    fs.writeFileSync(h, code)
    if (opts.check?.keep) { fs.mkdirSync(opts.check.keep, {recursive: true}); fs.writeFileSync(`${opts.check.keep}/harness.${cpp ? 'cpp' : 'c'}`, code) }
    // The same flags; undefined behavior trapped (the rule refuses it, so the code must fail there too); another
    // file's functions left unresolved (the rule refuses their calls: one reached is the code's crash, a difference).
    const undef = os.platform() === 'darwin' ? ['-Wl,-undefined,dynamic_lookup'] : ['-Wl,--unresolved-symbols=ignore-all']
    try { cp.execFileSync(opts.clang ?? 'clang', [...(cpp ? ['-x', 'c++'] : []), ...flags, '-w', '-O0', '-fsanitize=undefined', '-fsanitize-trap=undefined', '-fno-sanitize=vptr,function', ...strictFlex(opts.clang ?? 'clang'), h, '-o', `${work}/harness`, ...(cpp ? ['-lstdc++'] : []), ...undef], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26}) }
    catch (x) { return {...empty, mismatch: `the file doesn't build with the check's harness: ${String((x as {stderr?: string}).stderr ?? (x as Error).message).split('\n').filter(l => /error/.test(l)).slice(0, 6).join(' | ')}`} }
    const buildMs = Math.round(performance.now() - b0), none = (): Coverage => ({arms: 0, hit: 0, missed: []})
    return {...speak(work, `${work}/harness`, (globalThis as {process?: {env?: Record<string, string>}}).process?.env, c.pkg, read, r, sorts, opts.check ?? {}, none), buildMs}
  } finally {
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
}
