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
  const flags0 = [...flagsFor(file, opts.compileCommands), ...(opts.flags ?? [])], flags = cpp && !flags0.some(f => f.startsWith('-std=')) ? [...flags0, '-std=c++17'] : flags0, {tu, target} = clangDump(file, flags, opts.clang ?? (cpp ? 'clang++' : 'clang'), cpp, cpp ? opts.entry : undefined)
  return {c: readC(file, opts.entry, tu, target, cpp, opts.root, Object.fromEntries((opts.functions ?? []).filter(f => f.includes('/')).map(f => [f.split('/')[0]!, Number(f.split('/')[1])]))), flags}
}
export function extractC(file: string, opts: COptions, cpp = false): Extraction & {leaves?: GoLeaf[]} {
  const notes: string[] = []
  let read: GoRead, c: CRead, flags: string[]
  try {
    ;({c, flags} = readCFile(file, opts, cpp))
    read = readGo(c.pkg, {entry: opts.entry, methods: opts.functions?.map(f => f.split('/')[0]!) ?? c.methods, ...(opts.onError ? {onError: opts.onError} : {}), ...(opts.fails ? {fails: opts.fails} : {})} as GoOptions)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes}
    throw e
  }
  // (a signed leaf the caller states is a natural: its range law from 0, the claim for those states)
  for (const [n, d] of Object.entries(opts.domains ?? {})) if (d === 'nat') read.model.laws = read.model.laws?.map(l => (l.includes(`"${n} within its type's range"`) ? l.replace(/\.atLeast\(-\d+\)/, '.atLeast(0)') : l))
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

// The C++ front end (`gdp-wired/extract-cpp`): a class, its public methods the requests, its constructor the start (its
// parameters the rule's); `this` and references are pointers into the state, std::array a fixed array, std::min and
// std::max, std::lock_guard, std::scoped_lock and std::unique_lock of a member mutex the step atomic (Go's Lock with its
// deferred Unlock), a throw the step's refusal. Refused: templates, virtual methods, overloads, other classes' methods,
// STL containers but std::array, lambdas, try and catch.
export const extractCpp = (file: string, opts: COptions) => extractC(file, opts, true)

// --- the harness: C (or C++) that #includes the file, sets and prints the state's leaves as JSON lines -------------------
const ty = (pkg: GoPkg, t: number) => pkg.ttab[t] ?? {k: 'invalid'}
export function harnessC(file: string, c: CRead, read: GoRead, opts: COptions, cpp: boolean): string {
  const pkg = c.pkg, T = (t: number) => ty(pkg, t), q = JSON.stringify, robs: string[] = []
  // A leaf's place: o->a.b in C; in C++ each member through a pointer to it the explicit instantiation of gdp_rob takes
  // (access isn't checked there), so private members are read and set as the class's own code does.
  const acc = (path: string[]) => {
    if (!cpp) return `o->${path.join('.')}`
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
    } else if (l.kind === 'bool') { get.push(`gdp_putf("%s\\"%s\\":%s", sep, ${k}, ${a} ? "true" : "false"); sep = ",";`); set.push(`if ((v = gdp_key(st, ${k}))) { if (!strncmp(v, "true", 4)) ${a} = 1; else if (!strncmp(v, "false", 5)) ${a} = 0; else return "${l.name}: not a boolean"; }`) }
  }
  const frames = read.leaves.filter(l => l.kind === 'frame' && !T(l.t).mutex)
  const calls = read.methods.map(meth => {
    const lines: string[] = [], args: string[] = ['o'], outs: [string, string, number][] = []
    meth.params.forEach((pa, i) => {
      const t = T(pa.t), raw = `gdp_idx(a, ${i})`
      if (pa.arg.k === 'input') {
        lines.push(`${t.go} a${i}; memset(&a${i}, 0, sizeof a${i}); const char *r${i} = ${raw}; if (!r${i}) return "no argument ${i}";`)
        lines.push(t.k === 'int' ? intIn(`a${i}`, `r${i}`, pa.t, `return "argument ${i} outside its type"`) : `a${i} = !strncmp(r${i}, "true", 4);`)
        args.push(`a${i}`)
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
        args.push(byValue ? `a${i}` : `&a${i}`)
      } else lines.push(`return "an argument the harness can't make";`)
    })
    const rt = meth.results[0], fails = opts.fails?.[meth.name]?.trim()
    const callee = cpp ? `o->${meth.name}(${args.slice(1).join(', ')})` : `${meth.name}(${args.join(', ')})`
    const invoke = rt === undefined ? `${callee};` : `${cpp ? 'auto' : T(rt).go} r0 = ${callee}; gdp_has = 1; ${T(rt).k === 'int' ? `gdp_outv = ${T(rt).signed === false ? '(long long)' : ''}r0; gdp_outu = ${T(rt).signed === false ? 1 : 0};` : 'gdp_outb = r0; gdp_isb = 1;'}`
    const failed = fails !== undefined && rt !== undefined ? `if (r0 ${fails.replace(/^(==|!=|<=|>=|<|>)\s*/, '$1 ')}) gdp_err = 1;` : ''
    // (with out-parameters, the result is a record: the value returned and what each holds)
    const rec = outs.length ? `gdp_rec = 1; gdp_putf(",\\"out\\":{"); ${[...(rt !== undefined ? [['result', 'r0', rt] as [string, string, number]] : []), ...outs].map(([n, v, et], j) => `gdp_putf("${j ? ',' : ''}\\"${n}\\":"); ${T(et).k === 'int' ? `gdp_putf(${T(et).signed === false ? '"%llu", (unsigned long long)' : '"%lld", (long long)'}(${v}))` : `gdp_putf("%s", ${v} ? "true" : "false")`};`).join(' ')} gdp_putf("},\\"hasOut\\":true");` : ''
    return `if (!strcmp(m, ${q(meth.name)})) {\n    ${lines.join('\n    ')}\n    memcpy(gdp_pre, (void *)o, sizeof(gdp_T));\n    int sg = sigsetjmp(gdp_jb, 1);\n    if (!sg) { gdp_armed = 1; ${cpp ? 'try { ' : ''}${invoke} ${failed} gdp_armed = 0; ${rec}${cpp ? ' } catch (...) { gdp_armed = 0; gdp_sig = SIGUSR2; }' : ''} } else gdp_sig = sg;\n    return gdp_after(o);\n  }`
  })
  const frameLines = frames.map(l => { const e = acc(l.path); return `if (memcmp((char *)&${e}, (char *)gdp_pre + ((char *)&${e} - (char *)o), sizeof ${e})) return ${q(l.path.join('.'))};` })
  // The object, made as the code makes it: C's zeroed; C++'s constructed (in zeroed memory) with the rule's parameters.
  const cps = read.ctor ?? [], make = `static gdp_T *gdp_make(const char *line, const char **bad) {
  const char *a = gdp_key(line, "a"), *v; (void)a; (void)v;
  ${cps.map((pa, i) => `${T(pa.t).go} c${i} = 0; if (!(v = a ? gdp_idx(a, ${i}) : 0)) { *bad = "no argument ${i}"; return 0; } ${T(pa.t).k === 'int' ? intIn(`c${i}`, 'v', pa.t, `{ *bad = "argument ${i} outside its type"; return 0; }`) : `c${i} = !strncmp(v, "true", 4);`}`).join('\n  ')}
  void *mem = calloc(1, sizeof(gdp_T));
  return ${cpp ? `new (mem) gdp_T(${cps.map((_, i) => `c${i}`).join(', ')})` : '(gdp_T *)mem'};
}`
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
${cpp ? '#include <new>\n#include <type_traits>\n' : '#include <stdbool.h>\n'}
typedef ${c.cname} gdp_T;
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
  if (gdp_sig) gdp_putf(",\\"panic\\":\\"%s\\"", gdp_sig == SIGABRT ? "SIGABRT (abort, or an assertion failing)" : gdp_sig == SIGTRAP || gdp_sig == SIGILL ? "undefined behavior (the sanitizer's trap)" : gdp_sig == SIGUSR1 ? "another file's function called" : gdp_sig == SIGUSR2 ? "an exception thrown" : "a signal");
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
  if (argc == 2 && !strcmp(argv[1], "--probe")) return 0;
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
    if (op && !strncmp(op, "\\"new\\"", 5)) { const char *bad = 0; gdp_T *o = gdp_make(line, &bad); if (!o) gdp_putf("{\\"bad\\":\\"%s\\"}", bad); else { objs = (gdp_T **)realloc(objs, ++nobj * sizeof *objs); objs[nobj - 1] = o; gdp_putf("{\\"id\\":%zu}", nobj); } }
    else if (op && !strncmp(op, "\\"at\\"", 4)) {
      const char *bad = 0; gdp_T *o = gdp_make(line, &bad); const char *st = gdp_key(line, "state");
      if (o) bad = st ? gdp_set(o, st) : "no state";
      if (bad) gdp_putf("{\\"bad\\":\\"%s\\"}", bad);
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
    // file's functions linked as stubs that report themselves (the rule refuses their calls: one reached is the
    // code's failure where the rule took the step, a difference).
    const clang = opts.clang ?? (cpp ? 'clang++' : 'clang'), stubs = `${work}/gdp_stubs.c`
    const link = (more: string[]) => cp.execFileSync(clang, [...(cpp ? ['-x', 'c++'] : []), ...flags, '-w', '-O0', '-fsanitize=undefined', '-fsanitize-trap=undefined', '-fno-sanitize=vptr,function', ...strictFlex(clang), h, ...(more.length ? ['-x', 'c', ...more] : []), '-o', `${work}/harness`, ], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], maxBuffer: 1 << 26})
    const why = (x: unknown) => String((x as {stderr?: string}).stderr ?? (x as Error).message)
    try { link([]) } catch (x) {
      const names = [...new Set([...why(x).matchAll(/undefined (?:reference to [`']|symbol: )_?([A-Za-z_]\w*)|"_([A-Za-z_]\w*)", referenced from/g)].map(m => m[1] ?? m[2]!))]
      if (!names.length) return {...empty, mismatch: `the file doesn't build with the check's harness: ${why(x).split('\n').filter(l => /error/.test(l)).slice(0, 6).join(' | ')}`}
      fs.writeFileSync(stubs, `void gdp_extern_called(const char *);\n${names.map(n => `void ${n}(void) { gdp_extern_called(${JSON.stringify(n)}); }`).join('\n')}\n`)
      try { link([stubs]) } catch (y) { return {...empty, mismatch: `the file doesn't build with the check's harness: ${why(y).split('\n').filter(l => /error/.test(l)).slice(0, 6).join(' | ')}`} }
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
