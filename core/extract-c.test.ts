// The C front end (core/extract-c.ts on core/c/reader.ts and Go's lowering): rules read from C through clang, each
// checked against the file it was read from (compiled with a generated harness, the undefined-behavior sanitizer
// trapping). The cases: unsigned wrap, signed overflow refused where the path doesn't exclude it, truncating division,
// a stated failure, assert and abort, a switch's fallthrough, ?: and an enum, and the refusals. Skipped without clang.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {appendFileSync, mkdtempSync, readFileSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveRule, proveSteps} from './dsl.ts'
import {type COptions, extractC, extractCpp} from './extract-c.ts'
import {buildLaw} from './laws.ts'

const hasClang = (() => { try { execFileSync('clang', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasClang ? test : test.skip
const c = (code: string, entry: string, more: Partial<COptions> = {}, cpp = false) => {
  const file = `${mkdtempSync(`${tmpdir()}/gdp-ccase-`)}/case.${cpp ? 'cpp' : 'c'}`
  writeFileSync(file, code)
  return (cpp ? extractCpp : extractC)(file, {entry, check: {runs: 25, depth: 6, states: 50}, ...more})
}
const cpp = (code: string, entry: string, more: Partial<COptions> = {}) => c(code, entry, more, true)
type X = ReturnType<typeof c>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type A = any
// A callback retains its exact checked model proof, never a native-source claim.
// Every callback below has an equivalent registered law evaluated on real native observations.
const modelOnly = {kernelProven: true, proven: false, checked: false, translation: 'unchecked', why: 'source translation unchecked: a source proof contains a law with no native interpretation'}
const native = (v: ReturnType<typeof proveSteps>, name?: string) => {
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
  const out = process.env.SUPERCOMPUTER_OUTPUT_DIR
  if (out) appendFileSync(`${out}/c-native-verdicts.jsonl`, `${JSON.stringify({name, proven: v.proven, checked: v.checked, translation: v.translation, translationChecks: v.translationChecks})}\n`)
}
const step = (x: X, name: string, then: (b: A, a: A) => A, when: (b: A) => A, expr: string, method?: string) => {
  const r = x.rule as A
  expect(proveSteps(r, x.invariants ?? [], [r.stepLaw(name, then, when)])).toMatchObject(modelOnly)
  const built = buildLaw(x, {name, expr, ...(method ? {method} : {})})
  expect(built.kind).toBe('step')
  native(proveSteps(r, x.invariants ?? [], [built.law]), name)
}
const inv = (x: X, name: string, holds: (s: A) => A, expr: string) => {
  const r = x.rule as A
  expect(proveRule(r, [...x.invariants ?? [], r.law(name, holds)])).toMatchObject(modelOnly)
  const built = buildLaw(x, {name, expr})
  expect(built.kind).toBe('law')
  native(proveRule(r, [...x.invariants ?? [], built.law]), name)
}

t('unsigned arithmetic wraps; a narrow one is promoted and converted back', () => {
  const x = ok(c(`
#include <stdint.h>
struct ctr { uint8_t lap; uint32_t total; unsigned short seq; };
void tick(struct ctr *c) { c->lap++; c->seq += 1; }
void add(struct ctr *c, uint32_t n) { c->total += n; }
`, 'ctr'))
  expect(x.notes.join('\n')).toMatch(/uint8_t: a result past its range wraps modulo 2\^8, as C's does/)
  step(x, 'a lap wraps at 256', (_b, a) => a.lap.eq(0), b => b.method.is('tick').and(b.lap.eq(255)), 'old(lap) == 255 implies lap == 0', 'tick')
  step(x, 'a total past 2^32 wraps', (b, a) => a.total.eq(b.total.plus(b.add_n).minus(4294967296)), b => b.method.is('add').and(b.total.plus(b.add_n).atLeast(4294967296)), 'old(total) + n >= 4294967296 implies total == old(total) + n - 4294967296', 'add')
}, 60_000)

t('signed overflow is undefined: refused where the path doesn\'t exclude it, never wrapped', () => {
  const src = `
struct acc { int n; int hits; };
void bump(struct acc *a) { a->n++; }
void guarded(struct acc *a) { if (a->hits < 1000) a->hits = a->hits + 1; }
`
  const x = ok(c(src, 'acc'))
  expect(x.notes.join('\n')).toMatch(/int: a result past its range is refused \(signed overflow is undefined behavior in C\)/)
  // (the rule refuses bump at INT_MAX; guarded's + 1 is within int by its if, so it is never refused)
  expect(x.source).toMatch(/method\.is\('bump'\)\.implies\(n\.plus\(1\)\.atMost\(2147483647\)\)/)
  expect(x.source).not.toMatch(/hits\.plus\(1\)\.atMost/)
  inv(x, 'hits at most 1000 once there', ({hits}: A) => hits.atMost(2147483647), 'hits <= 2147483647')
  step(x, 'guarded counts to 1000', (b, a) => a.hits.eq(b.hits.plus(1)), b => b.method.is('guarded').and(b.hits.lt(1000)), 'old(hits) < 1000 implies hits == old(hits) + 1', 'guarded')
}, 60_000)

t('division and remainder truncate toward zero; by zero it is refused', () => {
  const x = ok(c(`
struct h { int half; int rest; int v; };
void split(struct h *s, int k) { s->v = k; s->half = k / 2; s->rest = k % 2; }
`, 'h'))
  step(x, 'the half and the rest make k again', (_b, a) => a.half.plus(a.half).plus(a.rest).eq(a.v), b => b.method.is('split'), 'half + half + rest == v', 'split')
  step(x, 'the rest takes the sign of k', (b, a) => a.rest.atMost(0), b => b.method.is('split').and(b.split_k.lt(0)), 'k < 0 implies rest <= 0', 'split')
}, 60_000)

t('a stated failure, assert and abort are refusals; a write before one needs onError: discard', () => {
  const src = `
#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
typedef struct { uint32_t tokens; uint32_t cap; } bucket;
int take(bucket *b, uint32_t n) { if (b->tokens < n) return -1; b->tokens -= n; return 0; }
void put(bucket *b, uint32_t n) { assert(n <= b->cap); if (b->cap - b->tokens < n) abort(); b->tokens += n; }
void setcap(bucket *b, uint32_t c) { b->cap = c; if (b->tokens > c) b->tokens = c; }
`
  const x = ok(c(src, 'bucket', {fails: {take: '< 0'}}))
  step(x, 'a take never goes below 0', (b, a) => a.tokens.eq(b.tokens.minus(b.take_n)), b => b.method.is('take'), 'tokens == max(0, old(tokens) - n)', 'take')
  inv(x, 'tokens within cap', ({tokens, cap}: A) => tokens.atMost(cap), 'tokens <= cap')
  expect(x.evidence!.refusedBoth).toBeGreaterThan(0)
  const w = c(`#include <stdlib.h>\nstruct s { int a; unsigned b; };\nvoid f(struct s *s, unsigned k) { s->a = 1; if (k > 5) abort(); s->b = k; }\n`, 's')
  expect(w.ok).toBe(false)
  expect(w.refusals[0]!.what).toMatch(/abort\(\) after the state is written/)
  // (glibc's assert: a discarded sizeof, then a statement expression)
  ok(c('#include <stdlib.h>\nstruct s { unsigned a; };\n#define gassert(e) ((void) sizeof ((e) ? 1 : 0), __extension__ ({ if (e) ; else abort (); }))\nvoid f(struct s *s, unsigned k) { gassert(k < 9); s->a = k; }\n', 's'))
  ok(c(`#include <stdlib.h>\nstruct s { int a; unsigned b; };\nvoid f(struct s *s, unsigned k) { s->a = 1; if (k > 5) abort(); s->b = k; }\n`, 's', {onError: 'discard'}))
}, 60_000)

t('a switch: labels together, a case running into the next, an enum, ?: and the file\'s functions inlined', () => {
  const x = ok(c(`
#include <stdbool.h>
enum state { CLOSED, OPEN, HALF };
struct cb { enum state st; unsigned fails; unsigned limit; bool tripped; };
static void trip(struct cb *b) { b->st = OPEN; b->tripped = true; }
void fail(struct cb *b) {
  switch (b->st) {
  case CLOSED: b->fails++;
  case HALF: if (b->fails >= b->limit || b->st == HALF) trip(b); break;
  default: break;
  }
}
void ok(struct cb *b) { b->fails = 0; b->st = b->st == HALF ? CLOSED : b->st; }
void probe(struct cb *b) { if (b->st == OPEN) b->st = HALF; }
`, 'cb'))
  step(x, 'a failure half open trips it', (_b, a) => a.st.eq(1).and(a.tripped), b => b.method.is('fail').and(b.st.eq(2)), 'old(st) == HALF implies st == OPEN and tripped', 'fail')
  step(x, 'a success closes a half-open breaker', (_b, a) => a.st.eq(0).and(a.fails.eq(0)), b => b.method.is('ok').and(b.st.eq(2)), 'old(st) == HALF implies st == CLOSED and fails == 0', 'ok')
}, 60_000)

t('a fixed array is a list of its length; an index the path doesn\'t keep within it is refused (undefined behavior)', () => {
  const x = ok(c(`
#include <stdint.h>
#define N 8
struct rb { uint8_t buf[N]; uint32_t head, tail, count; };
int rb_put(struct rb *r, uint8_t x) { if (r->count == N) return -1; r->buf[r->head] = x; r->head = (r->head + 1) & (N - 1); r->count++; return 0; }
int rb_get(struct rb *r) { if (r->count == 0) return -1; int x = r->buf[r->tail]; r->tail = (r->tail + 1) % N; r->count--; return x; }
`, 'rb', {fails: {rb_put: '< 0', rb_get: '< 0'}}))
  expect(x.source).toContain('.items({buf: nat}, {buf: 8})')
  expect(x.notes.join('\n')).not.toMatch(/rb_get.*after the state is written/)
  inv(x, 'at most 8 held', ({count}: A) => count.atMost(8), 'count <= 8')
  step(x, 'a put keeps its item at the head', (b, a) => a.buf.at(b.head).eq(b.rb_put_x), b => b.method.is('rb_put').and(b.count.lt(8)).and(b.head.lt(8)), 'old(count) < 8 and old(head) < 8 implies buf[old(head)] == x', 'rb_put')
  const oob = c('struct q { int xs[4]; };\nvoid f(struct q *q, unsigned i) { q->xs[i] = 1; }\n', 'q')
  expect(oob.ok).toBe(true)
  expect(oob.source).toMatch(/f_i\.lt\(4\)|f_i\.atMost\(3\)/)
}, 60_000)

t('an out-parameter: what the function leaves in *data is its result beside the value returned; masks of promoted values', () => {
  const x = ok(c(`
#include <stdint.h>
#include <stdbool.h>
#define N 16
typedef struct { uint8_t buf[N]; uint8_t head, tail; } rb_t;
static inline bool rb_full(rb_t *r) { return ((r->head - r->tail) & (N - 1)) == (N - 1); }
static inline bool rb_empty(rb_t *r) { return r->head == r->tail; }
void rb_queue(rb_t *r, uint8_t x) { if (rb_full(r)) r->tail = (r->tail + 1) & (N - 1); r->buf[r->head] = x; r->head = (r->head + 1) & (N - 1); }
uint8_t rb_dequeue(rb_t *r, uint8_t *data) { if (rb_empty(r)) return 0; *data = r->buf[r->tail]; r->tail = (r->tail + 1) & (N - 1); return 1; }
`, 'rb_t', {fails: {rb_dequeue: '== 0'}, onError: 'discard'}))
  expect(x.source).toContain('rb_dequeue_data')
  step(x, 'a dequeue gives the item at the tail', (b, a) => a.rb_dequeue_data.eq(b.buf.at(b.tail)), b => b.method.is('rb_dequeue').and(b.tail.lt(16)), 'old(tail) < 16 implies result.data == old(buf[tail])', 'rb_dequeue')
}, 60_000)

t('refused where it leaves the subset, each with why', () => {
  const why = (code: string, entry: string) => { const r = c(code, entry, {strict: true}); expect(r.ok).toBe(false); return r.refusals[0]!.what }
  expect(why('struct q { int n; };\nvoid f(struct q *q) { while (q->n > 0) q->n--; }\n', 'q')).toMatch(/a loop \(while\)/)
  expect(why('int g;\nstruct q { int n; };\nvoid f(struct q *q) { q->n = g; }\n', 'q')).toMatch(/a global variable/)
  expect(why('#include <string.h>\nstruct q { unsigned n; };\nvoid f(struct q *q) { q->n = strlen("ab"); }\n', 'q')).toMatch(/another file or library|a string/)
  expect(why('struct q { unsigned n; };\nvoid f(struct q *q, unsigned k) { q->n = q->n / k; }\n', 'q')).toMatch(/other than a constant/)
  expect(why('struct q { unsigned n; };\nvoid f(struct q *q, unsigned k) { q->n = q->n ^ k; }\n', 'q')).toMatch(/a bit operation|bit-vectors are outside the subset/)
}, 60_000)

// --- C++ (extractCpp: the same reader and harness) ---------------------------------------------------------------------
const BUCKET = `
#include <mutex>
#include <array>
#include <cstdint>
#include <algorithm>
#include <stdexcept>
class Bucket {
 public:
  enum class State { Closed, Open };
  explicit Bucket(uint32_t cap) : cap_(cap), tokens_(cap) {}
  bool take(uint32_t n);
  void refill(uint32_t k) { std::lock_guard<std::mutex> g(mu_); tokens_ = std::min(cap_, tokens_ + k); }
  void trip() { state_ = State::Open; hits_[0] = 1; }
  int put(uint32_t n) { if (n > cap_) throw std::invalid_argument("too many"); return clamp(n); }
  bool pop(int &out) { if (hits_[1] == 0) return false; out = hits_[1]; hits_[1] = 0; return true; }
 private:
  int clamp(uint32_t n) { return n > 10 ? 10 : (int)n; }
  uint32_t cap_, tokens_;
  State state_ = State::Closed;
  std::array<int, 4> hits_{};
  std::mutex mu_;
};
bool Bucket::take(uint32_t n) { std::scoped_lock lk(mu_); if (tokens_ < n) return false; tokens_ -= n; return true; }
`
t('C++: a class, its constructor the start (its parameters the rule\'s), private members, lock guards, std::min, std::array, a throw', () => {
  const x = ok(cpp(BUCKET, 'Bucket'))
  expect(x.source).toContain('.params({cap: nat})')
  expect(x.source).toContain('tokens_: ({cap}) => cap')
  inv(x, 'never more tokens than the capacity', ({tokens_, cap_}: A) => tokens_.atMost(cap_), 'tokens_ <= cap_')
  step(x, 'a take is all or nothing', (b, a) => a.take_result.implies(a.tokens_.eq(b.tokens_.minus(b.take_n))), b => b.method.is('take'), 'result implies tokens_ == max(0, old(tokens_) - n)', 'take')
  step(x, 'a pop gives the item and clears it', (b, a) => a.pop_out.eq(b.hits_.at(1)).and(a.hits_.at(1).eq(0)), b => b.method.is('pop').and(b.hits_.at(1).eq(0).not()), 'old(hits_[1]) != 0 implies result.out == old(hits_[1]) and hits_[1] == 0', 'pop')
  expect(x.evidence!.refusedBoth).toBeGreaterThan(0)
}, 60_000)

// (clang 18 and earlier dump a default member initializer's use with nothing inside: the field's own is read)
t('C++: a default member initializer beside a constructor that sets other fields', () => {
  const x = ok(cpp(`
class Meter {
 public:
  explicit Meter(int start) : used_(start > 0 ? 0 : 0) {}
  bool use() { if (used_ >= cap_) return false; used_++; return true; }
 private:
  int used_;
  int cap_ = 3;
};
`, 'Meter'))
  inv(x, 'the cap is three', ({cap_}: A) => cap_.eq(3), 'cap_ == 3')
}, 60_000)

t('C++: refused where it leaves the subset, each with why', () => {
  const why = (code: string) => { const r = cpp(code, 'K'); expect(r.ok).toBe(false); return r.refusals[0]!.what }
  expect(why('struct K { int n = 0; virtual void v() { n++; } void f() { v(); } };\n')).toMatch(/virtual/)
  expect(why('#include <vector>\nstruct K { std::vector<int> xs; int n = 0; void f() { n = (int)xs.size(); } };\n')).toMatch(/another class|other code/)
  expect(why('struct K { int n = 0; void f() { auto g = [this] { n++; }; g(); } };\n')).toMatch(/subset|other code|lambda|another class/)
  expect(why('struct K { int n = 0; void f() { try { n++; } catch (...) {} } };\n')).toMatch(/try and catch/)
  expect(why('template <class T> struct K { T n; void f() { n++; } };\nK<int> k;\n')).toMatch(/class template/)
}, 60_000)

// Default auto-search may use 10s, beyond Bun's 5s test default.
t('the boundary inferred: a library call left out, another file\'s function answered over its declared type, the entry', () => {
  const x = ok(c(`#include <stdio.h>
int quota_bonus(int n);
struct meter { unsigned used; unsigned cap; };
void meter_init(struct meter *m, unsigned cap) { m->used = 0; m->cap = cap; }
int meter_take(struct meter *m, unsigned n) {
  fflush(stdout); // gdp: skip
  unsigned extra = (unsigned)quota_bonus((int)(n % 100));
  if (n > m->cap || extra > m->cap - n || m->used > m->cap - n - extra) return -1;
  m->used += n + extra;
  return 0;
}
`, undefined as never))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: meter/)
  expect(notes).toMatch(/fflush .*left out \(tagged: gdp: skip/)
  expect(notes).toMatch(/quota_bonus .*answered by the request \(inferred: its value is read; assumes quota_bonus may return any int\)/)
  step(x, 'never past its cap', (_b, a) => a.used.atMost(a.cap), b => b.used.atMost(b.cap), 'old(used) <= old(cap) implies used <= cap')
}, 30_000)

// The reader fuzz's misreads (core/extract-fuzz.ts): a literal past 2^53 converted exactly.
t('a literal past 2^53 stored in a narrower unsigned: its value there exactly (2^53 + 1 is 1 in 32 bits)', () => {
  const x = ok(c(`
struct cb { unsigned fails; unsigned limit; };
void fail(struct cb *b) { if (b->fails < b->limit) b->fails++; }
void ok(struct cb *b) { b->fails = 9007199254740993; }
`, 'cb'))
  step(x, 'ok sets it to 1', (_b, a) => a.fails.eq(1), b => b.method.is('ok'), 'fails == 1', 'ok')
}, 60_000)

t('a function of any name\'s length called; a natural by cases made an integer before it wraps', () => {
  const long = `g${'a'.repeat(400)}`
  ok(c(`struct acc { int n; int hits; };\nvoid ${long}(struct acc *a) { if (a->hits < 1000) a->hits = a->hits + 1; }\n`, 'acc'))
  const x = ok(cpp(`class Meter {\n public:\n  explicit Meter(int start) : used_(start > 0 ? 0 : 2147483648) {}\n  bool use() { if (used_ >= cap_) return false; used_++; return true; }\n private:\n  int used_;\n  int cap_ = 3;\n};\n`, 'Meter'))
  expect(x.source).toContain('Int.of(when(')
}, 60_000)

// The check's build (the code with the harness): a compiler failing with nothing to say of the code (killed, past
// GDP_COMPILE_S) is retried once, then the check's harness failure; its errors about the code, the source refused with
// its message. Never "the rule and the code differ".
const killedBuild = <X>(make: () => X): X => { const old = process.env.GDP_COMPILE_S; process.env.GDP_COMPILE_S = '0.001'; try { return make() } finally { if (old === undefined) delete process.env.GDP_COMPILE_S; else process.env.GDP_COMPILE_S = old } }
t('the check\'s build: clang killed is the harness\'s failure, retried once; a source clang rejects refused with its message', () => {
  const src = 'struct acc { int n; int hits; };\nvoid bump(struct acc *a) { a->n++; }\n'
  const killed = killedBuild(() => c(src, 'acc'))
  expect(killed.ok).toBe(false)
  expect(killed.refusals[0]!.what).toMatch(/^the check's harness failed, twice .*clang failed twice with nothing to say of the code/)
  const bad = c(src + 'void bad(struct acc *a) { a->n = a->nope; }\n', 'acc')
  expect(bad.refusals.map(r => r.what).join('; ')).toMatch(/no member named 'nope'/)
  expect(bad.refusals.map(r => r.what).join('; ')).not.toMatch(/the rule and the code differ/)
}, 120_000)

t('a long function name with characters past ASCII called by its bytes; a C++ constructor the check can\'t call refused', () => {
  ok(c(`struct acc { int n; int hits; };\nvoid g${'a'.repeat(300)}é(struct acc *a) { if (a->hits < 1000) a->hits = a->hits + 1; }\n`, 'acc'))
  const x = cpp(`class Meter {\n public:\n  int used_;\n  bool use() { if (used_ >= 3) return false; used_++; return true; }\n private:\n  explicit Meter(int start) : used_(start > 0 ? 0 : 0) {}\n};\n`, 'Meter')
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toMatch(/Meter: its constructor is private \(the check makes the object with it\)/)
}, 120_000)

// --- embedded idioms -------------------------------------------------------------------------------------------------------

t('bit operations with a constant: flags set, cleared, toggled and tested, composed into one form', () => {
  const x = ok(c(`
#include <stdint.h>
#define F_INIT 0x0001u
#define F_OK 0x0010u
#define F_ARMED 0x0100u
struct io { uint16_t flags; uint8_t mode; };
void tick(struct io *s, int ok) {
  if (ok) s->flags |= F_OK; else s->flags &= ~F_OK;
  if (s->flags & F_INIT) s->flags |= F_ARMED; else s->flags &= (uint16_t)~F_ARMED;
  s->mode ^= 0x3u;
}
void init(struct io *s) { s->flags |= F_INIT; }
`, 'io'))
  // (a law's bit tests, as the CLI reads them: an invariant through the rule's functions, a step's through keys)
  const law = (name: string, expr: string, method?: string) => buildLaw(x, {name, expr, ...(method ? {method} : {})}).law
  native(proveSteps(x.rule as A, x.invariants ?? [], [law('ok follows the request', '(flags & 0x10) != 0 or ok == 0', 'tick')]), 'ok follows the request')
  native(proveRule(x.rule as A, [...x.invariants!, law('init is never cleared once set', '(flags & 1) == 0 or (flags & 1) == 1')]), 'init is never cleared once set')
}, 120_000)

t('native C laws use real nested fields, arrays and arguments captured before local reassignment', () => {
  const code = `
#include <stdint.h>
struct capture { struct { uint32_t value; } sub; uint8_t buf[4]; uint32_t head; };
void put(struct capture *s, uint8_t x) {
  if (s->head >= 4) return;
  s->buf[s->head] = x; s->sub.value = x;
  s->head = (s->head + 1) % 4; x++;
}
`
  const x = ok(c(code, 'capture'))
  const make = (read: X, expr: string) => buildLaw(read, {name: 'the original x is stored', expr, method: 'put'}).law
  const expr = 'old(head) < 4 implies buf[old(head)] == x and sub.value == x'
  native(proveSteps(x.rule!, x.invariants ?? [], [make(x, expr)]), 'nested fields/array/pre-call argument native control')
  // Deliberately corrupt only the untrusted lowering. Real native observations
  // must reject its false source equation despite the kernel's tautology proof.
  const faulty = make(x, 'old(head) < 4 implies sub.value == x + 1')
  faulty.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = proveSteps(x.rule!, x.invariants ?? [], [faulty], {search: false})
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(rejected.translationWitness?.after).toHaveProperty('sub.value')
  expect(typeof rejected.translationWitness?.bindings.x).toBe('number')
  const out = process.env.SUPERCOMPUTER_OUTPUT_DIR
  if (out) writeFileSync(`${out}/c-native-tamper-witness.json`, JSON.stringify({translation: rejected.translation, kernelProven: rejected.kernelProven, witness: rejected.translationWitness, evidence: x.evidence}, null, 2))
  const disabled = c(code, 'capture', {check: {runs: 0, states: 0, probes: false}})
  expect(disabled.ok).toBe(true)
  expect(proveSteps(disabled.rule!, disabled.invariants ?? [], [make(disabled, expr)], {search: false})).toMatchObject({
    proven: false, checked: false, kernelProven: true, translation: 'unchecked',
    why: 'source translation unchecked: source replay or native-law cross-check was disabled',
  })
}, 60_000)

t('a bit operation of two values neither a constant nor 0 or 1 is refused', () => {
  const x = c(`
#include <stdint.h>
struct m { uint32_t a; };
void f(struct m *s, uint32_t b) { s->a = s->a & b; }
`, 'm')
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toMatch(/neither of them a constant.*\(bit-vectors are outside the subset\)/)
}, 60_000)

t('a file that keeps its state in globals: the globals one object, its functions requests, an extern volatile the request\'s', () => {
  const x = ok(c(`
#include <stdint.h>
typedef enum { UNINIT, READY } st_e;
static struct { uint16_t timer; st_e state; uint8_t entry; uint8_t err; } s = { .timer = 0, .state = UNINIT };
extern volatile uint8_t pin;
static uint8_t seen;
void trigger(void) {
  if (s.entry) return;
  s.entry++;
  if (s.timer > 0u) { if ((--s.timer) > 0u) { s.entry--; return; } }
  switch (s.state) { case UNINIT: s.timer = 2; s.state = READY; break; case READY: seen = pin; break; }
  s.entry--;
}
`, 'case'))
  expect(x.names!.some(n => n.code === 'pin' && n.role === 'input')).toBe(true)
  inv(x, 'the guard is released', ({s_entry}: A) => s_entry.eq(0), 's.entry == 0')
  inv(x, 'the timer stays below 3', ({s_timer}: A) => s_timer.atMost(2), 's.timer <= 2')
}, 120_000)

t('native C laws bind globals, request parameters and distinct constant-argument answers', () => {
  const x = ok(c(`
#include <stdbool.h>
enum { LEFT = 1, RIGHT = 2 };
bool allowed(unsigned request, int option);
static bool accepted;
void choose(unsigned request) {
  if (request == 0) accepted = allowed(request, LEFT);
  else accepted = allowed(request, RIGHT);
}
`, 'case'))
  expect(x.names).toEqual(expect.arrayContaining([
    expect.objectContaining({code: 'allowed_x_1', role: 'answer'}),
    expect.objectContaining({code: 'allowed_x_2', role: 'answer'}),
  ]))
  const law = buildLaw(x, {name: 'the selected answer updates the global', method: 'choose',
    expr: '(request == 0 implies accepted == allowed(request, LEFT)) and (request != 0 implies accepted == allowed(request, RIGHT))'})
  native(proveSteps(x.rule!, x.invariants ?? [], [law.law]), 'globals, pre-call request and keyed native answers')
}, 60_000)

t('floats only written are left out; one read into a condition is refused', () => {
  const x = ok(c(`
#include <stdint.h>
struct meter { uint8_t state; float volts; };
void sample(struct meter *m, uint16_t raw) { m->volts = raw * 0.0125f; if (m->state < 3) m->state++; }
`, 'meter'))
  expect(x.notes.join('\n')).toMatch(/volts: a float, a float, left out/)
  const y = c(`
struct meter { int state; float volts; };
void sample(struct meter *m) { if (m->volts > 3.0f) m->state = 1; }
`, 'meter')
  expect(y.ok).toBe(false)
  expect(y.refusals[0]!.what).toMatch(/a float/)
}, 120_000)

t('an endless loop is the step\'s failure; do { } while (0) runs once; a side effect in a condition runs first', () => {
  ok(c(`
#include <stdint.h>
#define CHECK(x) do { if (!(x)) { for (;;) { } } } while (0)
struct q { uint8_t n; uint8_t used; };
void take(struct q *s) { CHECK(s->n < 200); if ((s->used = s->n++) > 100) s->n = 0; }
`, 'q', {onError: 'discard'}))
}, 120_000)

t('C++: an enum without a fixed type holds its enumerators\' range; the laws read the code\'s constants', () => {
  const x = ok(cpp(`
#include <stdint.h>
const uint32_t LIMIT = 60;
class Dog {
 public:
  Dog() : step(COUNT), left(LIMIT) {}
  void tick() { if (step == COUNT) { if (--left <= 0) step = OFF; } else if (step == OFF) step = ON; }
  void feed() { if (step == ON) step = COUNT; left = LIMIT; }
 private:
  enum Step { COUNT, OFF, ON };
  Step step;
  int32_t left;
};
`, 'Dog'))
  expect(x.consts).toMatchObject({COUNT: 0, OFF: 1, ON: 2})
}, 120_000)

t('reader fuzz 693042: a wrapping initializer needing division is refused before kernel scope', () => {
  const x = cpp(readFileSync(new URL('./reader-fixtures/c-693042.cpp', import.meta.url), 'utf8'), 'Meter')
  expect(x.ok).toBe(false)
  expect(x.refusals[0]!.what).toMatch(/division or remainder in an initializer.*outside the reader's start-expression subset/)
}, 60_000)

t('default C const tables read array_filler partial and designated initializers in semantic order (small, mid-idx, 2-D, cast-init)', () => {
  const H = '#include <stdint.h>\n#include <stdbool.h>\n'
  const S = H + 'struct ring { int32_t n; };\n'
  // Every partial/designated const table extracts cleanly (0 differential mismatch) and refutes a false n == 0 law.
  const valueCases: [string, string, string, Partial<COptions>?][] = [
    ['t1-designated', S + 'static const int32_t T[4] = {[3] = 9};\nvoid f(struct ring *r, int32_t i) { if (i >= 1 && i < 4) r->n = T[i]; }\n', 'ring'],
    ['t2-partial', S + 'static const int32_t T[4] = {1, 2};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 4) r->n = T[i] + 6; }\n', 'ring'],
    ['t4-desig-over', S + 'static const int32_t T[3] = {7, [0] = 8};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 1) r->n = T[i]; }\n', 'ring'],
    ['u1-value', S + 'static const int32_t K[2] = {65536};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 2) r->n = K[i]; }\n', 'ring'],
    ['u2-value', S + 'static const int32_t K[2] = {1};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 2) r->n = K[i]; }\n', 'ring'],
    ['u3-2d-partial', S + 'static const int32_t T[2][2] = {{0}, {9}};\nvoid f(struct ring *r, int32_t i, int32_t j) { if (i >= 0 && i < 2 && j >= 0 && j < 2) r->n = T[i][j]; }\n', 'ring'],
    ['u4-ring-next', S + 'static const uint8_t NEXT[8] = {1, 2, 3, 4, 5, 6, 8};\nvoid adv(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = NEXT[r->n]; }\n', 'ring'],
    ['u5-gmode-table', H + 'static int32_t n;\nstatic const int32_t STEP[4] = {9};\nvoid put(int32_t k) { if (k >= 0 && k < 4) n = STEP[k]; }\n', 'case', {methods: ['put']}],
    ['mid-idx-64', S + 'static const int32_t T[64] = {[37] = 9};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 64) r->n = T[i]; }\n', 'ring'],
    ['mid-idx-200', S + 'static const int32_t T[200] = {[137] = 9};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 200) r->n = T[i]; }\n', 'ring'],
    ['2d-16x16', S + 'static const int32_t T[16][16] = {[7][11] = 9};\nvoid f(struct ring *r, int32_t i, int32_t j) { if (i >= 0 && i < 16 && j >= 0 && j < 16) r->n = T[i][j]; }\n', 'ring'],
  ]
  for (const [label, code, entry, opts] of valueCases) {
    const x = ok(c(code, entry, opts))
    const falseLaw = buildLaw(x, {name: `${label}: n stays zero`, expr: 'n == 0'}).law
    const res = proveRule(x.rule!, [...(x.invariants ?? []), falseLaw])
    expect(res.proven, `${label} must refute false n == 0 law`).toBe(false)
    expect(res.run, `${label} must produce a concrete counterexample`).toBeDefined()
  }

  // Position-sensitive proofs on sparse 1-D and 2-D tables: pin the exact non-zero index and every other index to 0.
  const pinSteps = (x: X, label: string, method: string, exprs: string[]) => {
    for (const expr of exprs) native(proveSteps(x.rule!, x.invariants ?? [], [buildLaw(x, {name: `${label}: ${expr}`, expr, method}).law]), `${label}: ${expr}`)
  }
  const mid64 = ok(c(S + 'static const int32_t T[64] = {[37] = 9};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 64) r->n = T[i]; }\n', 'ring'))
  pinSteps(mid64, 'mid-idx-64', 'f', ['i == 37 implies n == 9', 'i >= 0 and i < 64 and i != 37 implies n == 0'])
  native(proveRule(mid64.rule!, [...(mid64.invariants ?? []), buildLaw(mid64, {name: 'mid-idx-64: n is 0 or 9', expr: 'n == 0 or n == 9'}).law]), 'mid-idx-64: n is 0 or 9')
  const mid200 = ok(c(S + 'static const int32_t T[200] = {[137] = 9};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 200) r->n = T[i]; }\n', 'ring'))
  pinSteps(mid200, 'mid-idx-200', 'f', ['i == 137 implies n == 9', 'i >= 0 and i < 200 and i != 137 implies n == 0'])
  native(proveRule(mid200.rule!, [...(mid200.invariants ?? []), buildLaw(mid200, {name: 'mid-idx-200: n is 0 or 9', expr: 'n == 0 or n == 9'}).law]), 'mid-idx-200: n is 0 or 9')
  const sparse2d = ok(c(S + 'static const int32_t T[16][16] = {[7][11] = 9};\nvoid f(struct ring *r, int32_t i, int32_t j) { if (i >= 0 && i < 16 && j >= 0 && j < 16) r->n = T[i][j]; }\n', 'ring'))
  pinSteps(sparse2d, '2d-16x16', 'f', ['i == 7 and j == 11 implies n == 9', 'i >= 0 and i < 16 and j >= 0 and j < 16 and (i != 7 or j != 11) implies n == 0'])
  native(proveRule(sparse2d.rule!, [...(sparse2d.invariants ?? []), buildLaw(sparse2d, {name: '2d-16x16: n is 0 or 9', expr: 'n == 0 or n == 9'}).law]), '2d-16x16: n is 0 or 9')

  // Narrowing cast initializers ((uint8_t)(-1) == 255, (int8_t)255 == -1) wrap in C across both full and partial tables.
  for (const [label, decl, pin] of [
    ['cast-init-full', 'static const int32_t T[2] = {(uint8_t)(-1), 0};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 2) r->n = T[i]; }\n',
      ['i == 0 implies n == 255', 'i == 1 implies n == 0']],
    ['cast-init-partial', 'static const int32_t T[64] = {[37] = (uint8_t)(-1)};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 64) r->n = T[i]; }\n',
      ['i == 37 implies n == 255', 'i >= 0 and i < 64 and i != 37 implies n == 0']],
  ] as [string, string, string[]][]) {
    const x = ok(c(S + decl, 'ring'))
    for (const falseExpr of ['n == 0', 'n == 0 or n == -1']) {
      const res = proveRule(x.rule!, [...(x.invariants ?? []), buildLaw(x, {name: `${label}: ${falseExpr}`, expr: falseExpr}).law])
      expect(res.proven, `${label} must refute ${falseExpr}`).toBe(false)
      expect(res.run, `${label} counterexample for ${falseExpr}`).toBeDefined()
    }
    pinSteps(x, label, 'f', pin)
    native(proveRule(x.rule!, [...(x.invariants ?? []), buildLaw(x, {name: `${label}: n is 0 or 255`, expr: 'n == 0 or n == 255'}).law]), `${label}: n is 0 or 255`)
  }
  const signedCast = ok(c(S + 'static const int32_t T[4] = {[2] = (int8_t)255};\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 4) r->n = T[i]; }\n', 'ring'))
  const scFalse = proveRule(signedCast.rule!, [...(signedCast.invariants ?? []), buildLaw(signedCast, {name: 'int8-cast: n stays zero', expr: 'n == 0'}).law])
  expect(scFalse.proven).toBe(false)
  expect(scFalse.run).toBeDefined()
  pinSteps(signedCast, 'int8-cast', 'f', ['i == 2 implies n == -1', 'i >= 0 and i < 4 and i != 2 implies n == 0'])
  native(proveRule(signedCast.rule!, [...(signedCast.invariants ?? []), buildLaw(signedCast, {name: 'int8-cast: n is 0 or -1', expr: 'n == 0 or n == -1'}).law]), 'int8-cast: n is 0 or -1')

  // Exact u1 (K[i] * x) and u2 (x / (K[i] + 1)) must be refused statically (never collapsed to zero and failing only in checkC).
  const u1Mul = c(S + 'static const int32_t K[2] = {65536};\nvoid f(struct ring *r, int32_t i, int32_t x) { if (i >= 0 && i < 2 && x >= 0 && x < 65536) r->n = K[i] * x; }\n', 'ring')
  expect(u1Mul.ok).toBe(false)
  expect(u1Mul.refusals[0]!.what).toMatch(/product of two numbers|multiplies only by constants/)
  const u2Div = c(S + 'static const int32_t K[2] = {1};\nvoid f(struct ring *r, int32_t i, int32_t x) { if (i >= 0 && i < 2) r->n = x / (K[i] + 1); }\n', 'ring')
  expect(u2Div.ok).toBe(false)
  expect(u2Div.refusals[0]!.what).toMatch(/\/ by other than a constant/)

  // String-literal const tables, non-zero mutable static global arrays, and C++ non-zero array fields must be refused up front.
  const strTab = c(S + 'static const char T[8] = "hi";\nvoid f(struct ring *r, int32_t i) { if (i >= 0 && i < 8) r->n = T[i]; }\n', 'ring')
  expect(strTab.ok).toBe(false)
  expect(strTab.refusals[0]!.what).toMatch(/an entry that isn't a constant integer/)
  const nonZeroArr = c(H + 'static int32_t buf[4] = {9};\nstatic int32_t cur;\nvoid put(void) { cur = buf[0]; }\n', 'case')
  expect(nonZeroArr.ok).toBe(false)
  expect(nonZeroArr.refusals[0]!.what).toMatch(/an array initializer of a int32_t\[4\]/)
  const cppNonZeroArr = cpp('#include <cstdint>\nclass K {\n public:\n  int32_t buf[4] = {9};\n  int32_t n = 0;\n  void f() { n = buf[0]; }\n};\n', 'K')
  expect(cppNonZeroArr.ok).toBe(false)
  expect(cppNonZeroArr.refusals[0]!.what).toMatch(/an array initializer of a int32_t\[4\]/)

  // C++ static constexpr partial const table also reads array_filler in semantic order (both refutation and positive proofs).
  const cppTab = ok(cpp('#include <cstdint>\nclass K {\n public:\n  int32_t n = 0;\n  static constexpr int32_t T[16] = {0, 0, 9};\n  void f(int32_t i) { if (i >= 0 && i < 16) n = T[i]; }\n};\n', 'K'))
  const cppRes = proveRule(cppTab.rule!, [...(cppTab.invariants ?? []), buildLaw(cppTab, {name: 'cpp-constexpr: n stays zero', expr: 'n == 0'}).law])
  expect(cppRes.proven).toBe(false)
  expect(cppRes.run).toBeDefined()
  pinSteps(cppTab, 'cpp-constexpr', 'f', ['i == 2 implies n == 9', 'i >= 0 and i < 16 and i != 2 implies n == 0'])
  native(proveRule(cppTab.rule!, [...(cppTab.invariants ?? []), buildLaw(cppTab, {name: 'cpp-constexpr: n is 0 or 9', expr: 'n == 0 or n == 9'}).law]), 'cpp-constexpr: n is 0 or 9')
}, 180_000)
