// The C front end (core/extract-c.ts on core/c/reader.ts and Go's lowering): rules read from C through clang, each
// checked against the file it was read from (compiled with a generated harness, the undefined-behavior sanitizer
// trapping). The cases: unsigned wrap, signed overflow refused where the path doesn't exclude it, truncating division,
// a stated failure, assert and abort, a switch's fallthrough, ?: and an enum, and the refusals. Skipped without clang.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveRule, proveSteps} from './dsl.ts'
import {type COptions, extractC, extractCpp} from './extract-c.ts'

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
const step = (x: X, name: string, then: (b: A, a: A) => A, when?: (b: A) => A) => {
  const r = x.rule as A, v = proveSteps(r, x.invariants ?? [], [r.stepLaw(name, then, when)])
  if (!v.proven) throw new Error(`${name}: ${JSON.stringify({goal: v.goal, witness: v.witness})}`)
}

t('unsigned arithmetic wraps; a narrow one is promoted and converted back', () => {
  const x = ok(c(`
#include <stdint.h>
struct ctr { uint8_t lap; uint32_t total; unsigned short seq; };
void tick(struct ctr *c) { c->lap++; c->seq += 1; }
void add(struct ctr *c, uint32_t n) { c->total += n; }
`, 'ctr'))
  expect(x.notes.join('\n')).toMatch(/uint8_t: a result past its range wraps modulo 2\^8, as C's does/)
  step(x, 'a lap wraps at 256', (_b, a) => a.lap.eq(0), b => b.method.is('tick').and(b.lap.eq(255)))
  step(x, 'a total past 2^32 wraps', (b, a) => a.total.eq(b.total.plus(b.add_n).minus(4294967296)), b => b.method.is('add').and(b.total.plus(b.add_n).atLeast(4294967296)))
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
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('hits at most 1000 once there', ({hits}: A) => hits.atMost(2147483647))]).proven).toBe(true)
  step(x, 'guarded counts to 1000', (b, a) => a.hits.eq(b.hits.plus(1)), b => b.method.is('guarded').and(b.hits.lt(1000)))
}, 60_000)

t('division and remainder truncate toward zero; by zero it is refused', () => {
  const x = ok(c(`
struct h { int half; int rest; int v; };
void split(struct h *s, int k) { s->v = k; s->half = k / 2; s->rest = k % 2; }
`, 'h'))
  step(x, 'the half and the rest make k again', (_b, a) => a.half.plus(a.half).plus(a.rest).eq(a.v), b => b.method.is('split'))
  step(x, 'the rest takes the sign of k', (b, a) => a.rest.atMost(0), b => b.method.is('split').and(b.split_k.lt(0)))
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
  step(x, 'a take never goes below 0', (b, a) => a.tokens.eq(b.tokens.minus(b.take_n)), b => b.method.is('take'))
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('tokens within cap', ({tokens, cap}: A) => tokens.atMost(cap))]).proven).toBe(true)
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
  step(x, 'a failure half open trips it', (_b, a) => a.st.eq(1).and(a.tripped), b => b.method.is('fail').and(b.st.eq(2)))
  step(x, 'a success closes a half-open breaker', (_b, a) => a.st.eq(0).and(a.fails.eq(0)), b => b.method.is('ok').and(b.st.eq(2)))
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
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('at most 8 held', ({count}: A) => count.atMost(8))]).proven).toBe(true)
  step(x, 'a put keeps its item at the head', (b, a) => a.buf.at(b.head).eq(b.rb_put_x), b => b.method.is('rb_put').and(b.count.lt(8)).and(b.head.lt(8)))
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
  step(x, 'a dequeue gives the item at the tail', (b, a) => a.rb_dequeue_data.eq(b.buf.at(b.tail)), b => b.method.is('rb_dequeue').and(b.tail.lt(16)))
}, 60_000)

t('refused where it leaves the subset, each with why', () => {
  const why = (code: string, entry: string) => { const r = c(code, entry, {strict: true}); expect(r.ok).toBe(false); return r.refusals[0]!.what }
  expect(why('struct q { int n; };\nvoid f(struct q *q) { while (q->n > 0) q->n--; }\n', 'q')).toMatch(/a loop \(while\)/)
  expect(why('int g;\nstruct q { int n; };\nvoid f(struct q *q) { q->n = g; }\n', 'q')).toMatch(/a global variable/)
  expect(why('#include <string.h>\nstruct q { unsigned n; };\nvoid f(struct q *q) { q->n = strlen("ab"); }\n', 'q')).toMatch(/another file or library|a string/)
  expect(why('struct q { unsigned n; };\nvoid f(struct q *q, unsigned k) { q->n = q->n / k; }\n', 'q')).toMatch(/other than a constant/)
  expect(why('struct q { unsigned n; };\nvoid f(struct q *q, unsigned k) { q->n = q->n ^ k; }\n', 'q')).toMatch(/a bit operation/)
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
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('never more tokens than the capacity', ({tokens_, cap_}: A) => tokens_.atMost(cap_))]).proven).toBe(true)
  step(x, 'a take is all or nothing', (b, a) => a.take_result.implies(a.tokens_.eq(b.tokens_.minus(b.take_n))), b => b.method.is('take'))
  step(x, 'a pop gives the item and clears it', (b, a) => a.pop_out.eq(b.hits_.at(1)).and(a.hits_.at(1).eq(0)), b => b.method.is('pop').and(b.hits_.at(1).eq(0).not()))
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
  expect(proveRule(x.rule!, [...x.invariants!, x.rule!.law('the cap is three', ({cap_}: A) => cap_.eq(3))]).proven).toBe(true)
}, 60_000)

t('C++: refused where it leaves the subset, each with why', () => {
  const why = (code: string) => { const r = cpp(code, 'K'); expect(r.ok).toBe(false); return r.refusals[0]!.what }
  expect(why('struct K { int n = 0; virtual void v() { n++; } void f() { v(); } };\n')).toMatch(/virtual/)
  expect(why('#include <vector>\nstruct K { std::vector<int> xs; int n = 0; void f() { n = (int)xs.size(); } };\n')).toMatch(/another class|other code/)
  expect(why('struct K { int n = 0; void f() { auto g = [this] { n++; }; g(); } };\n')).toMatch(/subset|other code|lambda|another class/)
  expect(why('struct K { int n = 0; void f() { try { n++; } catch (...) {} } };\n')).toMatch(/try and catch/)
  expect(why('template <class T> struct K { T n; void f() { n++; } };\nK<int> k;\n')).toMatch(/class template/)
}, 60_000)

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
  step(x, 'never past its cap', (_b, a) => a.used.atMost(a.cap), b => b.used.atMost(b.cap))
})
