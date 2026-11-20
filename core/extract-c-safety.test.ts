// C memory & UB safety tests (Stage 1): first-fault model, pre-lowering site accounting,
// Astra soundness controls, off-by-one corpus mutants with ASan/UBSan replay, and CLI opt-in.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {proveLaws} from '../kernel/prove.ts'
import {check} from './cli.ts'
import {clangDump, readC} from './c/reader.ts'
import {analyzeCSafety, cSafetyArtifactOf, verifyCSafetyProof, type CSafetyProofBundle} from './c/safety.ts'
import {bool, rule} from './dsl.ts'
import {extractC, type COptions} from './extract-c.ts'
import {readGo} from './extract-go.ts'
import {Refusal} from './extract-read.ts'
import {interpret} from './machine.ts'
import {allowed} from './watch.ts'

const hasClang = (() => { try { execFileSync('clang', ['--version'], {stdio: 'ignore'}); return true } catch { return false } })()
const withClang = hasClang ? test : test.skip

const analyze = (code: string, given: COptions = {}, filename = 'ring.c') => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-'))
  try {
    const file = join(dir, filename)
    writeFileSync(file, code)
    return extractC(file, {entry: 'ring', ...given, safety: true})
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}

// --- 1. Eight-slot ring buffer cases (brief-csafety.md) ------------------------------------------------------------------

const RB8 = (putWrap: string, extra = '') => `#include <stdint.h>
#define N 8
struct rb { uint8_t buf[N]; uint32_t head, tail, count; };
int rb_put(struct rb *r, uint8_t x) { if (r->count == N) return -1; r->buf[r->head] = x; ${putWrap} r->count++; return 0; }
${extra}
`
const RB8_GET = 'int rb_get(struct rb *r) { if (r->count == 0) return -1; int x = r->buf[r->tail]; r->tail = (r->tail + 1) % N; r->count--; return x; }'

withClang('8-slot ring buffer: guarded modulo and mask wraps prove safe with checkLaws', () => {
  for (const wrap of ['r->head = (r->head + 1) % N;', 'r->head = (r->head + 1) & (N - 1);']) {
    const x = analyze(RB8(wrap, RB8_GET), {entry: 'rb', fails: {rb_put: '< 0', rb_get: '< 0'}}, 'rb.c')
    expect(x.ok, JSON.stringify(x.refusals)).toBe(true)
    expect(x.safety?.status).toBe('proven')
    const bounds = x.safety!.issues.filter(o => o.kind === 'bounds').map(o => o.where)
    expect(bounds.length).toBe(2)
    expect(x.safety!.issues.every(i => i.status === 'proven')).toBe(true)
    const art = cSafetyArtifactOf(x.safety!)
    expect(art?.jointProof).toBeDefined()
    expect(verifyCSafetyProof(art!.machine, art!.targetLaws, art!.jointProof)).toBe(true)
  }
}, 60_000)

withClang('8-slot ring buffer: off-by-one (i > N) flips to broken with UBSan report at site', () => {
  const code = RB8(
    'r->head = (r->head + 1) % N;',
    'int rb_set(struct rb *r, uint32_t i, uint8_t v) { if (i > N) return -1; r->buf[i] = v; return 0; }',
  )
  const x = analyze(code, {entry: 'rb', fails: {rb_put: '< 0', rb_set: '< 0'}}, 'rb.c')
  expect(x.ok).toBe(false)
  expect(x.safety?.status).toBe('broken')
  const putIssue = x.safety!.issues.find(o => o.kind === 'bounds' && o.where.startsWith('rb.c:4:'))
  const setIssue = x.safety!.issues.find(o => o.kind === 'bounds' && o.where.startsWith('rb.c:5:'))
  expect(putIssue?.status).toBe('proven')
  expect(setIssue?.status).toBe('broken')
  expect(setIssue?.replay?.built).toBe(true)
  expect(setIssue?.replay?.matchedSite).toBe(true)
  expect(setIssue?.replay?.reports.join('\n')).toMatch(/rb\.c:5:\d+: runtime error: index 8 out of bounds for type 'uint8_t\[8\]'/)
}, 60_000)

withClang('8-slot ring buffer: head reset bug (head > N) found by search and replayed under UBSan', () => {
  const x = analyze(
    RB8('r->head = r->head + 1; if (r->head > N) r->head = 0;', RB8_GET),
    {entry: 'rb', fails: {rb_put: '< 0', rb_get: '< 0'}},
    'rb.c',
  )
  expect(x.ok).toBe(false)
  expect(x.safety?.status).toBe('broken')
  const putIssue = x.safety!.issues.find(o => o.kind === 'bounds' && o.where.startsWith('rb.c:4:'))
  const getIssue = x.safety!.issues.find(o => o.kind === 'bounds' && o.where.startsWith('rb.c:5:'))
  expect(getIssue?.status).toBe('proven')
  expect(putIssue?.status).toBe('broken')
  expect(putIssue?.replay?.built).toBe(true)
  expect(putIssue?.replay?.matchedSite).toBe(true)
  expect(putIssue?.replay?.requests.length).toBeGreaterThanOrEqual(10)
  expect(putIssue?.replay?.reports.join('\n')).toMatch(/rb\.c:4:\d+: runtime error: index 8 out of bounds for type 'uint8_t\[8\]'/)
}, 90_000)

// --- 2. Overflow, division/remainder, first-fault ordering, and constant tables ------------------------------------------

withClang('C Safety checks guarded cursor, records AST positions, and refuses uncovered constructs', () => {
  const safe = analyze(`struct ring { int head; int slots[8]; };
int rotate(struct ring *r) {
  if (r->head < 0 || r->head >= 8) return 0;
  int saved = r->slots[r->head];
  r->slots[r->head] = 1;
  if (r->head == 7) r->head = 0;
  else r->head = r->head + 1;
  return saved;
}
`)
  expect(safe.safety?.status, JSON.stringify(safe.refusals)).toBe('proven')
  const positions = safe.safety!.issues.filter(o => o.kind === 'bounds').map(o => o.where.replace(/#\d+$/, '')).sort()
  expect(positions).toEqual(['ring.c:4:15', 'ring.c:5:3'])

  const loop = analyze(`struct ring { int head; int slots[8]; };
void reset(struct ring *r) {
  while (r->head != 0) r->head = 0;
}
`)
  expect(loop.safety?.status).toBe('unchecked')
  expect(loop.refusals.map(r => r.what).join('; ')).toMatch(/loop|while/i)
}, 60_000)

withClang('C Safety never lets a later configured refusal hide INT_MIN % -1 and replays UBSan', () => {
  const x = analyze(`struct ring { int head; };
int update(struct ring *r, int x) {
  int v = x % -1;
  (void)v;
  return -1;
}
`, {fails: {update: '== -1'}})
  expect(x.safety?.status, JSON.stringify(x.refusals)).toBe('broken')
  const div = x.safety!.issues.find(o => o.kind === 'division')
  expect(div?.status).toBe('broken')
  expect(div?.where).toMatch(/ring\.c:3:/)
  expect(div?.replay?.built).toBe(true)
  expect(div?.replay?.matchedSite).toBe(true)
  expect(div?.replay?.reports.join('\n')).toMatch(/ring\.c:3:\d+: runtime error: division of -2147483648 by -1 cannot be represented in type 'int'/)

  // A configured refusal AFTER mutating state must be refused as unchecked (never discarded).
  const writeBeforeFail = analyze(`struct ring { int head; };
int update(struct ring *r, int x) {
  r->head = x % -1;
  return -1;
}
`, {fails: {update: '== -1'}})
  expect(writeBeforeFail.ok).toBe(false)
  expect(writeBeforeFail.safety?.status).toBe('unchecked')
}, 60_000)

withClang('C Safety checks signed overflow and division ordering with UBSan replay', () => {
  const exact = analyze(`struct ring { int head; };
void move(struct ring *r) { r->head = 1 + 2; }
`)
  expect(exact.safety?.status).toBe('proven')
  expect(exact.safety?.issues).toContainEqual({kind: 'overflow', where: expect.stringMatching(/ring\.c:2:/), status: 'proven'})

  const ovf = analyze(`struct ring { int hits; };
void add(struct ring *r, int k) { r->hits = r->hits + k; }
`)
  expect(ovf.safety?.status).toBe('broken')
  const ovfIssue = ovf.safety!.issues.find(o => o.kind === 'overflow')
  expect(ovfIssue?.status).toBe('broken')
  expect(ovfIssue?.replay?.matchedSite).toBe(true)
  expect(ovfIssue?.replay?.reports.join('\n')).toMatch(/ring\.c:2:\d+: runtime error: signed integer overflow/)

  const ordered = analyze(`struct ring { int head; };
void move(struct ring *r, int n) {
  int value = n / 0;
  r->head = value % -1;
}
`)
  const divisions = ordered.safety!.issues.filter(s => s.kind === 'division')
  expect(divisions.length).toBe(2)
  expect(divisions[0]).toMatchObject({kind: 'division', where: expect.stringMatching(/ring\.c:3:/), status: 'broken'})
  expect(divisions[0]!.replay?.reports.join('\n')).toMatch(/ring\.c:3:\d+: runtime error: division by zero/)
  expect(divisions[1]).toMatchObject({kind: 'division', where: expect.stringMatching(/ring\.c:4:/), status: 'proven'})
}, 60_000)

// --- 3. Off-by-one mutants of every bounds check in the C safety corpus (0 false positives) ------------------------------

type BoundsCase = {
  id: string,
  entry: string,
  file: string,
  code: string,
  opts?: COptions,
  mutants: {name: string, from: string, to: string, siteLine: number}[],
}

const BOUNDS_CORPUS: BoundsCase[] = [
  {
    id: 'ring-buffer-mod8',
    entry: 'rb',
    file: 'rb.c',
    code: `#include <stdint.h>
#define N 8
struct rb { uint8_t buf[N]; uint32_t head, tail, count; };
int rb_put(struct rb *r, uint8_t x) { if (r->count == N) return -1; r->buf[r->head] = x; r->head = (r->head + 1) % N; r->count++; return 0; }
int rb_get(struct rb *r) { if (r->count == 0) return -1; int x = r->buf[r->tail]; r->tail = (r->tail + 1) % N; r->count--; return x; }
int rb_set(struct rb *r, uint32_t i, uint8_t v) { if (i >= N) return -1; r->buf[i] = v; return 0; }
`,
    opts: {fails: {rb_put: '< 0', rb_get: '< 0', rb_set: '< 0'}},
    mutants: [
      {name: 'rb_set i >= N -> i > N', from: 'if (i >= N)', to: 'if (i > N)', siteLine: 6},
      {name: 'rb_put wrap % N -> % (N + 1)', from: '(r->head + 1) % N', to: '(r->head + 1) % (N + 1)', siteLine: 4},
      {name: 'rb_get wrap % N -> % (N + 1)', from: '(r->tail + 1) % N', to: '(r->tail + 1) % (N + 1)', siteLine: 5},
    ],
  },
  {
    id: 'ring-buffer-mask16-helpers-outparam',
    entry: 'rb_t',
    file: 'ringbuf.c',
    code: `#include <stdint.h>
#include <stdbool.h>
#define N 16
typedef struct { uint8_t buf[N]; uint8_t head, tail; } rb_t;
static inline uint8_t rb_num_items(rb_t *r) { return (uint8_t)((r->head - r->tail) & (N - 1)); }
static inline bool rb_full(rb_t *r) { return rb_num_items(r) == (N - 1); }
static inline bool rb_empty(rb_t *r) { return r->head == r->tail; }
void rb_queue(rb_t *r, uint8_t x) { if (rb_full(r)) r->tail = (uint8_t)((r->tail + 1) & (N - 1)); r->buf[r->head] = x; r->head = (uint8_t)((r->head + 1) & (N - 1)); }
uint8_t rb_dequeue(rb_t *r, uint8_t *data) { if (rb_empty(r)) return 0; *data = r->buf[r->tail]; r->tail = (uint8_t)((r->tail + 1) & (N - 1)); return 1; }
uint8_t rb_peek(rb_t *r, uint8_t *data, uint8_t idx) { if (idx >= N) return 0; *data = r->buf[idx]; return 1; }
`,
    opts: {fails: {rb_dequeue: '== 0', rb_peek: '== 0'}},
    mutants: [
      {name: 'rb_peek idx >= N -> idx > N', from: 'if (idx >= N)', to: 'if (idx > N)', siteLine: 10},
      {name: 'rb_queue head mask & 15 -> & 31', from: 'r->head = (uint8_t)((r->head + 1) & (N - 1))', to: 'r->head = (uint8_t)((r->head + 1) & 31)', siteLine: 8},
    ],
  },
  {
    id: 'bounded-signed-stack',
    entry: 'stk',
    file: 'stk.c',
    code: `struct stk { int items[6]; int top; };
int push(struct stk *s, int v) {
  if (s->top < 0 || s->top >= 6) return -1;
  s->items[s->top] = v;
  s->top = s->top + 1;
  return 0;
}
int peek(struct stk *s, int idx) {
  if (idx < 0 || idx >= 6) return -1;
  return s->items[idx];
}
`,
    opts: {fails: {push: '< 0', peek: '< 0'}},
    mutants: [
      {name: 'push top >= 6 -> top > 6', from: 's->top >= 6', to: 's->top > 6', siteLine: 4},
      {name: 'peek idx >= 6 -> idx > 6', from: 'idx >= 6', to: 'idx > 6', siteLine: 10},
      {name: 'peek idx < 0 -> idx < -1', from: 'idx < 0', to: 'idx < -1', siteLine: 10},
    ],
  },
  {
    id: 'const-table-1d-2d',
    entry: 'lut',
    file: 'lut.c',
    code: `struct lut { int last; };
static const int weights[4] = {10, 20, 30, 40};
static const int grid[2][4] = {{1, 2, 3, 4}, {5, 6, 7, 8}};
int lookup1(struct lut *s, int i) {
  if (i < 0 || i >= 4) return -1;
  s->last = weights[i];
  return s->last;
}
int lookup2(struct lut *s, int r, int c) {
  if (r < 0 || r >= 2 || c < 0 || c >= 4) return -1;
  s->last = grid[r][c];
  return s->last;
}
`,
    opts: {fails: {lookup1: '< 0', lookup2: '< 0'}},
    mutants: [
      {name: 'weights i >= 4 -> i > 4', from: 'i >= 4', to: 'i > 4', siteLine: 6},
      {name: 'weights i < 0 -> i < -1', from: 'i < 0', to: 'i < -1', siteLine: 6},
      {name: 'grid r >= 2 -> r > 2', from: 'r >= 2', to: 'r > 2', siteLine: 11},
      {name: 'grid c >= 4 -> c > 4', from: 'c >= 4', to: 'c > 4', siteLine: 11},
    ],
  },
  {
    id: 'globals-mode-fixed-array',
    entry: 'gbuf',
    file: 'gbuf.c',
    code: `static int buf[4];
static int cursor = 1;
int write_cur(int v) {
  buf[cursor] = v;
  cursor = cursor + 1;
  if (cursor == 4) cursor = 0;
  return 0;
}
int read_at(int i) {
  if (i < 0 || i >= 4) return -1;
  return buf[i];
}
`,
    opts: {fails: {read_at: '< 0'}},
    mutants: [
      {name: 'read_at i >= 4 -> i > 4', from: 'i >= 4', to: 'i > 4', siteLine: 11},
      {name: 'write_cur cursor == 4 -> cursor > 4', from: 'if (cursor == 4)', to: 'if (cursor > 4)', siteLine: 4},
    ],
  },
]

for (const item of BOUNDS_CORPUS) {
  withClang(`corpus bounds-check control (${item.id}): unmutated proves clear (0 FP); off-by-one mutants break with UBSan at site`, () => {
    const clean = analyze(item.code, {entry: item.entry, ...item.opts}, item.file)
    expect(clean.ok, `${item.id} unmutated failed: ${JSON.stringify(clean.refusals)}`).toBe(true)
    expect(clean.safety?.status, `${item.id} unmutated status`).toBe('proven')
    const art = cSafetyArtifactOf(clean.safety!)
    expect(art?.jointProof, `${item.id} missing proof`).toBeDefined()
    expect(verifyCSafetyProof(art!.machine, art!.targetLaws, art!.jointProof), `${item.id} checkLaws`).toBe(true)

    for (const mut of item.mutants) {
      expect(item.code.includes(mut.from), `${item.id}/${mut.name}: pattern missing`).toBe(true)
      const mutated = analyze(item.code.replace(mut.from, mut.to), {entry: item.entry, ...item.opts}, item.file)
      expect(mutated.ok, `${item.id}/${mut.name}: expected refusal`).toBe(false)
      expect(mutated.safety?.status, `${item.id}/${mut.name}: expected broken`).toBe('broken')
      const targetPrefix = `${item.file}:${mut.siteLine}:`
      const hit = mutated.safety!.issues.find(o => o.kind === 'bounds' && o.status === 'broken' && o.where.startsWith(targetPrefix))
      expect(hit, `${item.id}/${mut.name}: expected broken bounds at ${targetPrefix}, got ${JSON.stringify(mutated.safety!.issues)}`).toBeDefined()
      expect(hit!.replay?.built).toBe(true)
      expect(hit!.replay?.matchedSite).toBe(true)
      expect(hit!.replay?.reports.join('\n')).toMatch(/out of bounds/)
    }
  }, 180_000)
}

// --- 4. Astra Review Finding 1: Globals linkage chain & tentative declarations -------------------------------------------

withClang('Astra Finding 1: tentative global with later defining initializer (previousDecl) is refused as unchecked', () => {
  // Exact Astra fixture: read_g references the tentative VarDecl ID, while a later unreferenced
  // VarDecl in the same linkage chain supplies the nonzero initializer `10` (out of bounds for arr[8]).
  const tentative = analyze(`static int idx;
static int arr[8];
int read_g(void) {
  return arr[idx];
}
static int idx = 10;
`, {entry: 'tent'}, 'tent.c')
  expect(tentative.ok).toBe(false)
  expect(tentative.safety?.status).toBe('unchecked')
  expect(tentative.refusals.map(r => r.what).join('; ')).toMatch(/multiple declarations in its linkage chain/)

  // Single-declaration nonzero initializer: in-range proves clear, out-of-range breaks with UBSan replay.
  const okInit = analyze(`static int idx = 2;
static int arr[8];
int read_g(void) { return arr[idx]; }
`, {entry: 'okinit'}, 'okinit.c')
  expect(okInit.safety?.status).toBe('proven')

  const badInit = analyze(`static int idx = 8;
static int arr[8];
int read_g(void) { return arr[idx]; }
`, {entry: 'badinit'}, 'badinit.c')
  expect(badInit.safety?.status).toBe('broken')
  expect(badInit.safety!.issues[0]?.replay?.reports.join('\n')).toMatch(/index 8 out of bounds/)
}, 60_000)

// --- 5. Astra Review Finding 2: Declarators, pre-lowering inventory, and mutant accounting -------------------------------

withClang('Astra Finding 2a: array-form, VLA, typedef-array, and macro-spelled receiver declarators are unchecked', () => {
  const cases: [string, string][] = [
    ['array-form receiver', `struct ring { int slots[8]; };
void f(struct ring r[1], int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }
`],
    ['VLA receiver', `struct ring { int slots[8]; };
void f(struct ring r[static 1], int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }
`],
    ['typedef-array receiver', `struct ring { int slots[8]; };
typedef struct ring ring_arr[1];
void f(ring_arr r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }
`],
    ['macro-spelled receiver', `struct ring { int slots[8]; };
#define BAD_RECV struct ring r[1]
void f(BAD_RECV, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }
`],
  ]
  for (const [label, code] of cases) {
    const res = analyze(code)
    expect(res.ok, `${label} must not succeed`).toBe(false)
    expect(res.safety?.status, `${label} must be unchecked`).toBe('unchecked')
  }

  // Positive control: plain pointer typedef IS accepted and proven.
  const okTypedef = analyze(`struct ring { int slots[8]; };
typedef struct ring *ring_ptr;
void f(ring_ptr r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }
`)
  expect(okTypedef.safety?.status).toBe('proven')
}, 60_000)

withClang('Astra Finding 2b: pre-lowering site accounting catches dropped/uncut IDs while allowing genuinely dead sites', () => {
  // Positive dead-site check: dead branch, short-circuited RHS, and post-return statement prove clear.
  const deadSites = analyze(`struct ring { int slots[8]; int out; };
int f(struct ring *r, int i) {
  if (0) { r->slots[i] = 1; }
  if (0 && (i / 0)) { r->out = 1; }
  if (i >= 0 && i < 8) return r->slots[i];
  return 0;
  r->out = r->slots[i];
}
`)
  expect(deadSites.safety?.status, JSON.stringify(deadSites.refusals)).toBe('proven')
  expect(deadSites.safety!.issues.length).toBeGreaterThanOrEqual(4)

  // Mutant checks directly on readGo(..., {safety: true}):
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-acct-'))
  try {
    const file = join(dir, 'two.c')
    writeFileSync(file, `struct ring { int slots[8]; };
void put2(struct ring *r, int i, int j) {
  if (i >= 0 && i < 8) r->slots[i] = 1;
  if (j >= 0 && j < 8) r->slots[j] = 2;
}
`)
    const {tu, target} = clangDump(file, [])
    // Mutant A: discard one of two source site IDs from the lowered AST while keeping both in safetySites.
    const c1 = readC(file, 'ring', structuredClone(tu), target, false, undefined, {}, [], [], [], true)
    const fn1 = c1.pkg.funcs.find(f => f.name === 'put2')!
    expect(fn1.safetySites?.length).toBe(2)
    // Remove the second `if` statement from the lowered body without updating safetySites.
    fn1.body = fn1.body!.slice(0, 1)
    expect(() => readGo(c1.pkg, {entry: 'ring', methods: ['put2'], strict: true, safety: true})).toThrow(Refusal)

    // Mutant B: pre-register an extra source ID on fn.safetySites without any cut on a live path.
    const c2 = readC(file, 'ring', structuredClone(tu), target, false, undefined, {}, [], [], [], true)
    const fn2 = c2.pkg.funcs.find(f => f.name === 'put2')!
    fn2.safetySites = [...(fn2.safetySites ?? []), {where: 'two.c:99:1', kind: 'bounds'}]
    expect(() => readGo(c2.pkg, {entry: 'ring', methods: ['put2'], strict: true, safety: true})).toThrow(Refusal)
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 60_000)

// --- 6. Astra Review Finding 3: Natural remainder/product in signed int receiver & safetyBounds widening -----------------

withClang('Astra Finding 3: natural modk and mul in signed subtraction stay Int.minus (inline, hoisted, and in branch guard)', () => {
  // Inline and hoisted (x % 8) - b < 0, plus inside a branch guard:
  // when r = x % 8 = 2 and b = 5, r - b MUST be -3 < 0 (never truncated to 0 by Term.minus).
  const modCase = analyze(`#include <stdint.h>
struct ring { int diff; int neg; int slots[8]; };
void calc(struct ring *s, uint32_t x, uint16_t b) {
  int r = (int)(x % 8u);
  int d = r - (int)b;
  s->diff = d;
  if (((int)(x % 8u) - (int)b) < 0) {
    int d2 = (int)(x % 8u) - (int)b;
    s->neg = 1;
    s->slots[0] = d2;
  } else {
    s->neg = 0;
  }
}
`)
  expect(modCase.safety?.status, JSON.stringify(modCase.refusals)).toBe('proven')
  const modArt = cSafetyArtifactOf(modCase.safety!)!
  const gMod = modArt.rule.compiled(), pMod = modArt.rule.encodeParams({})
  const s0Mod = gMod.init(pMod)
  // Concrete oracle: x = 10 -> r = 10 % 8 = 2; b = 5 -> r - b = -3 < 0!
  const s1Mod = modArt.rule.decode(gMod.step(pMod, s0Mod, modArt.rule.encodeInput({method: 'calc', calc_x: 10, calc_b: 5})))
  expect(s1Mod.diff).toBe(-3)
  expect(s1Mod.neg).toBe(1)
  // Concrete oracle: x = 14 -> r = 6; b = 2 -> r - b = 4 >= 0!
  const s2Mod = modArt.rule.decode(gMod.step(pMod, s0Mod, modArt.rule.encodeInput({method: 'calc', calc_x: 14, calc_b: 2})))
  expect(s2Mod.diff).toBe(4)
  expect(s2Mod.neg).toBe(0)

  // Promoted narrow products (safetyBounds interval preservation):
  // uint8_t * uint8_t in int has exact range [0, 65025] -> proven without false inexact refusal.
  // Also tests product of two naturals in signed subtraction (a * b - c < 0).
  const u8Prod = analyze(`#include <stdint.h>
struct ring { int diff; int neg; };
void prod(struct ring *s, uint8_t a, uint8_t b, uint8_t c) {
  int d = (int)a * (int)b - (int)c;
  s->diff = d;
  s->neg = (((int)a * (int)b - (int)c) < 0) ? 1 : 0;
}
`)
  expect(u8Prod.safety?.status, JSON.stringify(u8Prod.refusals)).toBe('proven')
  const u8Art = cSafetyArtifactOf(u8Prod.safety!)!
  const gU8 = u8Art.rule.compiled(), pU8 = u8Art.rule.encodeParams({})
  const stU8 = u8Art.rule.decode(gU8.step(pU8, gU8.init(pU8), u8Art.rule.encodeInput({method: 'prod', prod_a: 2, prod_b: 3, prod_c: 10})))
  expect(stU8.diff).toBe(-4)
  expect(stU8.neg).toBe(1)

  // uint16_t * uint16_t in int has exact mathematical range [0, 4294836225] <= 2^53 - 1,
  // which CAN exceed INT_MAX (2147483647): unguarded breaks with UBSan, guarded proves clear!
  const u16Bad = analyze(`#include <stdint.h>
struct ring { int out; };
void prod16(struct ring *s, uint16_t a, uint16_t b) {
  s->out = (int)a * (int)b;
}
`)
  expect(u16Bad.safety?.status).toBe('broken')
  expect(u16Bad.safety!.issues.find(o => o.kind === 'overflow')?.replay?.reports.join('\n')).toMatch(/signed integer overflow/)

  const u16Safe = analyze(`#include <stdint.h>
struct ring { int out; };
void prod16(struct ring *s, uint16_t a, uint16_t b) {
  if (a <= 46340u && b <= 46340u) s->out = (int)a * (int)b;
}
`)
  expect(u16Safe.safety?.status).toBe('proven')
}, 60_000)

// --- 7. Astra Review Findings 4 & 5: Lowering + Monitor + Printed Machine Boolean-Table Integration & Proof Tamper --------

withClang('Astra Integration: two-level branch, short-circuit &&, later refusal, fixed array framing, and checkLaws tamper', () => {
  // Real C lowering + monitorCSafety + printed machine:
  // - Arithmetic guard with short-circuited RHS (`flag && (a / d > 0)`)
  // - Two-level branch with distinct normal writes and fixed-array write
  // - Later normal configured refusal (`fails: {step: '== -1'}`)
  const code = `struct ring { int data; int slots[2]; };
int step(struct ring *r, int flag, int idx, int fail) {
  if (flag && (r->slots[idx] >= 0)) {
    if (fail) return -1;
    r->slots[0] = 7;
    r->data = 11;
    return 1;
  } else {
    if (fail) return -1;
    r->slots[1] = 9;
    r->data = 22;
    return 2;
  }
}
`
  const x = analyze(code, {fails: {step: '== -1'}})
  expect(x.safety?.status).toBe('broken')
  const art = cSafetyArtifactOf(x.safety!)!
  const g = art.rule.compiled(), run = interpret(art.machine), p = art.rule.encodeParams({})
  const alarmName = Object.keys(art.rule.decode(g.init(p))).find(k => k.startsWith('cSafetyAlarm'))!
  expect(alarmName).toBeDefined()

  // Build two states: clear state (with nondefault data=5, result=3, slots=[4,6], alarm=false)
  // and already-faulted state (alarm=true, same nondefault slots).
  const baseInit = g.init(p)
  const mkState = (alarmOn: boolean) => {
    const s = {
      scalars: {...baseInit.scalars},
      maps: Object.fromEntries(Object.entries(baseInit.maps).map(([k, v]) => [k, new Map(v)])),
    }
    // data is signed Int (pos/neg), step_result is signed Int, slots is fixed list map of signed Ints
    s.scalars.data = 5; s.scalars['data$neg'] = 0
    s.scalars.step_result = 3; s.scalars['step_result$neg'] = 0
    s.scalars[alarmName] = alarmOn ? 1 : 0
    s.maps.slots = new Map([[0, 4], [1, 6]])
    s.maps['slots$neg'] = new Map([[0, 0], [1, 0]])
    return s
  }

  for (const priorAlarm of [false, true]) {
    for (const flag of [0, 1]) {
      for (const idx of [-1, 0, 1, 2]) {
        for (const fail of [0, 1]) {
          const st = mkState(priorAlarm)
          const inp = art.rule.encodeInput({method: 'step', step_flag: flag, step_idx: idx, step_fail: fail})
          const hit = !priorAlarm && flag === 1 && (idx < 0 || idx >= 2)
          const normalAllowed = !priorAlarm && !hit && fail === 0
          const shouldStep = priorAlarm || hit || normalAllowed
          const isAllowed = allowed(art.machine, run, p, st, inp)
          expect(isAllowed, `prior=${priorAlarm} flag=${flag} idx=${idx} fail=${fail}`).toBe(shouldStep)
          if (!shouldStep) continue
          const nx = art.rule.decode(g.step(p, st, inp))
          if (priorAlarm || hit) {
            // Sticky alarm, exact stutter of old scalar, nondefault result, both fixed cells and length!
            expect(nx[alarmName]).toBe(true)
            expect(nx.data).toBe(5)
            expect(nx.step_result).toBe(3)
            expect(nx.slots).toEqual([4, 6])
            expect(nx.slots_len).toBe(2)
          } else if (flag === 1) {
            // Taken then-branch (slots[idx] is 4 or 6, both >= 0)
            expect(nx[alarmName]).toBe(false)
            expect(nx.data).toBe(11)
            expect(nx.step_result).toBe(1)
            expect(nx.slots).toEqual([7, 6])
            expect(nx.slots_len).toBe(2)
          } else {
            // Short-circuited RHS (flag == 0): even with idx == -1 or 2, no fault, else-branch runs!
            expect(nx[alarmName]).toBe(false)
            expect(nx.data).toBe(22)
            expect(nx.step_result).toBe(2)
            expect(nx.slots).toEqual([4, 9])
            expect(nx.slots_len).toBe(2)
          }
        }
      }
    }
    // Failed type-domain check: out-of-range int32 input (> 2147483647) MUST remain refused even when idx is OOB!
    const badDomainInp = art.rule.encodeInput({method: 'step', step_flag: 1, step_idx: 2147483648, step_fail: 0})
    expect(allowed(art.machine, run, p, mkState(priorAlarm), badDomainInp)).toBe(false)
  }

  // Independent checkLaws verification control: accept intact proof, reject missing or damaged proof.
  const proven = analyze(`struct ring { int slots[4]; };
void set(struct ring *r, int i) { if (i >= 0 && i < 4) r->slots[i] = 1; }
`)
  expect(proven.safety?.status).toBe('proven')
  const pArt = cSafetyArtifactOf(proven.safety!)!
  expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, pArt.jointProof)).toBe(true)
  expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, undefined)).toBe(false)
  if (pArt.jointProof?.kind === 'usual') {
    const damagedTrees: CSafetyProofBundle = {
      ...pArt.jointProof,
      proof: {...pArt.jointProof.proof, trees: {}},
    }
    expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, damagedTrees)).toBe(false)
    const missingTarget: CSafetyProofBundle = {
      ...pArt.jointProof,
      laws: pArt.jointProof.laws.filter(l => !pArt.targetLaws.some(t => t.name === l.name)),
    }
    expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, missingTarget)).toBe(false)
    const wrongMachine: CSafetyProofBundle = {
      ...pArt.jointProof,
      machine: {...pArt.jointProof.machine, assume: {op: '<', a: {op: 'const', value: 1}, b: {op: 'const', value: 0}}},
    }
    expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, wrongMachine)).toBe(false)
    const wrongFailure: CSafetyProofBundle = {
      ...pArt.jointProof,
      machine: {...pArt.jointProof.machine, primitiveFailure: {op: '=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}},
    }
    expect(verifyCSafetyProof(pArt.machine, pArt.targetLaws, wrongFailure)).toBe(false)
  }
}, 60_000)

// --- 8. CLI opt-in (`// gdp: safety`), gdp.toml override refusal, and default path preservation ---------------------------

withClang('CLI opt-in // gdp: safety returns exit 0 (proven), 1 (broken+UBSan), 2 (unchecked); default path unchanged', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-cli-'))
  try {
    const safeFile = join(dir, 'safe.c')
    writeFileSync(safeFile, '// gdp: safety\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n')
    const rSafe = await check([safeFile], {entry: 'ring', propose: false})
    expect(rSafe.exit).toBe(0)
    expect(rSafe.rules[0]?.safety).toMatchObject({status: 'proven'})

    const brokenFile = join(dir, 'broken.c')
    writeFileSync(brokenFile, '// gdp: safety\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i <= 8) r->slots[i] = 1; }\n')
    const rBroken = await check([brokenFile], {entry: 'ring', propose: false})
    expect(rBroken.exit).toBe(1)
    expect(rBroken.rules[0]?.safety).toMatchObject({status: 'broken'})

    const uncovFile = join(dir, 'uncov.c')
    writeFileSync(uncovFile, '// gdp: safety\nstruct ring { int head; };\nvoid update(struct ring *r) { while (r->head) r->head = 0; }\n')
    const rUncov = await check([uncovFile], {entry: 'ring', propose: false})
    expect(rUncov.exit).toBe(2)
    expect(rUncov.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // Default path without // gdp: safety and without --safety has no safety field.
    const defaultFile = join(dir, 'plain.c')
    writeFileSync(defaultFile, 'struct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n')
    const rPlain = await check([defaultFile], {entry: 'ring', propose: false})
    expect(rPlain.exit).toBe(0)
    expect(rPlain.rules[0]?.safety).toBeUndefined()

    // gdp.toml cannot silently override an in-source `// gdp: safety` directive (top-level or per-rule).
    const tomlDirTop = mkdtempSync(join(tmpdir(), 'gdp-c-safety-toml-top-'))
    const tomlDirRule = mkdtempSync(join(tmpdir(), 'gdp-c-safety-toml-rule-'))
    try {
      const fTop = join(tomlDirTop, 'safe.c')
      writeFileSync(fTop, '// gdp: safety\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n')
      writeFileSync(join(tomlDirTop, 'gdp.toml'), 'safety = false\n')
      const rTop = await check([fTop], {propose: false})
      expect(rTop.exit).toBe(2)
      expect(rTop.rules[0]?.ok).toBe(false)
      expect(rTop.rules[0]?.refusals.map(x => x.what).join('; ')).toMatch(/gdp\.toml/)

      const fRule = join(tomlDirRule, 'safe.c')
      writeFileSync(fRule, '// gdp: safety\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n')
      writeFileSync(join(tomlDirRule, 'gdp.toml'), '[rules.ring]\nsafety = false\n')
      const rRuleExplicit = await check([fRule], {entry: 'ring', propose: false})
      expect(rRuleExplicit.exit).toBe(2)
      expect(rRuleExplicit.rules[0]?.ok).toBe(false)
      const rRuleInferred = await check([fRule], {propose: false})
      expect(rRuleInferred.exit).toBe(2)
      expect(rRuleInferred.rules[0]?.ok).toBe(false)
    } finally {
      rmSync(tomlDirTop, {recursive: true, force: true})
      rmSync(tomlDirRule, {recursive: true, force: true})
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 90_000)

// --- 9. Independent Review Soundness Probes (no false SAFEs, site-matched replay) ---------------------------------------

withClang('Review Probe 1: configured failure after state write (fails-after-write) is never proven safe', () => {
  const code = `#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int push(struct ring *r, int32_t v) {
  if (r->n > 100) return -1;
  r->n = r->n + 1;
  if (r->n > 8) return -1;
  r->a[r->n - 1] = v;
  return 0;
}
int top(struct ring *r) {
  if (r->n > 0) return r->a[r->n - 1];
  return 0;
}
`
  // With fails: {push: '< 0'}, push writes r->n before returning -1 -> MUST be refused as unchecked.
  const withFails = analyze(code, {fails: {push: '< 0'}})
  expect(withFails.ok).toBe(false)
  expect(withFails.safety?.status).toBe('unchecked')
  expect(withFails.refusals.map(r => r.what).join('; ')).toMatch(/after the state is written/)

  // Without fails, the write persists and the real OOB access in top() is found and replayed under UBSan.
  const withoutFails = analyze(code)
  expect(withoutFails.ok).toBe(false)
  expect(withoutFails.safety?.status).toBe('broken')
  const topOob = withoutFails.safety!.issues.find(i => i.kind === 'bounds' && i.status === 'broken')
  expect(topOob?.replay?.matchedSite).toBe(true)
  expect(topOob?.replay?.reports.join('\n')).toMatch(/index 8 out of bounds/)
}, 90_000)

withClang('Review Probe 2: unselected TU writers (non-first-param, void* callback, int* writer, wrapper) are refused', () => {
  const nonMethodWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void set_n(int32_t k, struct ring *r) { r->n = k; }
`)
  expect(nonMethodWriter.ok).toBe(false)
  expect(nonMethodWriter.safety?.status).toBe('unchecked')

  const voidCtxCallback = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 9) return r->a[r->n]; return 0; }
void on_event(void *ctx) { struct ring *r = ctx; r->n = 8; }
`)
  expect(voidCtxCallback.ok).toBe(false)
  expect(voidCtxCallback.safety?.status).toBe('unchecked')

  const ptrWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void corrupt(int32_t *p) { *p = 8; }
`)
  expect(ptrWriter.ok).toBe(false)
  expect(ptrWriter.safety?.status).toBe('unchecked')

  const wrapperCallingStaticHelper = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
static void set_helper(struct ring *r, int32_t k) { r->n = k; }
int32_t get(struct ring *r) { set_helper(r, 0); return r->a[r->n]; }
void evil(int32_t k, struct ring *r) { set_helper(r, k); }
`)
  expect(wrapperCallingStaticHelper.ok).toBe(false)
  expect(wrapperCallingStaticHelper.safety?.status).toBe('unchecked')

  // Positive control: a provably read-only non-selected function may coexist safely.
  const readOnlyCoexist = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t add2(int32_t a, int32_t b) { return a + b; }
`)
  expect(readOnlyCoexist.ok, JSON.stringify(readOnlyCoexist.refusals)).toBe(true)
  expect(readOnlyCoexist.safety?.status).toBe('proven')
}, 90_000)

withClang('Review Probe 3: narrowing methods/functions refuses dropped state writers and allows read-only readers', () => {
  const droppedWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void set(struct ring *r, int32_t k) { r->n = k; }
`, {methods: ['get']})
  expect(droppedWriter.ok).toBe(false)
  expect(droppedWriter.safety?.status).toBe('unchecked')

  const droppedGlobalWriter = analyze(`static int buf[4];
static int cursor = 0;
void set_cursor(int k) { cursor = k; }
int read_cur(void) { return buf[cursor]; }
`, {entry: 'gbuf', methods: ['read_cur']}, 'gbuf.c')
  expect(droppedGlobalWriter.ok).toBe(false)
  expect(droppedGlobalWriter.safety?.status).toBe('unchecked')

  const emptyMethods = analyze(`struct ring { int slots[4]; };
void put(struct ring *r, int i) { if (i >= 0 && i < 4) r->slots[i] = 1; }
`, {methods: []})
  expect(emptyMethods.ok).toBe(false)
  expect(emptyMethods.safety?.status).toBe('unchecked')

  // Positive control: narrowing away a provably read-only observer is allowed.
  const droppedReadOnly = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t current_n(const struct ring *r) { return r->n; }
`, {methods: ['get']})
  expect(droppedReadOnly.ok, JSON.stringify(droppedReadOnly.refusals)).toBe(true)
  expect(droppedReadOnly.safety?.status).toBe('proven')
}, 90_000)

withClang('Review Probe 4: unsigned wrap, signed/unsigned cmp, div-m1, outparam, u8-inc, shortcircuit, mod-neg never prove safe', () => {
  const H = '#include <stdint.h>\n'
  const brokenCases: [string, string][] = [
    ['unsigned-sub-wrap', H + `struct ring { uint32_t u; int32_t a[8]; };
int32_t f(struct ring *r) { uint32_t k = r->u - 1u; if (k != 0u) return r->a[k & 15u]; return 0; }
`],
    ['unsigned-cmp-conv', H + `struct ring { int32_t n; int32_t a[8]; };
int32_t f(struct ring *r, uint32_t u) { if (u < -1) return r->a[9]; return 0; }
`],
    ['div-m1', H + `struct ring { int32_t n; };
int32_t f(struct ring *r, int32_t x) { return x / -1; }
`],
    ['outparam-index', H + `struct ring { int32_t n; int32_t a[8]; };
void g(struct ring *r, int32_t *out) { *out = r->a[*out & 7]; }
int32_t h(struct ring *r, int32_t *out) { if (*out > 8) return 0; return r->a[*out]; }
`],
    ['u8-inc-index', H + `struct ring { uint8_t i; int32_t a[200]; };
void bump(struct ring *r) { r->i++; }
int32_t get(struct ring *r) { if (r->i < 250) return r->a[r->i]; return 0; }
`],
    ['shortcircuit', H + `struct ring { int32_t n; int32_t a[8]; };
int32_t f(struct ring *r, int32_t i) { return (i >= 0 && i < 8 && r->a[i] > 0) ? 1 : (i == 8 ? r->a[i] : 0); }
`],
  ]
  for (const [label, code] of brokenCases) {
    const res = analyze(code, {safetySearchMs: 10_000})
    expect(res.ok, `${label} must not succeed`).toBe(false)
    expect(res.safety?.status, `${label} must never prove safe`).not.toBe('proven')
    expect(res.safety?.status, `${label} should replay broken under UBSan`).toBe('broken')
    const badIssue = res.safety!.issues.find(i => i.status === 'broken')
    expect(badIssue?.replay?.matchedSite, `${label} matchedSite`).toBe(true)
  }

  // mod-neg: signed % 8 where dividend may be negative (outside nat modk or broken) must never prove safe.
  const modNeg = analyze(H + `struct ring { int32_t a[8]; };
int32_t f(struct ring *r, int32_t i) { return r->a[i % 8]; }
`, {safetySearchMs: 10_000})
  expect(modNeg.ok).toBe(false)
  expect(modNeg.safety?.status).not.toBe('proven')
}, 180_000)

withClang('Review Probe 5: replay without matchedSite stays unproven (never marked broken)', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-matchsite-'))
  try {
    const file = join(dir, 'oob.c')
    writeFileSync(file, 'struct ring { int slots[4]; };\nvoid set(struct ring *r, int i) { r->slots[i] = 1; }\n')
    const {tu, target} = clangDump(file, [])
    const c = readC(file, 'ring', tu, target, false, undefined, {}, [], [], [], true)
    const read = readGo(c.pkg, {entry: 'ring', methods: c.methods, strict: true, safety: true})
    const mismatched = analyzeCSafety(read, c, read.safety!.sites, {}, {
      replay: () => ({
        built: true, requests: ['set(4)'],
        reports: ['other.c:99:1: runtime error: index 4 out of bounds'],
        states: [], stderr: 'other.c:99:1: runtime error: index 4 out of bounds',
        matchedSite: false,
      }),
    })
    expect(mismatched.status).toBe('unproven')
    expect(mismatched.issues[0]?.status).toBe('unproven')
    expect(mismatched.issues[0]?.why).toMatch(/did not match target site/)

    const matched = analyzeCSafety(read, c, read.safety!.sites, {}, {
      replay: () => ({
        built: true, requests: ['set(4)'],
        reports: ['oob.c:2:35: runtime error: index 4 out of bounds'],
        states: [], stderr: 'oob.c:2:35: runtime error: index 4 out of bounds',
        matchedSite: true,
      }),
    })
    expect(matched.status).toBe('broken')
    expect(matched.issues[0]?.status).toBe('broken')
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 60_000)

test('removing an abstract bounds guard does not prove absence of alarms', () => {
  const checkAbs = (guarded: boolean) => {
    const r = rule('abstract access guard').inputs({request: bool, inBounds: bool}).state({alarm: bool.from(false)})
      .step(({alarm, request, inBounds}) => {
        const reached = guarded ? request.and(inBounds) : request
        return {alarm: alarm.or(reached.and(inBounds.not()))}
      })
    const clear = r.law('the bounds alarm stays clear', ({alarm}) => alarm.not())
    const {proven, checked, failed} = proveLaws(r.machine, [clear])
    return {proven, checked, stuck: failed?.stuck}
  }
  expect(checkAbs(true)).toMatchObject({proven: true, checked: true})
  expect(checkAbs(false)).toMatchObject({proven: false, checked: false, stuck: 'sat'})
})
