// C memory & UB safety tests (Stage 1): first-fault model, pre-lowering site accounting,
// Astra soundness controls, off-by-one corpus mutants with ASan/UBSan replay, and CLI opt-in.
import {expect, test} from 'bun:test'
import {execFileSync, spawn, spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {chmodSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {proveLaws} from '../kernel/prove.ts'
import {check} from './cli.ts'
import {clangDump, isSpecialVirtualPath, readC, resolveSafetyClang, verifyClangBinary} from './c/reader.ts'
import {analyzeCSafety, cSafetyArtifactOf, verifyCSafetyProof, type CSafetyProofBundle} from './c/safety.ts'
import {bool, rule} from './dsl.ts'
import {extractC, type COptions} from './extract-c.ts'
import {readGo, unsignedDomains} from './extract-go.ts'
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

withClang('Review Probe 2: unselected TU functions (writers, callbacks, free functions) are refused and named', () => {
  const nonMethodWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void set_n(int32_t k, struct ring *r) { r->n = k; }
`)
  expect(nonMethodWriter.ok).toBe(false)
  expect(nonMethodWriter.safety?.status).toBe('unchecked')
  expect(nonMethodWriter.safety?.uncheckedFunctions).toEqual(['set_n'])

  const voidCtxCallback = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 9) return r->a[r->n]; return 0; }
void on_event(void *ctx) { struct ring *r = ctx; r->n = 8; }
`)
  expect(voidCtxCallback.ok).toBe(false)
  expect(voidCtxCallback.safety?.status).toBe('unchecked')
  expect(voidCtxCallback.safety?.uncheckedFunctions).toEqual(['on_event'])

  const ptrWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void corrupt(int32_t *p) { *p = 8; }
`)
  expect(ptrWriter.ok).toBe(false)
  expect(ptrWriter.safety?.status).toBe('unchecked')
  expect(ptrWriter.safety?.uncheckedFunctions).toEqual(['corrupt'])

  const wrapperCallingStaticHelper = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
static void set_helper(struct ring *r, int32_t k) { r->n = k; }
int32_t get(struct ring *r) { set_helper(r, 0); return r->a[r->n]; }
void evil(int32_t k, struct ring *r) { set_helper(r, k); }
`)
  expect(wrapperCallingStaticHelper.ok).toBe(false)
  expect(wrapperCallingStaticHelper.safety?.status).toBe('unchecked')
  expect(wrapperCallingStaticHelper.safety?.uncheckedFunctions).toEqual(['evil'])

  // An unselected free function (even read-only on struct ring, e.g. signed overflow a + b) must be refused and named.
  const freeFnOverflow = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t add2(int32_t a, int32_t b) { return a + b; }
`)
  expect(freeFnOverflow.ok).toBe(false)
  expect(freeFnOverflow.safety?.status).toBe('unchecked')
  expect(freeFnOverflow.safety?.coveredFunctions).toEqual(['get'])
  expect(freeFnOverflow.safety?.uncheckedFunctions).toEqual(['add2'])

  // Positive control: a file-local static helper actually inlined and inventoried by get() is covered.
  const staticHelperCovered = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
static int32_t clamp_idx(int32_t i) { return (i >= 0 && i < 8) ? i : 0; }
int32_t get(struct ring *r) { return r->a[clamp_idx(r->n)]; }
`)
  expect(staticHelperCovered.ok, JSON.stringify(staticHelperCovered.refusals)).toBe(true)
  expect(staticHelperCovered.safety?.status).toBe('proven')
  expect(staticHelperCovered.safety?.coveredFunctions).toEqual(['get'])
  expect(staticHelperCovered.safety?.coveredHelpers).toEqual(['clamp_idx'])
}, 90_000)

withClang('Review Probe 3: narrowing methods/functions refuses any dropped TU function (writer or reader) and names it', () => {
  const droppedWriter = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
void set(struct ring *r, int32_t k) { r->n = k; }
`, {methods: ['get']})
  expect(droppedWriter.ok).toBe(false)
  expect(droppedWriter.safety?.status).toBe('unchecked')
  expect(droppedWriter.safety?.uncheckedFunctions).toEqual(['set'])

  const droppedGlobalWriter = analyze(`static int buf[4];
static int cursor = 0;
void set_cursor(int k) { cursor = k; }
int read_cur(void) { return buf[cursor]; }
`, {entry: 'gbuf', methods: ['read_cur']}, 'gbuf.c')
  expect(droppedGlobalWriter.ok).toBe(false)
  expect(droppedGlobalWriter.safety?.status).toBe('unchecked')
  expect(droppedGlobalWriter.safety?.uncheckedFunctions).toEqual(['set_cursor'])

  const emptyMethods = analyze(`struct ring { int slots[4]; };
void put(struct ring *r, int i) { if (i >= 0 && i < 4) r->slots[i] = 1; }
`, {methods: []})
  expect(emptyMethods.ok).toBe(false)
  expect(emptyMethods.safety?.status).toBe('unchecked')

  // Narrowing away even a read-only function leaves it unchecked -> refused and named.
  const droppedReader = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t current_n(const struct ring *r) { return r->n; }
`, {methods: ['get']})
  expect(droppedReader.ok).toBe(false)
  expect(droppedReader.safety?.status).toBe('unchecked')
  expect(droppedReader.safety?.coveredFunctions).toEqual(['get'])
  expect(droppedReader.safety?.uncheckedFunctions).toEqual(['current_n'])

  // Positive control: selecting every function in the TU proves safe and lists exact coveredFunctions.
  const allSelected = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t current_n(const struct ring *r) { return r->n; }
`, {methods: ['get', 'current_n']})
  expect(allSelected.ok, JSON.stringify(allSelected.refusals)).toBe(true)
  expect(allSelected.safety?.status).toBe('proven')
  expect(allSelected.safety?.coveredFunctions).toEqual(['get', 'current_n'])
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

  // Deep (201-step) u8-inc-index and negative signed mod-neg must never prove safe.
  const u8Inc = analyze(H + `struct ring { uint8_t i; int32_t a[200]; };
void bump(struct ring *r) { r->i++; }
int32_t get(struct ring *r) { if (r->i < 250) return r->a[r->i]; return 0; }
`, {safetySearchMs: 5_000})
  expect(u8Inc.ok).toBe(false)
  expect(['broken', 'unproven']).toContain(u8Inc.safety?.status ?? '')

  const modNeg = analyze(H + `struct ring { int32_t a[8]; };
int32_t f(struct ring *r, int32_t i) { return r->a[i % 8]; }
`, {safetySearchMs: 5_000})
  expect(modNeg.ok).toBe(false)
  expect(modNeg.safety?.status).not.toBe('proven')
}, 180_000)

withClang('Review Probe 5: replay without matchedSite stays unproven (never marked broken)', () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-matchsite-'))
  try {
    const file = join(dir, 'oob.c')
    writeFileSync(file, '#include <stdint.h>\nstruct ring { uint32_t slots[4]; };\nvoid set(struct ring *r, uint32_t i) { r->slots[i] = 1u; }\n')
    const {tu, target} = clangDump(file, [])
    const c = readC(file, 'ring', tu, target, false, undefined, {}, [], [], [], true)
    const read = readGo(c.pkg, {entry: 'ring', methods: c.methods, strict: true, safety: true})
    const mismatched = analyzeCSafety(read, c, read.safety!.sites, unsignedDomains(read), {
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

    const matched = analyzeCSafety(read, c, read.safety!.sites, unsignedDomains(read), {
      replay: () => ({
        built: true, requests: ['set(4)'],
        reports: ['oob.c:3:40: runtime error: index 4 out of bounds'],
        states: [], stderr: 'oob.c:3:40: runtime error: index 4 out of bounds',
        matchedSite: true,
      }),
    })
    expect(matched.status).toBe('broken')
    expect(matched.issues[0]?.status).toBe('broken')
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 60_000)

withClang('Review Probe 6: partial and designated const tables (array_filler) t1/t2/t4/u1-u5 and cast initializers', () => {
  const H = '#include <stdint.h>\n#include <stdbool.h>\n'
  const S = H + 'struct ring { int32_t n; int32_t a[8]; };\n'
  const brokenCases: [string, string, Parameters<typeof analyze>[1]?, string?][] = [
    ['t1-designated', S + 'static const int32_t T[4] = {[3] = 9};\nint32_t f(struct ring *r, int32_t i) { if (i >= 1 && i < 4) return r->a[T[i]]; return 0; }\n'],
    ['t2-partial', S + 'static const int32_t T[4] = {1, 2};\nint32_t f(struct ring *r, int32_t i) { if (i >= 0 && i < 4) return r->a[T[i] + 6]; return 0; }\n'],
    ['t4-desig-over', S + 'static const int32_t T[3] = {7, [0] = 8};\nint32_t f(struct ring *r, int32_t i) { if (i >= 0 && i < 1) return r->a[T[i]]; return 0; }\n'],
    ['u3-2d-partial', S + 'static const int32_t T[2][2] = {{0}, {9}};\nint32_t f(struct ring *r, int32_t i, int32_t j) { if (i >= 0 && i < 2 && j >= 0 && j < 2) return r->a[T[i][j]]; return 0; }\n'],
    ['u4-ring-next', S + 'static const uint8_t NEXT[8] = {1, 2, 3, 4, 5, 6, 8};\nvoid adv(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = NEXT[r->n]; }\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[NEXT[r->n]]; return 0; }\n'],
    ['u5-gmode-table', H + 'static int32_t buf[8];\nstatic int32_t cur;\nstatic const int32_t STEP[4] = {9};\nvoid put(int32_t k, int32_t v) { if (k >= 0 && k < 4) buf[STEP[k]] = v; }\n', {entry: 'gtab', methods: ['put']}, 'gtab.c'],
  ]
  for (const [label, code, opts, fname] of brokenCases) {
    const res = analyze(code, {safetySearchMs: 10_000, ...opts}, fname)
    expect(res.ok, `${label} must not succeed`).toBe(false)
    expect(res.safety?.status, `${label} must never prove safe`).not.toBe('proven')
    expect(res.safety?.status, `${label} must replay broken under ASan/UBSan`).toBe('broken')
    const badIssue = res.safety!.issues.find(i => i.status === 'broken')
    expect(badIssue?.replay?.matchedSite, `${label} matchedSite`).toBe(true)
  }

  // u1-overflow-partial (K[2]={65536}, K[i]*x) and u2-div-partial (K[2]={1}, x/(K[i]+1)) must NOT
  // collapse K to [0,0] and falsely prove safe; with real non-zero table entries they are nonlinear/nonconstant
  // and cleanly refused as unchecked (or broken if linear).
  const u1 = analyze(S + 'static const int32_t K[2] = {65536};\nint32_t f(struct ring *r, int32_t i, int32_t x) { if (i >= 0 && i < 2 && x >= 0 && x < 65536) return K[i] * x; return 0; }\n')
  expect(u1.ok).toBe(false)
  expect(u1.safety?.status).not.toBe('proven')
  expect(['unchecked', 'broken']).toContain(u1.safety?.status ?? '')

  const u2 = analyze(S + 'static const int32_t K[2] = {1};\nint32_t f(struct ring *r, int32_t i, int32_t x) { if (i >= 0 && i < 2) return x / (K[i] + 1); return 0; }\n')
  expect(u2.ok).toBe(false)
  expect(u2.safety?.status).toBe('unchecked')

  // Safe designated/partial positive control: T[4] = {[3] = 7} stays within [0, 8) -> proven.
  const desigSafe = analyze(S + 'static const int32_t T[4] = {[3] = 7};\nint32_t f(struct ring *r, int32_t i) { if (i >= 0 && i < 4) return r->a[T[i]]; return 0; }\n')
  expect(desigSafe.ok, JSON.stringify(desigSafe.refusals)).toBe(true)
  expect(desigSafe.safety?.status).toBe('proven')
  const desigArt = cSafetyArtifactOf(desigSafe.safety!)!
  expect(verifyCSafetyProof(desigArt.machine, desigArt.targetLaws, desigArt.jointProof)).toBe(true)

  // Narrowing C-style cast inside a const table initializer ((uint8_t)(-1) == 255, not -1) must be refused.
  const castInit = analyze(S + 'static const int32_t T[2] = {(uint8_t)(-1), 0};\nint32_t f(struct ring *r, int32_t i) { if (i >= 0 && i < 2) return r->a[T[i] + 1]; return 0; }\n')
  expect(castInit.ok).toBe(false)
  expect(castInit.safety?.status).toBe('unchecked')
}, 180_000)

withClang('Review Probe 7: bodyless prototypes refused; inline/trailing gdp: safety accepted and lookalike warned', async () => {
  const H = '#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\n'
  for (const [label, extra] of [
    ['entry-proto', 'void set_n(struct ring *r, int32_t k);\n'],
    ['const-entry-proto', 'void inspect_ext(const struct ring *r);\n'],
    ['void-ptr-proto', 'void on_event(void *ctx);\n'],
    ['scalar-ptr-proto', 'void poke(int32_t *p);\n'],
    ['kr-noproto', 'void mystery();\n'],
    ['ret-entry-proto', 'struct ring *make_ring(void);\n'],
  ] as const) {
    const res = analyze(H + extra)
    expect(res.ok, `${label} must be refused`).toBe(false)
    expect(res.safety?.status, `${label} must be unchecked`).toBe('unchecked')
  }

  // Positive control: forward prototype of a function defined in the same translation unit is allowed.
  const fwdDefined = analyze(`#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r);
int32_t get(struct ring *r) { return r->a[r->n]; }
`)
  expect(fwdDefined.ok, JSON.stringify(fwdDefined.refusals)).toBe(true)
  expect(fwdDefined.safety?.status).toBe('proven')

  // CLI gdp: safety directive syntax: inline, trailing text, multiline block, lookalike warning, string literal ignored.
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-tag-'))
  try {
    const variants: [string, string][] = [
      ['trailing.c', '// gdp: safety (Stage 1 bounds)\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n'],
      ['inline_line.c', 'struct ring { int slots[8]; }; // gdp: safety\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n'],
      ['inline_block.c', 'struct ring { int slots[8]; };\nvoid put(struct ring *r, int i) /* gdp: safety: ring */ { if (i >= 0 && i < 8) r->slots[i] = 1; }\n'],
      ['multiline.c', '/*\n * ring buffer\n * gdp: safety\n */\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n'],
    ]
    for (const [fname, code] of variants) {
      const f = join(dir, fname)
      writeFileSync(f, code)
      const res = await check([f], {entry: 'ring', propose: false})
      expect(res.exit, `${fname} exit`).toBe(0)
      expect(res.rules[0]?.safety, `${fname} safety`).toMatchObject({status: 'proven'})
    }

    // Lookalike comment (`// gdp: safe`) emits a clear warning note and exits 2 (non-zero).
    const typoFile = join(dir, 'typo.c')
    writeFileSync(typoFile, '// gdp: safe\nstruct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n')
    const rTypo = await check([typoFile], {entry: 'ring', propose: false})
    expect(rTypo.exit).toBe(2)
    expect(rTypo.rules[0]?.safety).toBeUndefined()
    expect(rTypo.rules[0]?.notes.join('\n')).toMatch(/looks like a gdp: safety directive/)

    // String literal mentioning `// gdp: safety` does not activate safety mode.
    const strDir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-str-'))
    try {
      const strFile = join(strDir, 'str.c')
      writeFileSync(strFile, 'struct ring { int n; };\nvoid put(struct ring *r) { if (r->n < 4) r->n++; }\nstatic const char *tag = "// gdp: safety";\n')
      const rStr = await check([strFile], {entry: 'ring', propose: false})
      expect(rStr.exit).toBe(0)
      expect(rStr.rules[0]?.safety).toBeUndefined()
    } finally {
      rmSync(strDir, {recursive: true, force: true})
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 120_000)

const runCliText = (argv: string[], extraEnv?: Record<string, string>): {code: number, out: string} => {
  const proc = spawnSync(process.execPath, [new URL('./cli.ts', import.meta.url).pathname, ...argv], {
    encoding: 'utf8',
    ...(extraEnv ? {env: {...process.env, ...extraEnv}} : {}),
  })
  return {code: proc.status ?? -1, out: proc.stdout ?? ''}
}

withClang('Review Probe 8: closed-TU function coverage (probe4 cli1/cli2/u01-u05/x04-x06/e05-e06) and explicit covered verdict', () => {
  const H = '#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n'

  // Unchecked function-body variants from probe4 (s3 u01-u05, s7 x04-x06):
  const uncheckedCases: [string, string, string[], COptions?][] = [
    ['u01-peek-second-param', H + 'int32_t get(struct ring *r) { return r->a[r->n]; }\nint32_t peek(int32_t z, struct ring *r) { return r->a[r->n]; }\n', ['peek']],
    ['u02-free-overflow', H + 'int32_t get(struct ring *r) { return r->a[r->n]; }\nint32_t inc(int32_t x) { return x + 1; }\n', ['inc']],
    ['u03-free-div', H + 'int32_t get(struct ring *r) { return r->a[r->n]; }\nint32_t dv(int32_t x, int32_t y) { return x / y; }\n', ['dv']],
    ['u04-static-unused-reader', H + 'static int32_t peek(struct ring *r, int32_t i) { return r->a[i]; }\nint32_t get(struct ring *r) { return r->a[r->n]; }\n', ['peek']],
    ['u05-narrowed-reader', H + 'int32_t get(struct ring *r) { return r->a[r->n]; }\nint32_t peek(struct ring *r, int32_t i) { return r->a[i]; }\n', ['peek'], {methods: ['get']}],
    ['x04-byvalue', H + 'int32_t get(struct ring *r) { return r->a[r->n]; }\nint32_t peekv(struct ring r) { return r.a[r.n]; }\n', ['peekv']],
    ['x06-static-called-by-unselected', H + 'static int32_t h(struct ring *r, int32_t i) { return r->a[i]; }\nint32_t peek(int32_t z, struct ring *r) { return h(r, z); }\nint32_t get(struct ring *r) { return r->a[r->n]; }\n', ['h', 'peek']],
  ]
  for (const [label, code, expectedUnchecked, opts] of uncheckedCases) {
    const res = analyze(code, opts)
    expect(res.ok, `${label} must be refused`).toBe(false)
    expect(res.safety?.status, `${label} must be unchecked`).toBe('unchecked')
    expect(res.safety?.coveredFunctions, `${label} coveredFunctions`).toEqual(['get'])
    expect(res.safety?.uncheckedFunctions, `${label} uncheckedFunctions`).toEqual(expectedUnchecked)
    for (const fn of expectedUnchecked) {
      expect(res.refusals.map(r => r.what).join('; '), `${label} refusal names ${fn}`).toContain(fn)
    }
  }

  // Unmodeled globals from probe4 s8 (e05-fnptr-global, e06-extern-ring-global):
  const e05 = analyze(H + 'void (*hook)(struct ring *);\nint32_t get(struct ring *r) { return r->a[r->n]; }\n')
  expect(e05.ok).toBe(false)
  expect(e05.safety?.status).toBe('unchecked')
  const e06 = analyze(H + 'extern struct ring R0;\nint32_t get(struct ring *r) { return r->a[r->n]; }\n')
  expect(e06.ok).toBe(false)
  expect(e06.safety?.status).toBe('unchecked')

  // CLI end-to-end tests matching probe4/cli1 and probe4/cli2 (both inferred entry and explicit text output):
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-p4-cli-'))
  try {
    const cli1 = join(dir, 'cli1_ring.c')
    writeFileSync(cli1, `// gdp: safety
#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t peek(int32_t i, struct ring *r) { return r->a[i]; }
int32_t inc(int32_t x) { return x + 1; }
int32_t dv(int32_t x, int32_t y) { return x / y; }
`)
    const r1 = runCliText(['check', '--no-propose', cli1])
    expect(r1.code).toBe(2)
    expect(r1.out).toContain('unchecked (covers: get)')
    expect(r1.out).toContain('unchecked functions: peek, inc, dv')

    const cli2 = join(dir, 'cli2_ring.c')
    writeFileSync(cli2, `// gdp: safety
#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { return r->a[r->n]; }
int32_t peek(int32_t z, struct ring *r) { return r->a[r->n]; }
int32_t peekv(struct ring r) { return r.a[r.n]; }
`)
    const r2 = runCliText(['check', '--no-propose', cli2])
    expect(r2.code).toBe(2)
    expect(r2.out).toContain('unchecked (covers: get)')
    expect(r2.out).toContain('unchecked functions: peek, peekv')

    // Proven CLI text verdict explicitly names the covered functions and any inlined static helpers.
    const covFile = join(dir, 'covered.c')
    writeFileSync(covFile, `// gdp: safety
#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
static int32_t clamp8(int32_t i) { return (i >= 0 && i < 8) ? i : 0; }
int32_t get(struct ring *r) { return r->a[clamp8(r->n)]; }
void set(struct ring *r, int32_t i, int32_t v) { if (i >= 0 && i < 8) r->a[i] = v; }
`)
    const rCov = runCliText(['check', '--no-propose', covFile])
    expect(rCov.code).toBe(0)
    expect(rCov.out).toContain('proven (covers: get, set; static helpers inlined: clamp8)')
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 120_000)

withClang('Review Probe 9: SAFETY_TAG_RE variants (t1-t10), C23 digit separators, and visible TEXT warning + exit 2 on lookalikes', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-p4-tags-'))
  try {
    const buggyBody = '#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t f(struct ring *r, int32_t i) { return r->a[i]; }\n'
    const tagVariants: [string, string][] = [
      ['t1_period.c', '// gdp: safety.\n' + buggyBody],
      ['t2_docblock.c', '/** gdp: safety **/\n' + buggyBody],
      ['t3_bang_prefix.c', '//! gdp: safety\n' + buggyBody],
      ['t4_uppercase.c', '// GDP: safety\n' + buggyBody],
      ['t5_spaces.c', '// gdp:  safety\n' + buggyBody],
      ['t6_todo_paren.c', '// TODO(gdp: safety)\n' + buggyBody],
      ['t7_excl.c', '// gdp: safety!\n' + buggyBody],
      ['t8_apostrophe.c', "// gdp: safety's on\n" + buggyBody],
      ['t9_tight_block.c', '/*gdp: safety*/\n' + buggyBody],
      ['t10_prefix_text.c', '// see gdp: safety\n' + buggyBody],
    ]
    for (const [fname, code] of tagVariants) {
      const f = join(dir, fname)
      writeFileSync(f, code)
      const res = await check([f], {entry: 'ring', propose: false})
      expect(res.exit, `${fname} must trigger safety mode and fail broken (exit 1)`).toBe(1)
      expect(res.rules[0]?.safety, `${fname} safety status`).toMatchObject({status: 'broken', coveredFunctions: ['f']})
    }

    // C23 digit separators before a trailing `// gdp: safety` or `/* gdp: safety */` comment must not be misparsed as char literals.
    const c23Cases: [string, string, string[]][] = [
      ['c23_dec.c', "#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t f(struct ring *r, int32_t i) { int32_t k = 1'000; (void)k; return r->a[i]; } // gdp: safety\n", ['-std=c23']],
      ['c23_hex.c', "#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t f(struct ring *r, int32_t i) { uint32_t k = 0xDE'AD'BE'EFu; (void)k; return r->a[i]; } /* gdp: safety */\n", ['-std=c23']],
      ['c23_bin.c', "#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t f(struct ring *r, int32_t i) { int32_t k = 0b1010'0101; (void)k; return r->a[i]; } // gdp: safety\n", ['-std=c23']],
      ['c23_u8_char_quote.c', "#if 0\nunsigned char q = u8'\"'; // gdp: safety\n#endif\n" + buggyBody, []],
    ]
    for (const [fname, code, flags] of c23Cases) {
      const f = join(dir, fname)
      writeFileSync(f, code)
      const res = await check([f], {entry: 'ring', ...(flags.length ? {flags} : {}), propose: false})
      expect(res.exit, `${fname} must honor trailing gdp: safety directive`).toBe(1)
      expect(res.rules[0]?.safety, `${fname} safety status`).toMatchObject({status: 'broken'})
    }

    // Lookalikes not honoured as `gdp: safety` must print warning in TEXT output AND exit 2 (non-zero).
    const safeBody = 'struct ring { int slots[8]; };\nvoid put(struct ring *r, int i) { if (i >= 0 && i < 8) r->slots[i] = 1; }\n'
    for (const [fname, header] of [
      ['look_safe.c', '// gdp: safe\n'],
      ['look_assign.c', '// gdp: safety = false\n'],
      ['look_suffix.c', '// gdp: safety_mode\n'],
    ] as const) {
      const f = join(dir, fname)
      writeFileSync(f, header + safeBody)
      const rText = runCliText(['check', '--entry', 'ring', '--no-propose', f])
      expect(rText.code, `${fname} lookalike must exit 2`).toBe(2)
      expect(rText.out, `${fname} lookalike must print warning in TEXT output`).toMatch(/warning:.*looks like a gdp: safety directive/)
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 10: alias/weak/asm exports (al1-al4, ds1-ds3), header globals (rh1), non-system headers (out1-out4), macro config (nd2/nd3), and normalized tags (tg4-tg6, tm1-tm2)', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-p6-'))
  try {
    const H = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n'
    const dvBase = H + `static int32_t dv(int32_t x, int32_t y) { return x / y; }
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return dv(r->a[r->n], 2); return 0; }
void put(struct ring *r, int32_t v) { if (r->n >= 0 && r->n < 7) { r->a[r->n] = v; r->n = r->n + 1; } }
`
    // (1) al1-al4: static helper exported via alias, #pragma weak, __asm__(".globl ..."), weak alias -> refused (exit 2).
    for (const [label, extra] of [
      ['al1-alias', 'int32_t pub(int32_t, int32_t) __attribute__((alias("dv")));\n'],
      ['al2-pragma-weak', '#pragma weak pub = dv\n'],
      ['al3-asm-globl', '__asm__(".globl dv");\n'],
      ['al4-weak-alias', 'extern int32_t pub(int32_t, int32_t) __attribute__((weak, alias("dv")));\n'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, dvBase + extra)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.ok, `${label} must be refused`).toBe(false)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // ds1-ds3: destructor attribute (before, on, or redeclared after body) -> refused (exit 2).
    for (const [label, code] of [
      ['ds1-post-redecl', '// gdp: safety\n#include <stdint.h>\nstatic int32_t a[4];\nstatic int32_t i;\nstatic int32_t h(void) { return a[i]; }\nint32_t get(void) { if (i >= 0 && i < 4) return h(); return 0; }\nvoid set(int32_t v) { i = v; }\n__attribute__((destructor)) static int32_t h(void);\n'],
      ['ds2-on-def', '// gdp: safety\n#include <stdint.h>\nstatic int32_t a[4];\nstatic int32_t i;\n__attribute__((destructor)) static int32_t h(void) { return a[i]; }\nint32_t get(void) { if (i >= 0 && i < 4) return h(); return 0; }\nvoid set(int32_t v) { i = v; }\n'],
      ['ds3-pre-redecl', '// gdp: safety\n#include <stdint.h>\nstatic int32_t a[4];\nstatic int32_t i;\n__attribute__((destructor)) static int32_t h(void);\nstatic int32_t h(void) { return a[i]; }\nint32_t get(void) { if (i >= 0 && i < 4) return h(); return 0; }\nvoid set(int32_t v) { i = v; }\n'],
    ] as const) {
      const d = join(dir, label)
      mkdirSync(d, {recursive: true})
      const f = join(d, 'ring.c')
      writeFileSync(f, code)
      const res = await check([f], {entry: 'ring', propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (2) rh1: global struct with function-pointer field initialized in header under root -> refused (exit 2).
    const rhDir = join(dir, 'rh1')
    mkdirSync(rhDir, {recursive: true})
    writeFileSync(join(rhDir, 'h.h'), '#include <stdint.h>\nstatic int32_t dv(int32_t x, int32_t y);\nstruct ops { int32_t (*f)(int32_t, int32_t); };\nconst struct ops OPS = { dv };\n')
    const rhFile = join(rhDir, 'ring.c')
    writeFileSync(rhFile, `// gdp: safety
#include <stdint.h>
#include "h.h"
struct ring { int32_t n; int32_t a[8]; };
static int32_t dv(int32_t x, int32_t y) { return x / y; }
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return dv(r->a[r->n], 2); return 0; }
void put(struct ring *r, int32_t v) { if (r->n >= 0 && r->n < 7) { r->a[r->n] = v; r->n = r->n + 1; } }
`)
    const rRh = await check([rhFile], {propose: false})
    expect(rRh.exit).toBe(2)
    expect(rRh.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (3) out1-out4: non-system header outside root (inline + extern, constructor, __dv, static + fn-ptr hook) -> refused (exit 2).
    const ringOk = `// gdp: safety
#include <stdint.h>
struct ring { int32_t n; int32_t a[8]; };
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }
void put(struct ring *r, int32_t v) { if (r->n >= 0 && r->n < 7) { r->a[r->n] = v; r->n = r->n + 1; } }
#include "../inc/h.h"
`
    for (const [label, hdr, tail] of [
      ['out1-inline-ext', '#include <stdint.h>\ninline int32_t dv(int32_t x, int32_t y) { return x / y; }\n', 'extern int32_t dv(int32_t, int32_t);\n'],
      ['out2-constructor', '#include <stdint.h>\nstatic void __attribute__((constructor)) boom(void) { volatile int32_t z = 0; volatile int32_t q = 1 / z; (void)q; }\n', ''],
      ['out3-dunder', '#include <stdint.h>\nint32_t __dv(int32_t x, int32_t y) { return x / y; }\n', ''],
      ['out4-static-hook', '#include <stdint.h>\nstatic int32_t dv(int32_t x, int32_t y) { return x / y; }\nint32_t (*hook)(int32_t, int32_t) = dv;\n', ''],
    ] as const) {
      const base = join(dir, label), inc = join(base, 'inc'), srcDir = join(base, 'src')
      mkdirSync(inc, {recursive: true})
      mkdirSync(srcDir, {recursive: true})
      writeFileSync(join(inc, 'h.h'), hdr)
      const f = join(srcDir, 'ring.c')
      writeFileSync(f, ringOk + tail)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // #line spoofing a system header path is also refused (exit 2).
    const lineSpoof = join(dir, 'line_spoof.c')
    writeFileSync(lineSpoof, H + `int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }
#line 1 "/usr/include/stdint.h"
static int32_t dv(int32_t x, int32_t y) { return x / y; }
`)
    const rLine = await check([lineSpoof], {propose: false})
    expect(rLine.exit).toBe(2)
    expect(rLine.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (4) nd2/nd3: build-mode macro conditionals (__OPTIMIZE__, NDEBUG) refused (exit 2);
    // proven verdict explicitly states macroConfig (-D flags, NDEBUG=undefined, __OPTIMIZE__=undefined).
    const nd2 = join(dir, 'nd2.c')
    writeFileSync(nd2, H + `#ifdef __OPTIMIZE__
void put(struct ring *r, int32_t v) { r->a[r->n] = v; r->n = r->n + 1; }
#else
void put(struct ring *r, int32_t v) { if (r->n >= 0 && r->n < 8) { r->a[r->n] = v; r->n = r->n + 1; } }
#endif
`)
    const rNd2 = await check([nd2], {propose: false})
    expect(rNd2.exit).toBe(2)
    expect(rNd2.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rNd2.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('__OPTIMIZE__')

    const nd3 = join(dir, 'nd3.c')
    writeFileSync(nd3, H + `void put(struct ring *r, int32_t v) {
#ifndef NDEBUG
  if (r->n < 0 || r->n >= 8) return;
#endif
  r->a[r->n] = v; r->n = r->n + 1;
}
`)
    const rNd3 = await check([nd3], {propose: false})
    expect(rNd3.exit).toBe(2)
    expect(rNd3.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rNd3.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('NDEBUG')

    const cleanFile = join(dir, 'clean_cfg.c')
    writeFileSync(cleanFile, H + 'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rClean = runCliText(['check', '--no-propose', cleanFile])
    expect(rClean.code).toBe(0)
    expect(rClean.out).toContain('proven (covers: get)')
    expect(rClean.out).toMatch(/macro config: target: \S+.*; std: \S+ \(__STDC_VERSION__=\S+\); env: scrubbed; -I flags: none; -D flags: none; NDEBUG=undefined, __OPTIMIZE__=undefined, DEBUG=undefined/)

    const rWithDef = await check([cleanFile], {flags: ['-DLIMIT=8'], propose: false})
    expect(rWithDef.exit).toBe(0)
    expect(rWithDef.rules[0]?.safety).toMatchObject({
      status: 'proven',
      coveredFunctions: ['get'],
      macroConfig: {envScrubbed: true, includeDirs: [], defines: ['-DLIMIT=8'], ndebugDefined: false, optimizeDefined: false, debugDefined: false},
    })

    // (5) Normalized tag & lookalike handling: tm1 (newline in /* */) and tm2 (backslash-continued //)
    // activate safety mode (exit 1 on buggy peek); tg4 (NBSP), tg5 (fullwidth colon), tg6 ('gdp safety'),
    // and starred newline wrap emit visible TEXT warning + exit 2.
    const buggyPeek = '#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t peek(struct ring *r, int32_t i) { return r->a[i]; }\n'
    for (const [fname, header] of [
      ['tm1_newline.c', '/* gdp:\n   safety */\n'],
      ['tm2_bslash.c', '// see below \\\n   gdp: safety\n'],
      ['tm3_doc.c', '/**\n * gdp: safety\n */\n'],
    ] as const) {
      const f = join(dir, fname)
      writeFileSync(f, header + buggyPeek)
      const res = await check([f], {entry: 'ring', propose: false})
      expect(res.exit, `${fname} must activate safety and fail broken (exit 1)`).toBe(1)
      expect(res.rules[0]?.safety, `${fname} safety status`).toMatchObject({status: 'broken'})
    }
    for (const [fname, header] of [
      ['tg4_nbsp.c', '// gdp:\u00A0safety\n'],
      ['tg5_fwcolon.c', '// gdp\uFF1A safety\n'],
      ['tg6_nocolon.c', '// gdp safety\n'],
      ['tm_starwrap.c', '/* gdp:\n * safety */\n'],
    ] as const) {
      const f = join(dir, fname)
      writeFileSync(f, header + buggyPeek)
      const rText = runCliText(['check', '--entry', 'ring', '--no-propose', f])
      expect(rText.code, `${fname} lookalike must exit 2`).toBe(2)
      expect(rText.out, `${fname} lookalike must print warning in TEXT output`).toMatch(/warning:.*looks like a gdp: safety directive/)
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 11: path-only system-header boundary (h3-h7), pragma/linemarker spellings (l1-l3, p1-p2), build-mode token invariance (m1/m5/m6), and target/std config reporting (m2-m4)', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe11-'))
  try {
    // (1) h3-h7 + digraph %:pragma + macro-hidden _Pragma: #pragma GCC system_header (and _Pragma /
    // %:pragma / macro-expanded _Pragma) in a non-system project header must NEVER exempt that header
    // or any header it includes (via -I or relative ../inc), regardless of whether it hides a plain
    // function body (h3), a function-pointer global (h4), or a static-helper alias (h5-h7).
    const baseGet = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n'
    const baseHelper = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nstatic int32_t dv(int32_t x, int32_t y) { return x / y; }\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return dv(r->a[r->n], 2); return 0; }\n'
    for (const [label, hContent, evilContent, ringBody, useDashI] of [
      ['h3-I-fn', '#pragma GCC system_header\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', baseGet + '#include "h.h"\n', true],
      ['h4-I-fnptr', '#pragma GCC system_header\n#include "evil.h"\n', '#include <stdint.h>\nint32_t (*pubp)(int32_t, int32_t) = dv;\n', baseHelper + '#include "h.h"\n', true],
      ['h5-I-alias', '#pragma GCC system_header\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t, int32_t) __attribute__((alias("dv")));\n', baseHelper + '#include "h.h"\n', true],
      ['h6-rel-alias', '#pragma GCC system_header\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t, int32_t) __attribute__((alias("dv")));\n', baseHelper + '#include "../inc/h.h"\n', false],
      ['h7-op-pragma', '_Pragma("GCC system_header")\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t, int32_t) __attribute__((alias("dv")));\n', baseHelper + '#include "../inc/h.h"\n', false],
      ['h8-digraph-sh', '%:pragma GCC system_header\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', baseGet + '#include "../inc/h.h"\n', false],
      ['h9-macro-sh', '#define HIDE(x) _Pragma(#x)\nHIDE(GCC system_header)\n#include "evil.h"\n', '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', baseGet + '#include "../inc/h.h"\n', false],
    ] as const) {
      const rootDir = join(dir, label), inc = join(rootDir, 'inc'), srcDir = join(rootDir, 'src')
      mkdirSync(inc, {recursive: true})
      mkdirSync(srcDir, {recursive: true})
      writeFileSync(join(inc, 'evil.h'), evilContent)
      writeFileSync(join(inc, 'h.h'), hContent)
      const f = join(srcDir, 'ring.c')
      writeFileSync(f, ringBody)
      const res = await check([f], {propose: false, ...(useDashI ? {flags: [`-I${inc}`]} : {})})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (2) l1-l3 & p1-p2: digraph (%:), trigraph (??=), and _Pragma linemarkers/weak exports -> exit 2.
    for (const [label, code, flags] of [
      ['l1-digraph-lm', baseGet + '%: 1 "/usr/include/zz_fake.h" 3\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', [] as string[]],
      ['l2-trigraph-lm', baseGet + '??= 1 "/usr/include/zz_fake.h" 3\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', ['-std=c11']],
      ['l3-digraph-line', baseGet + '%:line 1 "/usr/include/zz_fake.h"\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n', [] as string[]],
      ['l4-real-stdint-line', baseGet + '%:line 1 "/usr/include/stdint.h"\nstatic int32_t pub(int32_t x, int32_t y) { return x / y; }\n', [] as string[]],
      ['p1-op-weak', baseHelper + '_Pragma("weak pub = dv")\n', [] as string[]],
      ['p2-digraph-weak', baseHelper + '%:pragma weak pub = dv\n', [] as string[]],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, code)
      const res = await check([f], {propose: false, ...(flags.length ? {flags: [...flags]} : {})})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (3) m1, m5, m6: closed-world preprocessor allowlist + token-stream invariance catches DEBUG,
    // digraph %:ifndef NDEBUG, and token-pasted #if !CAT(ND,EBUG) regardless of spelling -> exit 2.
    const macroHdr = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n'
    for (const [label, body, want] of [
      ['m1-debug', 'void put(struct ring *r, int32_t v) {\n#ifndef DEBUG\n  if (r->n < 0 || r->n >= 8) return;\n#endif\n  r->a[r->n] = v; r->n = r->n + 1;\n}\n', 'DEBUG'],
      ['m5-digraph-ndebug', 'void put(struct ring *r, int32_t v) {\n%:ifndef NDEBUG\n  if (r->n < 0 || r->n >= 8) return;\n#endif\n  r->a[r->n] = v; r->n = r->n + 1;\n}\n', 'NDEBUG'],
      ['m6-cat-ndebug', '#define CAT(a,b) a##b\nvoid put(struct ring *r, int32_t v) {\n#if !CAT(ND,EBUG)\n  if (r->n < 0 || r->n >= 8) return;\n#endif\n  r->a[r->n] = v; r->n = r->n + 1;\n}\n', '##'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, macroHdr + body)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
    }

    // (4) m2, m3, m4, m7: under the closed-world preprocessor allowlist, conditionals referencing
    // predefined macros (__x86_64__, __clang__, __STDC_VERSION__) or __has_* queries are refused
    // (exit 2) naming the macro/operator and line; clean files still report target, compiler +
    // absolute compilerPath, effective std, and __STDC_VERSION__ across default/-std=c23/-std=c11.
    for (const [label, cond, want] of [
      ['m2_arch', 'defined(__x86_64__) || defined(__aarch64__) || defined(__LP64__)', '__x86_64__'],
      ['m3_builtin', '__has_builtin(__builtin_trap)', '__has_builtin'],
      ['m4_stdc', '__STDC_VERSION__ >= 201710L', '__STDC_VERSION__'],
      ['m7_not_clang', '!defined(__clang__)', '__clang__'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, macroHdr + `void put(struct ring *r, int32_t v) {\n#if ${cond}\n  if (r->n < 0 || r->n >= 8) return;\n#endif\n  r->a[r->n] = v; r->n = r->n + 1;\n}\n`)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
      expect(res.rules[0]?.refusals[0]?.where, `${label} reports line 5`).toContain(':5:')
    }

    const cleanStd = join(dir, 'clean_std.c')
    writeFileSync(cleanStd, macroHdr + 'void put(struct ring *r, int32_t v) {\n  if (r->n < 0 || r->n >= 8) return;\n  r->a[r->n] = v; r->n = r->n + 1;\n}\n')
    const rStdText = runCliText(['check', '--no-propose', cleanStd])
    expect(rStdText.code).toBe(0)
    expect(rStdText.out).toMatch(/macro config: target: \S+; compiler: clang \S+ \(\/\S+\); libc: [^;]+; user files: \d+ \(sha256:[0-9a-f]{64}\); system headers: \d+ \(sha256:[0-9a-f]{64}\); std: (?:gnu|c)(?:17|23) \(__STDC_VERSION__=(?:201710L|202311L)\); env: scrubbed; -I flags: none; -D flags: none; NDEBUG=undefined, __OPTIMIZE__=undefined, DEBUG=undefined/)

    const rStdC23 = await check([cleanStd], {flags: ['-std=c23'], propose: false})
    expect(rStdC23.exit).toBe(0)
    expect(rStdC23.rules[0]?.safety).toMatchObject({
      status: 'proven',
      coveredFunctions: ['put'],
      macroConfig: {std: 'c23', stdcVersion: '202311L', envScrubbed: true, ndebugDefined: false, optimizeDefined: false, debugDefined: false},
    })
    const mc23 = (rStdC23.rules[0]?.safety as {macroConfig?: {target?: string, compilerPath?: string}})?.macroConfig
    expect(mc23?.target).toMatch(/\S+-\S+/)
    expect(mc23?.compilerPath).toMatch(/^\//)

    const rStdC11 = await check([cleanStd], {flags: ['-std=c11'], propose: false})
    expect(rStdC11.exit).toBe(0)
    expect(rStdC11.rules[0]?.safety).toMatchObject({
      status: 'proven',
      macroConfig: {std: 'c11', stdcVersion: '201112L', envScrubbed: true},
    })
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 12: macro expansion in system headers (mx1/mx2/w4/-D), scrubbed clang env (cp1/cp2/CCC_OVERRIDE_OPTIONS), -Os/sanitizer/DEBUG=2/NDEBUG=0 invariance (os1/dbg), and CLI text -I & env reporting', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe12-'))
  try {
    // (1) mx1, mx2, w4, and -D command-line macro hijack inside a system header (<stddef.h>):
    // A node is system only if BOTH spelling and expansion locations are system files, and any
    // user-defined or -D macro expanded inside a system header is refused (exit 2).
    const mxBase = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n'
    const mxTail = '#include <stddef.h>\n#undef ptrdiff_t\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n'
    for (const [label, code, flags] of [
      ['mx1-fn', mxBase + '#define ptrdiff_t PD_; int32_t pub(int32_t x, int32_t y) { return x / y; } typedef long PD2_\n' + mxTail, [] as string[]],
      ['mx2-ctor', mxBase + '#define ptrdiff_t PD_; __attribute__((constructor)) static void boot(void) { volatile int32_t z = 0; int32_t a[8]; a[8 + z] = 1 / z; } typedef long PD2_\n' + mxTail, [] as string[]],
      ['w4-size-t', mxBase + 'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n#define size_t SZ_; int32_t (*leak(void))(struct ring *, int32_t); typedef unsigned long SZ2_\n#include <stddef.h>\n#undef size_t\n', [] as string[]],
      ['mx-cli-D', mxBase + '#include <stddef.h>\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', ['-Dptrdiff_t=PD_; int32_t pub(int32_t x, int32_t y) { return x / y; } typedef long PD2_']],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, code)
      const res = await check([f], {propose: false, ...(flags.length ? {flags: [...flags]} : {})})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (2) cp1, cp2, CCC_OVERRIDE_OPTIONS: Clang invocations run in a scrubbed environment so
    // CPATH / C_INCLUDE_PATH / CCC_OVERRIDE_OPTIONS cannot smuggle headers as system dirs.
    const cpRoot = join(dir, 'cp'), cpInc = join(cpRoot, 'inc'), cpSrc = join(cpRoot, 'src')
    mkdirSync(cpInc, {recursive: true})
    mkdirSync(cpSrc, {recursive: true})
    writeFileSync(join(cpInc, 'evil.h'), '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n')
    const cpFile = join(cpSrc, 'ring.c')
    writeFileSync(cpFile, '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n#include "evil.h"\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    for (const [label, extraEnv] of [
      ['cp1-CPATH', {CPATH: cpInc}],
      ['cp2-C_INCLUDE_PATH', {C_INCLUDE_PATH: cpInc}],
      ['cp3-CCC_OVERRIDE_OPTIONS', {CCC_OVERRIDE_OPTIONS: `+-isystem${cpInc}`}],
    ] as const) {
      const rEnv = runCliText(['check', '--no-propose', cpFile], extraEnv)
      expect(rEnv.code, `${label} must exit 2 (env scrubbed)`).toBe(2)
      expect(rEnv.out, `${label} must report unchecked`).toContain('unchecked (covers: none)')
      expect(rEnv.out, `${label} must not prove`).not.toContain('proven (covers:')
    }

    // (3) q1/q2: #pragma clang system_header and _Pragma("clang system_header") refused (exit 2).
    for (const [label, pragmaLine] of [
      ['q1-pragma-clang', '#pragma clang system_header\n'],
      ['q2-op-pragma-clang', '_Pragma("clang system_header")\n'],
    ] as const) {
      const qRoot = join(dir, label), qInc = join(qRoot, 'inc'), qSrc = join(qRoot, 'src')
      mkdirSync(qInc, {recursive: true})
      mkdirSync(qSrc, {recursive: true})
      writeFileSync(join(qInc, 'evil.h'), '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n')
      writeFileSync(join(qInc, 'h.h'), pragmaLine + '#include "evil.h"\n')
      const f = join(qSrc, 'ring.c')
      writeFileSync(f, '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n#include "h.h"\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
      const res = await check([f], {flags: [`-I${qInc}`], propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (4) os1, sanitizer macros, dbg (DEBUG > 1), NDEBUG=0: invariance check covers -Os,
    // -fsanitize=address,undefined, __SANITIZE_*, -DDEBUG=2, and -DNDEBUG=0 -> exit 2.
    const invHdr = '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\n'
    for (const [label, cond, want] of [
      ['os1-opt-size', '#ifdef __OPTIMIZE_SIZE__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__OPTIMIZE_SIZE__'],
      ['san-has-feat', '#if __has_feature(address_sanitizer)\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__has_feature'],
      ['san-macro', '#ifdef __SANITIZE_UNDEFINED__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__SANITIZE_'],
      ['dbg-gt-1', '#if DEBUG > 1\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', 'DEBUG'],
      ['ndebug-zero', '#if defined(NDEBUG) && NDEBUG == 0\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', 'NDEBUG'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, invHdr + cond + 'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < LIM) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = r->n + 1; }\n')
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
    }

    // (5) CLI TEXT and JSON report scrubbed env and -I flags explicitly.
    const incRoot = join(dir, 'clean-inc'), incDir = join(incRoot, 'inc'), srcDir = join(incRoot, 'src')
    mkdirSync(incDir, {recursive: true})
    mkdirSync(srcDir, {recursive: true})
    writeFileSync(join(incDir, 'lim.h'), '#define RING_LIM 8\n')
    const incFile = join(srcDir, 'ring.c')
    writeFileSync(incFile, '// gdp: safety\n#include <stdint.h>\n#include "lim.h"\nstruct ring { int32_t n; int32_t a[RING_LIM]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < RING_LIM) return r->a[r->n]; return 0; }\n')
    writeFileSync(join(srcDir, 'gdp.toml'), `flags = ["-I${incDir}"]\n`)
    const rIncText = runCliText(['check', '--no-propose', incFile])
    expect(rIncText.code).toBe(0)
    expect(rIncText.out).toContain('env: scrubbed')
    expect(rIncText.out).toContain(`-I flags: -I${incDir}`)
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 13: closed-world compiler verification & fixed PATH (e1-e3), closed-world #if macro allowlist (c_*), invocation-dependent macros (f1-f4), and #pragma once / user #define positive controls', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe13-'))
  try {
    // (1) e1, e2, e3: custom clang in gdp.toml or options is refused; PATH wrapper is ignored
    // because PATH is scrubbed to a fixed safe list; verifyClangBinary refuses both shell wrappers
    // and compiled native wrapper binaries that inject -isystem or -D.
    const bin1 = join(dir, 'bin1'), bin2 = join(dir, 'bin2'), e1Inc = join(dir, 'e1inc')
    mkdirSync(bin1, {recursive: true})
    mkdirSync(bin2, {recursive: true})
    mkdirSync(e1Inc, {recursive: true})
    const realClang = resolveSafetyClang('clang', join(dir, 'probe.c')).bin
    writeFileSync(join(e1Inc, 'util.h'), '#include <stdint.h>\nint32_t pub(int32_t x, int32_t y) { return x / y; }\n')
    const wrap1 = join(bin1, 'clang')
    writeFileSync(wrap1, `#!/bin/sh\nexec ${realClang} -isystem ${e1Inc} "$@"\n`)
    chmodSync(wrap1, 0o755)
    const wrap2 = join(bin2, 'clang')
    writeFileSync(wrap2, `#!/bin/sh\nexec ${realClang} -DLIM=8 "$@"\n`)
    chmodSync(wrap2, 0o755)

    // e1: gdp.toml clang = wrapper adding -isystem -> exit 2
    const e1Dir = join(dir, 'e1')
    mkdirSync(e1Dir, {recursive: true})
    writeFileSync(join(e1Dir, 'gdp.toml'), `clang = ${JSON.stringify(wrap1)}\n`)
    const e1File = join(e1Dir, 'ring.c')
    writeFileSync(e1File, '// gdp: safety\n#include <stdint.h>\n#include <util.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rE1 = await check([e1File], {propose: false})
    expect(rE1.exit).toBe(2)
    expect(rE1.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rE1.rules[0]?.refusals.map(r => r.what).join('; ')).toMatch(/custom compiler/)

    // e3: gdp.toml clang = wrapper adding -DLIM=8 -> exit 2
    const e3Dir = join(dir, 'e3')
    mkdirSync(e3Dir, {recursive: true})
    writeFileSync(join(e3Dir, 'gdp.toml'), `clang = ${JSON.stringify(wrap2)}\n`)
    const e3File = join(e3Dir, 'ring.c')
    writeFileSync(e3File, '// gdp: safety\n#include <stdint.h>\n#ifndef LIM\n#define LIM 9\n#endif\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < LIM) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = r->n + 1; }\n')
    const rE3 = await check([e3File], {propose: false})
    expect(rE3.exit).toBe(2)
    expect(rE3.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // e2: PATH wrapper first on PATH adding -DLIM=8 (or -isystem) is ignored due to fixed safe PATH -> exit 2
    const e2Dir = join(dir, 'e2')
    mkdirSync(e2Dir, {recursive: true})
    const e2File = join(e2Dir, 'ring.c')
    writeFileSync(e2File, '// gdp: safety\n#include <stdint.h>\n#ifndef LIM\n#define LIM 9\n#endif\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < LIM) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = r->n + 1; }\n')
    const rE2 = runCliText(['check', '--no-propose', e2File], {PATH: `${bin2}:${process.env.PATH ?? ''}`})
    expect(rE2.code).toBe(2)
    expect(rE2.out).toContain('unchecked (covers: none)')
    expect(rE2.out).not.toContain('proven (covers:')

    const e2IncFile = join(e2Dir, 'inc_ring.c')
    writeFileSync(e2IncFile, '// gdp: safety\n#include <stdint.h>\n#include <util.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rE2Inc = runCliText(['check', '--no-propose', e2IncFile], {PATH: `${bin1}:${process.env.PATH ?? ''}`})
    expect(rE2Inc.code).toBe(2)
    expect(rE2Inc.out).toContain('unchecked (covers: none)')

    // Direct verifyClangBinary checks: rejects shell wrappers AND compiled native wrapper binaries.
    expect(() => verifyClangBinary(wrap1, e1File)).toThrow(Refusal)
    expect(() => verifyClangBinary(wrap2, e3File)).toThrow(Refusal)
    const nativeWrapSrc = join(dir, 'wrap.c')
    const nativeWrapBin = join(dir, 'clang-wrap')
    writeFileSync(nativeWrapSrc, `#include <unistd.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  char **na = malloc((size_t)(argc + 2) * sizeof(char *));
  na[0] = ${JSON.stringify(realClang)};
  na[1] = "-DLIM=8";
  for (int i = 1; i < argc; i++) na[i + 1] = argv[i];
  na[argc + 1] = NULL;
  execv(${JSON.stringify(realClang)}, na);
  return 127;
}
`)
    execFileSync(realClang, [nativeWrapSrc, '-o', nativeWrapBin])
    expect(() => verifyClangBinary(nativeWrapBin, e3File)).toThrow(Refusal)

    // (2) Closed-world #if/#ifdef/#ifndef/#elif/defined()/__has_* allowlist:
    // Refuses every predefined or undefined-elsewhere macro (c___PIC__, c___AVX2__, c__REENTRANT,
    // c___SANITIZE_THREAD__, c___SSP_STRONG__, __FAST_MATH__, __CHAR_UNSIGNED__, indirect alias,
    // non-#if predefined macro use, and token pasting) with its name and line -> exit 2.
    const ringTail = 'struct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < LIM) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 8) r->n = r->n + 1; }\n'
    for (const [label, pre, want, wantLine] of [
      ['c___PIC__', '#ifndef __PIC__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__PIC__', 3],
      ['c___AVX2__', '#ifdef __AVX2__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__AVX2__', 3],
      ['c__REENTRANT', '#ifdef _REENTRANT\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '_REENTRANT', 3],
      ['c___SANITIZE_THREAD__', '#ifdef __SANITIZE_THREAD__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__SANITIZE_THREAD__', 3],
      ['c___SSP_STRONG__', '#ifdef __SSP_STRONG__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__SSP_STRONG__', 3],
      ['c___FAST_MATH__', '#ifdef __FAST_MATH__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__FAST_MATH__', 3],
      ['c___CHAR_UNSIGNED__', '#ifdef __CHAR_UNSIGNED__\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__CHAR_UNSIGNED__', 3],
      ['c_indirect_alias', '#define MY_ALIAS __AVX2__\n#if MY_ALIAS\n#define LIM 9\n#else\n#define LIM 8\n#endif\n', '__AVX2__', 4],
      ['c_expr_pic', '#define LIM (8 + (2 - __PIC__))\n', '__PIC__', 3],
      ['c_pragma_pack', '#pragma pack(1)\n#define LIM 8\n', '#pragma pack(1)', 3],
      ['g1_macro_pragma', '#define P(x) _Pragma(#x)\nP(weak evil = get)\n#define LIM 8\n', '_Pragma', 3],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, '// gdp: safety\n#include <stdint.h>\n' + pre + ringTail)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
      expect(res.rules[0]?.refusals[0]?.where, `${label} reports line ${wantLine}`).toContain(`:${wantLine}:`)
    }

    // (3) Invocation-dependent predefined macros (f1-f4: __FILE__, plus __BASE_FILE__, __FILE_NAME__,
    // __TIMESTAMP__, __DATE__, __TIME__, __COUNTER__, __LINE__, __INCLUDE_LEVEL__) refused -> exit 2.
    for (const [label, lineCode, want] of [
      ['f4_file_arr', 'struct ring { int32_t n; int32_t a[sizeof(__FILE__) > 20 ? 9 : 8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 9) return r->a[r->n]; return 0; }\n', '__FILE__'],
      ['f_base_file', 'struct ring { int32_t n; int32_t a[sizeof(__BASE_FILE__) > 1 ? 8 : 4]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__BASE_FILE__'],
      ['f_file_name', 'struct ring { int32_t n; int32_t a[sizeof(__FILE_NAME__) > 1 ? 8 : 4]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__FILE_NAME__'],
      ['f_timestamp', 'struct ring { int32_t n; int32_t a[sizeof(__TIMESTAMP__) > 1 ? 8 : 4]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__TIMESTAMP__'],
      ['f_date', 'struct ring { int32_t n; int32_t a[sizeof(__DATE__) > 1 ? 8 : 4]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__DATE__'],
      ['f_time', 'struct ring { int32_t n; int32_t a[sizeof(__TIME__) > 1 ? 8 : 4]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__TIME__'],
      ['f_counter', 'struct ring { int32_t n; int32_t a[8 + __COUNTER__]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__COUNTER__'],
      ['f_line', 'struct ring { int32_t n; int32_t a[__LINE__ + 5]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n', '__LINE__'],
      ['f_spliced_file', 'struct ring { int32_t n; int32_t a[sizeof(__FI\\\nLE__) > 20 ? 9 : 8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 9) return r->a[r->n]; return 0; }\n', '__FILE__'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, '// gdp: safety\n#include <stdint.h>\n' + lineCode)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
      expect(res.rules[0]?.refusals[0]?.where, `${label} reports line 3`).toContain(':3:')
    }

    // (4) Positive closed-world controls: #pragma once in a user header, user-defined macros, and
    // explicit -D flags listed in the verdict ARE allowed in #if/#ifdef/#elif/defined(), and the
    // verdict reports the verified absolute compilerPath in both JSON and CLI TEXT.
    const okDir = join(dir, 'ok_allow')
    mkdirSync(okDir, {recursive: true})
    writeFileSync(join(okDir, 'cfg.h'), '#pragma once\n#define USER_CAP 8\n')
    const okFile = join(okDir, 'ring.c')
    writeFileSync(okFile, `// gdp: safety
#include <stdint.h>
#include "cfg.h"
#if defined(USER_CAP) && USER_CAP == 8 && defined(CLI_LIM) && CLI_LIM == 8
#define EFF_LIM USER_CAP
#else
#define EFF_LIM 4
#endif
struct ring { int32_t n; int32_t a[EFF_LIM]; };
int32_t get(struct ring *r) { if (r->n >= 0 && r->n < EFF_LIM) return r->a[r->n]; return 0; }
void put(struct ring *r) { if (r->n >= 0 && r->n < 7) r->n = r->n + 1; }
`)
    const rOk = await check([okFile], {flags: ['-DCLI_LIM=8'], propose: false})
    expect(rOk.exit).toBe(0)
    expect(rOk.rules[0]?.safety).toMatchObject({
      status: 'proven',
      coveredFunctions: ['get', 'put'],
      macroConfig: {compilerPath: realClang, envScrubbed: true, defines: ['-DCLI_LIM=8']},
    })
    writeFileSync(join(okDir, 'gdp.toml'), 'flags = ["-DCLI_LIM=8"]\n')
    const rOkTxt = runCliText(['check', '--no-propose', okFile])
    expect(rOkTxt.code).toBe(0)
    expect(rOkTxt.out).toContain(`(${realClang})`)
    expect(rOkTxt.out).toContain('-D flags: -DCLI_LIM=8')
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 14: Clang-native lexer/token audit (s1/s2/s3/al/a-k), all 9 trigraphs, non-C23 digit-quote refusal vs C23 positive control, closed-world flag allowlist, and libc version reporting', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe14-'))
  try {
    const H = '// gdp: safety\n#include <stdint.h>\n'
    const tail = 'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 4) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 3) r->n = r->n + 1; }\n'

    // (1) probe10 s1/r40, s1/r200, s2/t40, s3/tm, al/j, al/k: trigraph comment-hide (`// note ??/`)
    // and non-C23 digit-quote (`0'x'`) can never hide __FILE__, __DATE__, or predefined macros -> exit 2.
    for (const [label, src, want] of [
      ['s1_r40', H + "#define SECOND(a, b) b\nstruct ring { int32_t a[SECOND(0'x', sizeof __FILE__)]; int32_t n; };\n" +
        'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n', "digit followed by quote (')"],
      ['s2_t40', H + '// layout note ??/\nstruct ring { int32_t a[sizeof __FILE__]; int32_t n; };\n' +
        'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n', 'trigraph sequence ??/'],
      ['s3_tm', H + "// layout note ??/\nstruct ring { int32_t a['9' - __DATE__[5] + 1]; int32_t n; };\n" +
        'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 10) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 9) r->n = r->n + 1; }\n', 'trigraph sequence ??/'],
      ['al_j', H + '#include <limits.h>\n// note ??/\n#if __PIC__ == 2\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, 'trigraph sequence ??/'],
      ['al_k', H + "#include <limits.h>\n#define SECOND(a,b) b\nenum { K = SECOND(0'x', __STDC_HOSTED__ * 8) };\nstruct ring { int32_t a[K]; int32_t n; };\n" + tail, "digit followed by quote (')"],
      ['al_a', H + '#include <limits.h>\n#if INT_MAX > 100\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, 'INT_MAX'],
      ['al_b', H + '#include <limits.h>\n#if __SIZEOF_LONG__ == 8\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, '__SIZEOF_LONG__'],
      ['al_c', H + '#include <limits.h>\n#if __has_include(<stdint.h>)\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, '__has_include'],
      ['al_d', H + '#include <limits.h>\nstruct ring { int32_t a[__SIZEOF_LONG__]; int32_t n; };\n' + tail, '__SIZEOF_LONG__'],
      ['al_f', H + '#include <limits.h>\n#ifdef INT_MAX\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, 'INT_MAX'],
      ['al_h', H + '#include <limits.h>\n#define F(x) defined(x)\n#if F(__x86_64__)\n#define K 8\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\n' + tail, ''],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, src)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      if (want) expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} mentions ${want}`).toContain(want)
    }

    // (2) All 9 C trigraph sequences refused anywhere in user files (even inside comments/strings).
    for (const [idx, tri] of ['??=', '??/', "??'", '??(', '??)', '??!', '??<', '??>', '??-'].entries()) {
      const f = join(dir, `tri_${idx}.c`)
      writeFileSync(f, H + `/* ${tri} */\nstruct ring { int32_t a[8]; int32_t n; };\n` + tail)
      const res = await check([f], {propose: false})
      expect(res.exit, `trigraph ${tri} must exit 2`).toBe(2)
      expect(res.rules[0]?.refusals.map(r => r.what).join('; ')).toContain(`trigraph sequence ${tri}`)
    }

    // (3) Non-C23 digit-quote (`0'x'`, `1'000`) refused in default/gnu17; C23 digit separator (`1'000`)
    // under `-std=c23` and ordinary char literals (`'0'`, `'9'`, `'\0'`) in default mode still prove.
    const nonC23Sep = join(dir, 'non_c23_sep.c')
    writeFileSync(nonC23Sep, H + "struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { int32_t k = 1'000; (void)k; if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n")
    const rNonC23 = await check([nonC23Sep], {propose: false})
    expect(rNonC23.exit).toBe(2)
    expect(rNonC23.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    const c23Ok = join(dir, 'c23_sep_ok.c')
    writeFileSync(c23Ok, H + "struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { int32_t k = 1'000; if (k == 1'000 && r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n")
    const rC23Ok = await check([c23Ok], {flags: ['-std=c23'], propose: false})
    expect(rC23Ok.exit).toBe(0)
    expect(rC23Ok.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get']})

    // (4) Closed-world flag allowlist: refuses -isystem, -include, -trigraphs, -funsigned-char,
    // and audits 2-argument `-D FOO=__FILE__`.
    const cleanFlagFile = join(dir, 'clean_flag.c')
    writeFileSync(cleanFlagFile, H + "/* '\tLoc=<FAKE:1:1>\n * résumé */\r\n#include <stdbool.h>\r\nstruct ring { int32_t a[('9' - '0') + _Generic((char)0, signed char: 0, unsigned char: 1, default: 2)]; int32_t n; };\r\nint32_t get(struct ring *r) { _Bool ok = (r->n >= 0 && r->n < 4); if (ok) return r->a[r->n]; return 0; }\r\n")
    const rEdgeOk = await check([cleanFlagFile], {propose: false})
    expect(rEdgeOk.exit).toBe(0)
    expect(rEdgeOk.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get']})

    for (const [label, badFlags] of [
      ['flag_isystem', ['-isystem', dir]],
      ['flag_include', ['-include', cleanFlagFile]],
      ['flag_trigraphs', ['-trigraphs']],
      ['flag_uchar', ['-funsigned-char']],
      ['flag_2arg_D_file', ['-D', 'BAD=__FILE__']],
    ] as const) {
      const res = await check([cleanFlagFile], {flags: [...badFlags], propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (5) libc + version reported in both JSON (`macroConfig.libc`) and CLI TEXT (`; libc: ...;`)
    // including files relying on system constants like PATH_MAX (al/i) and __GLIBC_MINOR__ (al/e).
    const alI = join(dir, 'al_i.c')
    writeFileSync(alI, H + '#define _GNU_SOURCE 1\n#include <limits.h>\nstruct ring { int32_t a[PATH_MAX / 1024]; int32_t n; };\n' + tail)
    const rAlI = await check([alI], {propose: false})
    expect(rAlI.exit).toBe(0)
    const libcVal = (rAlI.rules[0]?.safety as {macroConfig?: {libc?: string}})?.macroConfig?.libc
    expect(libcVal).toBeTruthy()
    expect(libcVal).not.toBe('unknown')
    const rAlIText = runCliText(['check', '--no-propose', alI])
    expect(rAlIText.code).toBe(0)
    expect(rAlIText.out).toContain(`; libc: ${libcVal};`)

    if (libcVal?.startsWith('glibc ')) {
      const alE = join(dir, 'al_e.c')
      writeFileSync(alE, H + '#define _GNU_SOURCE 1\n#include <limits.h>\nstruct ring { int32_t a[__GLIBC_MINOR__]; int32_t n; };\n' + tail)
      const rAlE = await check([alE], {propose: false})
      expect(rAlE.exit).toBe(0)
      expect((rAlE.rules[0]?.safety as {macroConfig?: {libc?: string}})?.macroConfig?.libc).toBe(libcVal)
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 15: closed-world __builtin_* allowlist & AST-fact differential (b1-b4, ff), byte-contiguous raw-token parser (fg/fgc), -D newline hardening (d1), encoding plumbing, and system header SHA-256 digest (z2)', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe15-'))
  try {
    const H = '// gdp: safety\n#include <stdint.h>\n'
    const realClang = resolveSafetyClang('clang', join(dir, 'probe.c')).bin

    // (1) Closed-world __builtin_* allowlist + AST-fact differential: __builtin_FILE,
    // __builtin_FILE_NAME, __builtin_strlen (b1, b2, b3, b4, ff) are refused -> exit 2.
    for (const [label, src, want] of [
      ['b1_file_arr', H + 'struct ring { int32_t a[__builtin_strlen(__builtin_FILE())]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n', '__builtin_'],
      ['b2_file_cond', H + 'struct ring { int32_t a[40]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < (int32_t)__builtin_strlen(__builtin_FILE())) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 100) r->n = r->n + 1; }\n', '__builtin_'],
      ['b3_file_enum', H + 'enum { L = sizeof(struct { char c[__builtin_strlen(__builtin_FILE())]; }) };\nstruct ring { int32_t a[L]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n', '__builtin_'],
      ['b4_file_tern', H + 'struct ring { int32_t a[__builtin_strlen(__builtin_FILE()) < 10 ? 40 : 4]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n', '__builtin_'],
      ['ff_filename_arr', H + 'struct ring { int32_t a[__builtin_strlen(__builtin_FILE_NAME()) * 5]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 30) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 29) r->n = r->n + 1; }\n', '__builtin_'],
      ['b_func_predef', H + 'struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < (int32_t)sizeof(__func__)) return r->a[r->n]; return 0; }\n', ''],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, src)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      if (want) expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names ${want}`).toContain(want)
    }

    // Positive control: anonymous typedef struct + sizeof(unnamed struct) still proves cleanly
    // through the AST-fact differential (anonymous-tag location normalization).
    const posFile = join(dir, 'pos_anon_struct.c')
    writeFileSync(posFile, H + 'typedef struct { int32_t a[sizeof(struct { char c[8]; })]; int32_t n; } ring_t;\nint32_t get(ring_t *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\nvoid put(ring_t *r) { if (r->n >= 0 && r->n < 7) r->n = r->n + 1; }\n')
    const rPos = await check([posFile], {propose: false})
    expect(rPos.exit).toBe(0)
    expect(rPos.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get', 'put']})

    // (2) Byte-contiguous -dump-raw-tokens parser (fg vs fgc): forged Clang token records inside
    // comments can never split a comment early or swallow a real #if __has_include directive -> exit 2.
    const fgDir = join(dir, 'fg')
    mkdirSync(fgDir, {recursive: true})
    const fgFile = join(fgDir, 'ring.c')
    const pre = `// gdp: safety\n#include <stdint.h>\n/*X'\t\tLoc=<${fgFile}:3:1>\ncomment '/**/\n#if __has_include(<stdint.h>)\n#define CAP 40\n#else\n#define CAP 4\n#endif\n#if 0\n`
    const kLine = pre.split('\n').length
    const tail = '\n#endif\nstruct ring { int32_t a[CAP]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 39) r->n = r->n + 1; }\n'
    writeFileSync(fgFile, pre + '/**/' + tail)
    const rawDump = spawnSync(realClang, ['-x', 'c', '-w', '-Xclang', '-dump-raw-tokens', '-fsyntax-only', fgFile], {encoding: 'utf8'}).stderr ?? ''
    const ctext = `/*X'\t\tLoc=<${fgFile}:3:1>\ncomment '/**/`
    const idxA = rawDump.indexOf(`comment '${ctext}`) + `comment '${ctext}`.length
    const kk = `comment '/**/'\t [StartOfLine]\tLoc=<${fgFile}:${kLine}:1>`
    const idxB = rawDump.indexOf(kk) + "comment '/**/".length
    expect(idxA).toBeGreaterThan(0)
    expect(idxB).toBeGreaterThan(idxA)
    writeFileSync(fgFile, pre + '/**/' + rawDump.slice(idxA, idxB) + tail)
    const rFg = await check([fgFile], {propose: false})
    expect(rFg.exit, 'forged raw-token comment (fg) must exit 2').toBe(2)
    expect(rFg.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    const fgcFile = join(dir, 'fgc.c')
    writeFileSync(fgcFile, H + '#if __has_include(<stdint.h>)\n#define CAP 40\n#else\n#define CAP 4\n#endif\nstruct ring { int32_t a[CAP]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\n')
    const rFgc = await check([fgcFile], {propose: false})
    expect(rFgc.exit, 'fgc control must exit 2').toBe(2)
    expect(rFgc.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (3) d1: newline inside -D flag value cannot shift subsequent -D flags past the audit -> exit 2.
    const d1File = join(dir, 'd1.c')
    writeFileSync(d1File, H + '#if HAVE_Z\n#define K 40\n#else\n#define K 4\n#endif\nstruct ring { int32_t a[K]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 40) return r->a[r->n]; return 0; }\n')
    const rD1 = await check([d1File], {flags: ['-DPAD=1\n2', '-DHAVE_Z=__has_include(<stdint.h>)'], propose: false})
    expect(rD1.exit).toBe(2)
    expect(rD1.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (4) Encoding plumbing: clean UTF-8 BOM + no-trailing-newline proves; hidden __FILE__ under
    // BOM / lone-CR / CRLF-splice / NUL byte is refused -> exit 2.
    const cleanBom = join(dir, 'clean_bom.c')
    writeFileSync(cleanBom, Buffer.concat([Buffer.from([0xef, 0xbb, 0xbf]), Buffer.from(H + 'struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }')]))
    const rBomOk = await check([cleanBom], {propose: false})
    expect(rBomOk.exit).toBe(0)
    expect(rBomOk.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get']})

    for (const [label, buf] of [
      ['enc_bom_file', Buffer.concat([Buffer.from([0xef, 0xbb, 0xbf]), Buffer.from(H + 'struct ring { int32_t a[sizeof __FILE__]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')])],
      ['enc_lonecr_file', Buffer.from((H + 'struct ring { int32_t a[sizeof __FILE__]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n').replace(/\n/g, '\r'))],
      ['enc_nul_byte', Buffer.concat([Buffer.from(H), Buffer.from([0x2f, 0x2a, 0x20, 0x00, 0x20, 0x2a, 0x2f, 0x0a]), Buffer.from('struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')])],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, buf)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
    }

    // (5) System header digest & list (z2 class): every included system header's resolved path +
    // exact SHA-256 is reported in JSON (`macroConfig.systemHeaders`) and summarized as one SHA-256
    // (`macroConfig.systemHeadersSha256`) in both JSON and CLI TEXT; including an additional system
    // header (<limits.h> vs <stdint.h> alone) changes both the header list and summary digest.
    const hdr1 = join(dir, 'hdr_stdint.c')
    const hdr2 = join(dir, 'hdr_limits.c')
    writeFileSync(hdr1, H + 'struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    writeFileSync(hdr2, H + '#include <limits.h>\nstruct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rH1 = await check([hdr1], {propose: false})
    const rH2 = await check([hdr2], {propose: false})
    expect(rH1.exit).toBe(0)
    expect(rH2.exit).toBe(0)
    const mc1 = (rH1.rules[0]?.safety as {macroConfig?: {systemHeadersSha256?: string, systemHeaders?: {path: string, sha256: string}[]}})?.macroConfig
    const mc2 = (rH2.rules[0]?.safety as {macroConfig?: {systemHeadersSha256?: string, systemHeaders?: {path: string, sha256: string}[]}})?.macroConfig
    expect(mc1?.systemHeadersSha256).toMatch(/^[0-9a-f]{64}$/)
    expect(mc2?.systemHeadersSha256).toMatch(/^[0-9a-f]{64}$/)
    expect(mc1?.systemHeaders?.length).toBeGreaterThan(0)
    expect(mc2?.systemHeaders?.length).toBeGreaterThan(mc1!.systemHeaders!.length)
    expect(mc2?.systemHeadersSha256).not.toBe(mc1?.systemHeadersSha256)
    expect(mc1?.systemHeaders?.some(h => h.path.endsWith('/stdint.h') && /^[0-9a-f]{64}$/.test(h.sha256))).toBe(true)
    expect(mc2?.systemHeaders?.some(h => h.path.endsWith('/limits.h') && /^[0-9a-f]{64}$/.test(h.sha256))).toBe(true)
    const rH2Text = runCliText(['check', '--no-propose', hdr2])
    expect(rH2Text.code).toBe(0)
    expect(rH2Text.out).toContain(`; system headers: ${mc2!.systemHeaders!.length} (sha256:${mc2!.systemHeadersSha256});`)
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 16: closed-world user include boundary & /proc|/dev|/sys refusal (w1-w3, symlinks, outside-root), colon paths (c:olon), and userFiles SHA-256 reporting', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe16-'))
  try {
    const H = '// gdp: safety\n#include <stdint.h>\n'
    const cliPath = new URL('./cli.ts', import.meta.url).pathname

    // (1) w1 & w2: #include "/dev/stdin" -> exit 2 (unchecked), naming /dev/stdin.
    for (const [label, body] of [
      ['w1', 'struct ring { int32_t n; int32_t a[8\n#include "/dev/stdin"\n]; };\n'],
      ['w2', 'struct ring { int32_t a[8\n#include "/dev/stdin"\n]; int32_t n; };\n'],
    ] as const) {
      const f = join(dir, `${label}.c`)
      writeFileSync(f, H + body + 'int32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 7) r->n = r->n + 1; }\n')
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must exit 2`).toBe(2)
      expect(res.rules[0]?.safety, `${label} must be unchecked`).toMatchObject({status: 'unchecked'})
      expect(res.rules[0]?.refusals.map(r => r.what).join('; '), `${label} names /dev/stdin`).toContain('/dev/stdin')
    }

    // (2) w3: #include "/proc/self/cwd/cap.h" even when invoked with cwd containing cap.h -> exit 2,
    // naming /proc/self/cwd/cap.h (via subprocess with cwd=w3/b1 where cap.h holds `8`).
    const w3Root = join(dir, 'w3')
    const w3Src = join(w3Root, 'src')
    const w3B1 = join(w3Root, 'b1')
    mkdirSync(w3Src, {recursive: true})
    mkdirSync(w3B1, {recursive: true})
    writeFileSync(join(w3B1, 'cap.h'), '8\n')
    const w3Ring = join(w3Src, 'ring.c')
    writeFileSync(w3Ring, H + 'struct ring { int32_t a[\n#include "/proc/self/cwd/cap.h"\n]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 7) r->n = r->n + 1; }\n')
    const w3Proc = spawnSync(process.execPath, [cliPath, 'check', '--no-propose', '--json', w3Ring], {cwd: w3B1, encoding: 'utf8'})
    expect(w3Proc.status, 'w3 run from b1 must exit 2').toBe(2)
    const w3Json = JSON.parse(w3Proc.stdout) as {rules: {safety?: {status: string}, refusals: {what: string}[]}[]}
    expect(w3Json.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(w3Json.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('/proc/self/cwd/cap.h')

    // (3) Symlinks & outside-root boundary:
    // (a) symlink file inside root -> /proc/self/cwd/cap.h (invoked from w3/b1) -> exit 2
    // (b) symlink directory inside root -> /proc/self/cwd (even when cwd IS inside root!) -> exit 2
    // (c) symlink file inside root -> regular file outside root -> exit 2
    // (d) direct absolute #include to regular file outside root and not in -I -> exit 2
    // (e) -I /proc/self/cwd -> exit 2
    const outsideDir = join(dir, 'outside')
    mkdirSync(outsideDir, {recursive: true})
    const extHdr = join(outsideDir, 'ext.h')
    writeFileSync(extHdr, '#define EXT_CAP 8\n')

    const projDir = join(dir, 'proj')
    const projB1 = join(projDir, 'b1')
    mkdirSync(projB1, {recursive: true})
    writeFileSync(join(projB1, 'cap.h'), '8\n')
    symlinkSync('/proc/self/cwd/cap.h', join(projDir, 'sym_proc.h'))
    symlinkSync('/proc/self/cwd', join(projDir, 'sym_proc_dir'))
    symlinkSync(extHdr, join(projDir, 'sym_out.h'))

    const symProcFile = join(projDir, 'use_sym_proc.c')
    writeFileSync(symProcFile, H + 'struct ring { int32_t a[\n#include "sym_proc.h"\n]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rSymProc = spawnSync(process.execPath, [cliPath, 'check', '--no-propose', '--json', symProcFile], {cwd: projB1, encoding: 'utf8'})
    expect(rSymProc.status, 'symlink to /proc/self/cwd/cap.h must exit 2').toBe(2)
    expect(JSON.parse(rSymProc.stdout).rules[0]?.safety).toMatchObject({status: 'unchecked'})

    const symDirFile = join(projDir, 'use_sym_dir.c')
    writeFileSync(symDirFile, H + 'struct ring { int32_t a[\n#include "sym_proc_dir/cap.h"\n]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rSymDir = spawnSync(process.execPath, [cliPath, 'check', '--no-propose', '--json', symDirFile], {cwd: projB1, encoding: 'utf8'})
    expect(rSymDir.status, 'symlink dir to /proc/self/cwd inside root must exit 2').toBe(2)
    expect(JSON.parse(rSymDir.stdout).rules[0]?.safety).toMatchObject({status: 'unchecked'})

    const symOutFile = join(projDir, 'use_sym_out.c')
    writeFileSync(symOutFile, H + '#include "sym_out.h"\nstruct ring { int32_t a[EXT_CAP]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rSymOut = await check([symOutFile], {root: projDir, propose: false})
    expect(rSymOut.exit, 'symlink outside root must exit 2').toBe(2)
    expect(rSymOut.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rSymOut.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('sym_out.h')

    const absOutFile = join(projDir, 'use_abs_out.c')
    writeFileSync(absOutFile, H + `#include "${extHdr}"\nstruct ring { int32_t a[EXT_CAP]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n`)
    const rAbsOut = await check([absOutFile], {root: projDir, propose: false})
    expect(rAbsOut.exit, 'absolute include outside root/-I must exit 2').toBe(2)
    expect(rAbsOut.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rAbsOut.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('ext.h')

    const procIncFile = join(projDir, 'use_proc_inc.c')
    writeFileSync(procIncFile, H + 'struct ring { int32_t a[8]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rProcInc = await check([procIncFile], {root: projDir, flags: ['-I/proc/self/cwd'], propose: false})
    expect(rProcInc.exit, '-I/proc/self/cwd must exit 2').toBe(2)
    expect(rProcInc.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (4) Paths containing colons (`c:olon/ring.c`): clean file proves (exit 0) AND hidden
    // invocation-dependent / predefined macros inside `c:olon/` are still refused (exit 2),
    // confirming `dumpUserExpandedTokens` parses colon paths instead of skipping them.
    const colonDir = join(dir, 'c:olon')
    mkdirSync(colonDir, {recursive: true})
    const colonClean = join(colonDir, 'ring.c')
    writeFileSync(colonClean, H + 'struct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < 7) r->n = r->n + 1; }\n')
    const rColonOk = await check([colonClean], {propose: false})
    expect(rColonOk.exit, 'c:olon/ring.c clean must prove (exit 0)').toBe(0)
    expect(rColonOk.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get', 'put']})

    const colonBadFile = join(colonDir, 'bad_file.c')
    writeFileSync(colonBadFile, H + 'struct ring { int32_t a[sizeof __FILE__]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rColonBad = await check([colonBadFile], {propose: false})
    expect(rColonBad.exit, 'c:olon/bad_file.c must exit 2').toBe(2)
    expect(rColonBad.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    const colonBadLine = join(colonDir, 'bad_line.c')
    writeFileSync(colonBadLine, H + 'struct ring { int32_t a[__LINE__]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < 8) return r->a[r->n]; return 0; }\n')
    const rColonLine = await check([colonBadLine], {propose: false})
    expect(rColonLine.exit, 'c:olon/bad_line.c must exit 2').toBe(2)
    expect(rColonLine.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (5) User file digest & list (`macroConfig.userFiles` and `macroConfig.userFilesSha256`) in
    // JSON and CLI TEXT: exact SHA-256 of every user file under root and listed `-I` dirs, and
    // editing an included user header changes both its per-file hash and the summary digest.
    const incDir = join(dir, 'inc')
    mkdirSync(incDir, {recursive: true})
    writeFileSync(join(incDir, 'inc_cap.h'), '#define INC_CAP 8\n')
    const localHdr = join(projDir, 'local.h')
    writeFileSync(localHdr, '// v1\n#define LOCAL_LIM INC_CAP\n')
    const goodUser = join(projDir, 'good_user.c')
    writeFileSync(goodUser, H + '#include "inc_cap.h"\n#include "local.h"\nstruct ring { int32_t a[LOCAL_LIM]; int32_t n; };\nint32_t get(struct ring *r) { if (r->n >= 0 && r->n < LOCAL_LIM) return r->a[r->n]; return 0; }\n')
    const rU1 = await check([goodUser], {root: projDir, flags: [`-I${incDir}`], propose: false})
    expect(rU1.exit).toBe(0)
    const mcU1 = (rU1.rules[0]?.safety as {macroConfig?: {userFilesSha256?: string, userFiles?: {path: string, sha256: string}[], systemHeadersSha256?: string, systemHeaders?: {path: string, sha256: string}[]}})?.macroConfig
    expect(mcU1?.userFilesSha256).toMatch(/^[0-9a-f]{64}$/)
    expect(mcU1?.userFiles?.length).toBe(3)
    for (const uf of mcU1!.userFiles!) {
      const diskSha = createHash('sha256').update(readFileSync(uf.path)).digest('hex')
      expect(uf.sha256).toBe(diskSha)
    }
    writeFileSync(join(projDir, 'gdp.toml'), `flags = ["-I${incDir}"]\n`)
    const rU1Text = runCliText(['check', '--no-propose', goodUser])
    expect(rU1Text.code).toBe(0)
    expect(rU1Text.out).toContain(`; user files: 3 (sha256:${mcU1!.userFilesSha256}); system headers: ${mcU1!.systemHeaders!.length} (sha256:${mcU1!.systemHeadersSha256});`)

    writeFileSync(localHdr, '// v2 changed\n#define LOCAL_LIM INC_CAP\n')
    const rU2 = await check([goodUser], {root: projDir, flags: [`-I${incDir}`], propose: false})
    expect(rU2.exit).toBe(0)
    const mcU2 = (rU2.rules[0]?.safety as {macroConfig?: {userFilesSha256?: string, userFiles?: {path: string, sha256: string}[]}})?.macroConfig
    expect(mcU2?.userFilesSha256).not.toBe(mcU1?.userFilesSha256)
    expect(mcU2?.userFiles?.find(f => f.path.endsWith('/local.h'))?.sha256).not.toBe(mcU1?.userFiles?.find(f => f.path.endsWith('/local.h'))?.sha256)
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 17: atomic user-file snapshot & concurrent-writer refusal (c1), pre-clang FIFO check (d1), component-wise symlink walk (h1/f3/f6/g1/d8), -I= refusal (f2), trailing-space include (e1), and case-insensitive /proc|/dev|/sys check', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe17-'))
  try {
    const H = '// gdp: safety\n#include <stdint.h>\n'
    const cliPath = new URL('./cli.ts', import.meta.url).pathname

    // (1) Case-insensitive /proc, /dev, /sys check (for case-insensitive filesystems such as macOS).
    for (const bad of ['/proc', '/proc/self/cwd', '/PROC/self/cwd', '/Proc/1', '/dev', '/dev/stdin', '/DEV/stdin', '/Dev/null', '/sys', '/SYS/kernel', '/Sys']) {
      expect(isSpecialVirtualPath(bad), `${bad} must be refused`).toBe(true)
    }
    for (const ok of ['/tmp/proc/a.h', '/var/dev/a.h', '/dev_tools/a.h', '/procedure/a.h', '/system/a.h']) {
      expect(isSpecialVirtualPath(ok), `${ok} must be allowed`).toBe(false)
    }

    // (2) c1 snapshot & concurrent-writer refusal:
    // (a) Direct verification: clangDump snapshots n.h once, reports the snapshot SHA-256, and
    //     verifySnapshotUnchanged() refuses if n.h is rewritten on disk afterward.
    const c1Dir = join(dir, 'c1')
    mkdirSync(c1Dir, {recursive: true})
    const c1Hdr = join(c1Dir, 'n.h')
    const c1Src = join(c1Dir, 'ring.c')
    writeFileSync(c1Hdr, '#define LIM 7\n')
    writeFileSync(c1Src, H + '#include "n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
    const lim7Sha = createHash('sha256').update('#define LIM 7\n').digest('hex')
    const lim8Sha = createHash('sha256').update('#define LIM 8\n').digest('hex')
    const dumped = clangDump(c1Src, [], 'clang', false, undefined, true, c1Dir)
    expect(dumped.target.safetyMeta?.macroConfig.userFiles?.find(u => u.path.endsWith('/n.h'))?.sha256).toBe(lim7Sha)
    expect(() => dumped.target.safetyMeta?.verifySnapshotUnchanged?.()).not.toThrow()
    writeFileSync(c1Hdr, '#define LIM 8\n')
    expect(() => dumped.target.safetyMeta?.verifySnapshotUnchanged?.()).toThrow(Refusal)

    // (b) Live concurrent-writer race on Linux via inotify IN_CLOSE_NOWRITE (probe13/watch.py):
    //     swapping n.h from LIM 7 -> LIM 8 at ANY close (1: after discovery -E -H, 2: after
    //     snapshot read, 3: after clangDump re-hash, 4: after analysis) must NEVER report
    //     proven exit 0 with the LIM 8 digest (close 1 -> broken exit 1, closes 2 & 3 ->
    //     unchecked exit 2 naming concurrent modification, close 4 -> proven with LIM 7 digest).
    if (process.platform === 'linux') {
      const pyCheck = spawnSync('python3', ['-c', 'import ctypes'], {stdio: 'ignore'})
      if (pyCheck.status === 0) {
        const watchPy = join(dir, 'watch.py')
        writeFileSync(watchPy, `import ctypes, os, struct, sys
f, n, new, log = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
libc = ctypes.CDLL(None, use_errno=True)
fd = libc.inotify_init()
libc.inotify_add_watch(fd, f.encode(), 0x10)
open(log, 'w').write('ready\\n')
cnt = 0
while True:
  buf = os.read(fd, 4096)
  i = 0
  while i < len(buf):
    _wd, mask, _cookie, ln = struct.unpack_from('iIII', buf, i)
    i += 16 + ln
    if mask & 0x10:
      cnt += 1
      if cnt == n:
        with open(f, 'r+') as h:
          h.seek(0); h.write(new); h.truncate()
        open(log, 'a').write(f'swapped:{cnt}\\n')
        sys.exit(0)
`)
        for (const closeN of [1, 2, 3, 4]) {
          const rDir = join(dir, `race_${closeN}`)
          mkdirSync(rDir, {recursive: true})
          const rHdr = join(rDir, 'n.h')
          const rSrc = join(rDir, 'ring.c')
          const rLog = join(rDir, 'w.log')
          writeFileSync(rHdr, '#define LIM 7\n')
          writeFileSync(rSrc, H + '#include "n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
          const watcher = spawn('python3', [watchPy, rHdr, String(closeN), '#define LIM 8\n', rLog], {stdio: 'ignore'})
          try {
            const deadline = Date.now() + 2000
            while (Date.now() < deadline) {
              try { if (readFileSync(rLog, 'utf8').includes('ready')) break } catch { /* wait */ }
              await new Promise(r => setTimeout(r, 10))
            }
            const p = spawnSync(process.execPath, [cliPath, 'check', '--no-propose', '--json', rSrc], {cwd: rDir, encoding: 'utf8'})
            const j = JSON.parse(p.stdout) as {rules: {safety?: {status: string, macroConfig?: {userFiles?: {path: string, sha256: string}[]}}, refusals: {what: string}[]}[]}
            if (closeN === 1) {
              expect(p.status, 'live race at close 1 must never exit 0').not.toBe(0)
              expect(j.rules[0]?.safety?.status).not.toBe('proven')
            } else if (closeN === 2 || closeN === 3) {
              expect(p.status, `live race at close ${closeN} must exit 2`).toBe(2)
              expect(j.rules[0]?.safety?.status).toBe('unchecked')
              expect(j.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('changed on disk during analysis')
            } else {
              expect(p.status, 'post-analysis close 4 proves snapshot LIM 7').toBe(0)
              expect(j.rules[0]?.safety?.status).toBe('proven')
              const nHash = j.rules[0]?.safety?.macroConfig?.userFiles?.find(u => u.path.endsWith('/n.h'))?.sha256
              expect(nHash).toBe(lim7Sha)
              expect(nHash).not.toBe(lim8Sha)
            }
          } finally {
            watcher.kill('SIGKILL')
          }
        }
      }
    }

    // (3) d1: FIFO include target is refused BEFORE the first clang pass (never hangs).
    const d1Dir = join(dir, 'd1')
    mkdirSync(d1Dir, {recursive: true})
    const mkfifo = spawnSync('mkfifo', [join(d1Dir, 'n.h')], {stdio: 'ignore'})
    if (mkfifo.status === 0) {
      const d1Src = join(d1Dir, 'ring.c')
      writeFileSync(d1Src, H + '#include "n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
      const t0 = Date.now()
      const rD1 = await check([d1Src], {propose: false})
      expect(Date.now() - t0, 'FIFO refusal must return promptly without hanging').toBeLessThan(10_000)
      expect(rD1.exit).toBe(2)
      expect(rD1.rules[0]?.safety).toMatchObject({status: 'unchecked'})
      expect(rD1.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('not a regular file')
    }

    // (4) h1: component-wise symlink walk catches `L/../n.h` where `L -> /proc/self/cwd/sub`
    //     without lexically collapsing `L/..` first.
    const h1Dir = join(dir, 'h1')
    const hcwd = join(dir, 'hcwd')
    mkdirSync(h1Dir, {recursive: true})
    mkdirSync(join(hcwd, 'sub'), {recursive: true})
    writeFileSync(join(hcwd, 'n.h'), '#define LIM 7\n')
    writeFileSync(join(h1Dir, 'n.h'), '/* decoy */\n')
    symlinkSync('/proc/self/cwd/sub', join(h1Dir, 'L'))
    const h1Src = join(h1Dir, 'ring.c')
    writeFileSync(h1Src, H + '#include "L/../n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
    const rH1 = spawnSync(process.execPath, [cliPath, 'check', '--no-propose', '--json', h1Src], {cwd: hcwd, encoding: 'utf8'})
    expect(rH1.status, 'h1 L/../n.h through /proc symlink must exit 2').toBe(2)
    const jH1 = JSON.parse(rH1.stdout) as {rules: {safety?: {status: string}, refusals: {what: string}[]}[]}
    expect(jH1.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(jH1.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('/proc')

    // (5) f2 (-I=...), f6 (-I<dir>/../../../proc/...), g1 (-I/ + "proc/self/cwd/n.h"), d8 (relative symlink to /proc).
    const f3h = join(dir, 'f3h')
    mkdirSync(f3h, {recursive: true})
    writeFileSync(join(f3h, 'n.h'), '#define LIM 7\n')
    const f2Src = join(dir, 'f2.c')
    writeFileSync(f2Src, H + '#include "n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
    const rF2 = await check([f2Src], {flags: [`-I=/proc/self/root${f3h}`], propose: false})
    expect(rF2.exit).toBe(2)
    const rF6 = await check([f2Src], {flags: [`-I${f3h}/../../../../../../../../proc/self/root${f3h}`], propose: false})
    expect(rF6.exit).toBe(2)
    const g1Src = join(dir, 'g1.c')
    writeFileSync(g1Src, H + '#include "proc/self/cwd/n.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
    const rG1 = await check([g1Src], {flags: ['-I/'], propose: false})
    expect(rG1.exit).toBe(2)

    // (6) e1: trailing-space include filename ("n.h ") is preserved (not trimmed to decoy "n.h"),
    //     proves cleanly, and reports the exact SHA-256 of "n.h ".
    const e1Dir = join(dir, 'e1')
    mkdirSync(e1Dir, {recursive: true})
    writeFileSync(join(e1Dir, 'n.h'), '/* decoy */\n')
    writeFileSync(join(e1Dir, 'n.h '), '#define LIM 7\n')
    const e1Src = join(e1Dir, 'ring.c')
    writeFileSync(e1Src, H + '#include "n.h "\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r) { return r->a[r->n]; }\nvoid put(struct ring *r) { if (r->n >= 0 && r->n < LIM) r->n = r->n + 1; }\n')
    const rE1 = await check([e1Src], {propose: false})
    expect(rE1.exit).toBe(0)
    const mcE1 = (rE1.rules[0]?.safety as {macroConfig?: {userFiles?: {path: string, sha256: string}[]}})?.macroConfig
    expect(mcE1?.userFiles?.some(u => u.path.endsWith('/n.h ') && u.sha256 === lim7Sha)).toBe(true)
    expect(mcE1?.userFiles?.some(u => u.path.endsWith('/n.h'))).toBe(false)
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

withClang('Review Probe 18: Clang-discovered full user+system -nostdinc snapshot & exact -E -H cross-check (probe14 s1/s2/s3/s4, n1/n2), stdlib -O2 alternate, and system header snapshot/assumptions', async () => {
  const dir = mkdtempSync(join(tmpdir(), 'gdp-c-safety-probe18-'))
  try {
    const body = '#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r, int32_t i) { if (i >= 0 && i < 8) return r->a[i]; return 0; }\n'
    const evilStddef = '#define if(c) if (1)\n'
    const evilSha = createHash('sha256').update(evilStddef).digest('hex')

    // (1) s1 (".//stddef.h"), s2 (fake-comment string macros around #include), s3 (form feed after #):
    //     Clang -E -H discovers the local stddef.h and snapshots it with -nostdinc (never falling
    //     back to system <stddef.h>) -> MUST NOT exit 0 / proven, and stddef.h is recorded in userFiles.
    for (const [label, prefix] of [
      ['s1', '// gdp: safety\n#include ".//stddef.h"\n'],
      ['s2', '// gdp: safety\n#define S "/*"\n#include "stddef.h"\n#define T "*/"\n'],
      ['s3', '// gdp: safety\n#\x0cinclude "stddef.h"\n'],
    ] as const) {
      const d = join(dir, label)
      mkdirSync(d, {recursive: true})
      writeFileSync(join(d, 'stddef.h'), evilStddef)
      const f = join(d, 'ring.c')
      writeFileSync(f, prefix + body)
      const res = await check([f], {propose: false})
      expect(res.exit, `${label} must never prove (exit 0)`).not.toBe(0)
      expect(res.rules[0]?.safety?.status, `${label} must not be proven`).not.toBe('proven')
      const mc = (res.rules[0]?.safety as {macroConfig?: {userFiles?: {path: string, sha256: string}[]}})?.macroConfig
      expect(mc?.userFiles?.some(u => u.path.endsWith('/stddef.h') && u.sha256 === evilSha), `${label} must include local stddef.h in snapshot`).toBe(true)
    }

    // (2) s4 (<inc//stddef.h> with -I<s4>): refused (exit 2), never proven.
    const s4Dir = join(dir, 's4')
    mkdirSync(join(s4Dir, 'inc'), {recursive: true})
    writeFileSync(join(s4Dir, 'inc', 'stddef.h'), evilStddef)
    const s4Src = join(s4Dir, 'ring.c')
    writeFileSync(s4Src, '// gdp: safety\n#include <inc//stddef.h>\n' + body)
    const rS4 = await check([s4Src], {flags: [`-I${s4Dir}`], propose: false})
    expect(rS4.exit).toBe(2)
    expect(rS4.rules[0]?.safety).toMatchObject({status: 'unchecked'})

    // (3) n1 (-I into a system directory, e.g. /usr/include/linux or /usr/include): refused (exit 2).
    const n1Dir = join(dir, 'n1')
    mkdirSync(n1Dir, {recursive: true})
    const n1Src = join(n1Dir, 'ring.c')
    writeFileSync(n1Src, '// gdp: safety\n#include <stdint.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r, int32_t i) { if (i >= 0 && i < 8) return r->a[i]; return 0; }\n')
    const sysIncTarget = process.platform === 'linux' ? '/usr/include/linux' : '/usr/include'
    const rN1 = await check([n1Src], {flags: [`-I${sysIncTarget}`], propose: false})
    expect(rN1.exit, 'n1 -I into system dir must exit 2').toBe(2)
    expect(rN1.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rN1.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('system header directory')

    // (4) n2 (user-visible symlink resolving into a system header directory): refused (exit 2).
    const probeDump = clangDump(n1Src, [], 'clang', false, undefined, true, n1Dir)
    const stdintSysPath = probeDump.target.safetyMeta?.macroConfig.systemHeaders?.find(h => h.path.endsWith('/stdint.h'))?.path
    expect(stdintSysPath).toBeTruthy()
    const n2Dir = join(dir, 'n2')
    mkdirSync(n2Dir, {recursive: true})
    symlinkSync(stdintSysPath!, join(n2Dir, 'my_sys.h'))
    const n2Src = join(n2Dir, 'ring.c')
    writeFileSync(n2Src, '// gdp: safety\n#include "my_sys.h"\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r, int32_t i) { if (i >= 0 && i < 8) return r->a[i]; return 0; }\n')
    const rN2 = await check([n2Src], {propose: false})
    expect(rN2.exit, 'n2 user symlink into system dir must exit 2').toBe(2)
    expect(rN2.rules[0]?.safety).toMatchObject({status: 'unchecked'})
    expect(rN2.rules[0]?.refusals.map(r => r.what).join('; ')).toContain('system header directory')

    // (5) Positive controls: <stdlib.h> proves cleanly across -nostdinc & -O2 build-mode alternate,
    //     system header snapshot hashes match disk, and assumptions name /usr/local/include & Homebrew.
    const stdlibSrc = join(dir, 'stdlib_ok.c')
    writeFileSync(stdlibSrc, '// gdp: safety\n#include <stdint.h>\n#include <stdlib.h>\nstruct ring { int32_t n; int32_t a[8]; };\nint32_t get(struct ring *r, int32_t i) { if (i >= 0 && i < 8) return r->a[i]; return 0; }\n')
    const rStdlib = await check([stdlibSrc], {propose: false})
    expect(rStdlib.exit, 'clean file including <stdlib.h> must prove (exit 0)').toBe(0)
    expect(rStdlib.rules[0]?.safety).toMatchObject({status: 'proven', coveredFunctions: ['get']})
    const assumpText = (rStdlib.rules[0]?.safety as {assumptions?: readonly string[]})?.assumptions?.join(' ') ?? ''
    expect(assumpText).toContain('/usr/local/include')
    expect(assumpText).toContain('/opt/homebrew/include')
    const mcStd = (rStdlib.rules[0]?.safety as {macroConfig?: {systemHeaders?: {path: string, sha256: string}[]}})?.macroConfig
    expect(mcStd?.systemHeaders?.length).toBeGreaterThan(0)
    for (const sh of mcStd!.systemHeaders!.slice(0, 5)) {
      const diskSha = createHash('sha256').update(readFileSync(sh.path)).digest('hex')
      expect(sh.sha256).toBe(diskSha)
    }
  } finally {
    rmSync(dir, {recursive: true, force: true})
  }
}, 180_000)

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
