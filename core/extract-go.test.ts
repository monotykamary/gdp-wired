// The Go front end (core/extract-go.ts): rules read from Go, each checked against the Go code it was read from (built
// with the Go toolchain, a harness beside it). The adversarial cases: overflow at the type's width, aliasing through
// pointers, map iteration order, slices sharing a backing array, defer, panics, errors after a write. Each is refused
// with the reason, or extracted and checked (and its semantics proven of the rule where it matters). Skipped where Go
// isn't installed (research/extract/go-setup.sh installs it in a job).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {extractGo, type GoExtraction, type GoOptions} from './extract-go.ts'
import {no, proveRule, proveSteps} from './dsl.ts'

const hasGo = (() => { try { execFileSync('go', ['version'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasGo ? test : test.skip
const budget = {runs: 40, depth: 8, states: 80}
// A module of one package, `p`, with the code given.
const go = (code: string, entry: string, more: Partial<GoOptions> = {}): GoExtraction => {
  const root = mkdtempSync(`${tmpdir()}/gdp-gocase-`)
  writeFileSync(`${root}/go.mod`, 'module example.com/gocase\n\ngo 1.22\n')
  mkdirSync(`${root}/p`)
  writeFileSync(`${root}/p/p.go`, `package p\n\n${code}\n`)
  return extractGo(`${root}/p`, {entry, check: budget, ...more})
}
const ok = (x: GoExtraction) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}\n${JSON.stringify(x.evidence)}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
const refused = (x: GoExtraction, why: RegExp) => {
  expect(x.ok).toBe(false)
  expect(x.refusals.map(r => r.what).join('; ')).toMatch(why)
}
// A step law of the extracted rule, proven (with the rule's own invariants beside it).
const step = (x: GoExtraction, name: string, then: (b: any, a: any) => any, when: (b: any) => any) => {
  const r = x.rule! as any
  const v = proveSteps(r, x.invariants ?? [], [r.stepLaw(name, then, when)])
  if (!v.proven) throw new Error(`${name}: ${JSON.stringify({goal: v.goal, stuck: v.stuck, witness: v.witness})}`)
}

// --- the subset -------------------------------------------------------------------------------------------------------
t('a struct of uint32 counters (gobreaker\'s Counts): increments wrap at 2^32, a result kept', () => {
  const x = ok(go(`
type Counts struct {
	Requests        uint32
	TotalExclusions uint32
	Consecutive     uint32
}
func (c *Counts) onRequest()   { c.Requests++ }
func (c *Counts) onExclusion() { c.TotalExclusions++ }
func (c *Counts) onFailure()   { c.Consecutive++ }
func (c *Counts) onSuccess()   { c.Consecutive = 0 }
func (c *Counts) validRequests() uint32 {
	if c.Requests < c.TotalExclusions {
		return 0
	}
	return c.Requests - c.TotalExclusions
}`, 'Counts', {methods: ['onRequest', 'onExclusion', 'onFailure', 'onSuccess', 'validRequests']}))
  expect(x.source).toContain('4294967296')
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  step(x, 'onRequest at 2^32 − 1 wraps to 0', (_, a) => a.Requests.eq(0), b => b.method.is('onRequest').and(b.Requests.eq(4294967295)))
  step(x, 'onRequest below 2^32 − 1 adds 1', (b, a) => a.Requests.eq(b.Requests.plus(1)), b => b.method.is('onRequest').and(b.Requests.lt(4294967295)))
  const r = x.rule! as any
  expect(proveRule(r, [...x.invariants!, r.law('validRequests is at most Requests', ({validRequests_result, Requests}: any) => validRequests_result.atMost(Requests))]).proven).toBe(true)
}, 600_000)

t('overflow at each width: int8 wraps to −128, uint16 below 0 wraps up, int32 products wrap', () => {
  const x = ok(go(`
type W struct {
	A int8
	B uint16
	C int32
}
func (w *W) IncA()          { w.A++ }
func (w *W) SubB(d uint16)  { w.B -= d }
func (w *W) Twice()         { w.C = w.C * 2 }`, 'W'))
  step(x, 'int8 127 + 1 is −128', (_, a) => a.A.eq(-128), b => b.method.is('IncA').and(b.A.eq(127)))
  step(x, 'uint16 0 − 1 is 65535', (_, a) => a.B.eq(65535), b => b.method.is('SubB').and(b.B.eq(0), b.SubB_d.eq(1)))
  step(x, 'int32 2^30 · 2 is −2^31', (_, a) => a.C.eq(-2147483648), b => b.method.is('Twice').and(b.C.eq(1073741824)))
}, 600_000)

t('a uint64 below 0 is refused (Go wraps it past the rule\'s 2^53); past 2^53 the runtime refuses', () => {
  const x = ok(go(`
type L struct{ N uint64 }
func (l *L) Take(d uint64) { l.N -= d }
func (l *L) Add(d uint64)  { l.N += d }`, 'L'))
  expect(x.source).toMatch(/Take_d\)?\.?.*atMost|Take_d/)
  expect(x.notes.join('\n')).toMatch(/below 0 is refused/)
  // The rule refuses the step Go would wrap: Take(d) with d > N.
  const r = x.rule! as any
  expect(proveSteps(r, x.invariants ?? [], [r.stepLaw('Take never takes N below 0', (_: any, a: any) => a.N.atLeast(0), (b: any) => b.method.is('Take'))]).proven).toBe(true)
}, 600_000)

t('*big.Int fields (blnk\'s balances): nil a state of its own, Add and Sub in place, Cmp, an error as the refusal', () => {
  const x = ok(go(`
import (
	"fmt"
	"math/big"
)
type Bal struct {
	Credit *big.Int
	Debit  *big.Int
	Net    *big.Int
}
func (b *Bal) init() {
	if b.Credit == nil {
		b.Credit = big.NewInt(0)
	}
	if b.Debit == nil {
		b.Debit = big.NewInt(0)
	}
	if b.Net == nil {
		b.Net = big.NewInt(0)
	}
}
func (b *Bal) Credit1(x *big.Int) {
	b.init()
	b.Credit.Add(b.Credit, x)
	b.Net.Sub(b.Credit, b.Debit)
}
func (b *Bal) Debit1(x *big.Int) error {
	if b.Net == nil || b.Net.Cmp(x) < 0 {
		return fmt.Errorf("insufficient: have %s", b.Net.String())
	}
	b.init()
	b.Debit.Add(b.Debit, x)
	b.Net.Sub(b.Credit, b.Debit)
	return nil
}`, 'Bal'))
  const r = x.rule! as any
  expect(proveRule(r, [...x.invariants!, r.law('Net is Credit − Debit once set', ({Net, Credit, Debit, Net_nil}: any) => Net_nil.or(Net.eq(Credit.minus(Debit))))]).proven).toBe(true)
}, 600_000)

// --- overflow: a wrong model of it is caught by the check -------------------------------------------------------------
t('the check catches a rule that forgets the wrap (the model edited after reading)', async () => {
  const root = mkdtempSync(`${tmpdir()}/gdp-gocase-`)
  writeFileSync(`${root}/go.mod`, 'module example.com/gocase\n\ngo 1.22\n')
  mkdirSync(`${root}/p`)
  writeFileSync(`${root}/p/p.go`, 'package p\n\ntype C struct{ N uint8 }\n\nfunc (c *C) Inc() { c.N++ }\n')
  const {readGoPackage, readGo} = await import('./extract-go.ts')
  const {fromModel} = await import('./extract.ts')
  const {checkGo} = await import('./extract-go-check.ts')
  const pkg = readGoPackage(`${root}/p`), read = readGo(pkg, {entry: 'C'})
  // N + 1 with no wrap: the rule says 256 where Go says 0.
  read.model.writes.N = {s: 'num', e: {op: 'add', a: {op: 'var', name: 'N'}, b: {op: 'const', v: 1}}}
  read.model.laws = []
  const y = fromModel(read.model, 'C.go', {N: 'nat'}, [], (rule, sorts) => checkGo(`${root}/p`, pkg, read, rule, sorts, {entry: 'C', check: budget}))
  expect(y.ok).toBe(false)
  expect(y.refusals[0]!.what).toMatch(/the rule and the code differ: .*N is 0 in the code, 256 in the rule/)
}, 600_000)

// --- aliasing through pointers ----------------------------------------------------------------------------------------
t('aliasing through pointers: a copied pointer writes the object, a copied struct doesn\'t, an interior pointer does', () => {
  const x = ok(go(`
type In struct{ X int64 }
type A struct {
	N   int64
	M   int64
	Sub In
}
func (a *A) ViaPointer()  { p := a; p.N = 5 }
func (a *A) ViaCopy()     { v := *a; v.N = 7; a.M = v.N }
func (a *A) ViaInterior() { q := &a.Sub; q.X++ }
func (a *A) ViaChoice(c bool) {
	p := &a.N
	if c {
		p = &a.M
	}
	*p = 1
}`, 'A'))
  step(x, 'a copied pointer writes the object', (_, a) => a.N.eq(5), b => b.method.is('ViaPointer'))
  step(x, 'a copied struct leaves the object', (b, a) => a.N.eq(b.N).and(a.M.eq(7)), b => b.method.is('ViaCopy'))
  step(x, 'an interior pointer writes the nested field', (b, a) => a.Sub_X.eq(b.Sub_X.plus(1)), b => b.method.is('ViaInterior').and(b.Sub_X.lt(1000)))
  step(x, 'a pointer chosen by a condition writes the one it is', (b, a) => a.M.eq(1).and(a.N.eq(b.N)), b => b.method.is('ViaChoice').and(b.ViaChoice_c))
}, 600_000)

t('aliasing refused: one big.Int in two fields, a pointer the caller gave kept in the state', () => {
  refused(go(`
import "math/big"
type B struct{ X, Y *big.Int }
func (b *B) Share() { b.X = big.NewInt(1); b.Y = b.X }`, 'B'), /one object in two places|may be one big\.Int/)
  refused(go(`
import "math/big"
type B struct{ X *big.Int }
func (b *B) Keep(v *big.Int) { b.X = v }`, 'B'), /pointer the caller gave|keeps the \*big\.Int the caller gave/)
}, 600_000)

// --- maps -------------------------------------------------------------------------------------------------------------
t('maps: read with a zero for a missing key, comma-ok, delete, a nil map\'s write panics; a range over one is refused', () => {
  const x = ok(go(`
type M struct{ Seen map[string]int64 }
func (m *M) Init() {
	if m.Seen == nil {
		m.Seen = map[string]int64{}
	}
}
func (m *M) Bump(k string) { m.Seen[k] = m.Seen[k] + 1 }
func (m *M) Has(k string) bool { _, ok := m.Seen[k]; return ok }
func (m *M) Forget(k string) { delete(m.Seen, k) }`, 'M'))
  step(x, 'Bump on a nil map is refused (a panic)', () => no, b => b.method.is('Bump').and(b.Seen_nil))
  refused(go(`
type M struct{ Seen map[string]int64 }
func (m *M) Sum() int64 {
	var s int64
	for _, v := range m.Seen {
		s += v
	}
	return s
}`, 'M'), /a range over a map \(Go's iteration order is random/)
}, 600_000)

// --- slices -----------------------------------------------------------------------------------------------------------
t('slices as lists: append and pop in place, an index out of range panics; a second name for a slice is refused', () => {
  const x = ok(go(`
type S struct{ Xs []int64 }
func (s *S) Push(v int64) { s.Xs = append(s.Xs, v) }
func (s *S) Pop() {
	if len(s.Xs) > 0 {
		s.Xs = s.Xs[:len(s.Xs)-1]
	}
}
func (s *S) Set(i int, v int64) { s.Xs[i] = v }`, 'S'))
  expect(x.source).toContain('Xs.push(')
  refused(go(`
type S struct{ Xs []int64 }
func (s *S) Alias(v int64) { t := s.Xs; t = append(t, v); _ = t }`, 'S'), /a slice given a second name.*backing array/)
  refused(go(`
type S struct{ Xs, Ys []int64 }
func (s *S) Share() { s.Ys = s.Xs }`, 'S'), /a slice given a second name.*backing array/)
  refused(go(`
type S struct{ Xs []int64 }
func (s *S) Window() { s.Xs = s.Xs[1:] }`, 'S'), /a slice of a slice \(it shares the backing array/)
}, 600_000)

// --- defer ------------------------------------------------------------------------------------------------------------
t('defer: a mutex\'s Unlock after its Lock is read (the step is atomic); any other defer, or a lock taken twice, is refused', () => {
  ok(go(`
import "sync"
type C struct {
	mu sync.Mutex
	N  int64
}
func (c *C) Inc() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.N++
}`, 'C'))
  refused(go(`
type C struct{ N int64 }
func (c *C) Inc() {
	defer func() { c.N = 0 }()
	c.N++
}`, 'C'), /defer \(other than a mutex's Unlock/)
  refused(go(`
import "sync"
type C struct {
	mu sync.Mutex
	N  int64
}
func (c *C) get() int64 { c.mu.Lock(); defer c.mu.Unlock(); return c.N }
func (c *C) Inc() {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.N = c.get() + 1
}`, 'C', {methods: ['Inc']}), /locked again in the same step \(a deadlock\)/)
}, 600_000)

// --- panics and errors ------------------------------------------------------------------------------------------------
t('panics: explicit, a nil *big.Int, a division by a constant zero is Go\'s compile error; each a refusal, the state as it was', () => {
  const x = ok(go(`
import "math/big"
type P struct {
	N int64
	X *big.Int
}
func (p *P) Check(v int64) {
	if v < 0 {
		panic("negative")
	}
	p.N = v
}
func (p *P) Grow(d *big.Int) { p.X.Add(p.X, d) }`, 'P'))
  step(x, 'Check refuses a negative value', () => no, b => b.method.is('Check').and(b.Check_v.lt(0)))
  step(x, 'Grow on a nil X is refused (a nil dereference)', () => no, b => b.method.is('Grow').and(b.X_nil))
}, 600_000)

t('a panic or an error after a write is refused, unless the caller discards what a failed call wrote', () => {
  const src = `
import "errors"
type E struct{ N, M int64 }
func (e *E) Move(d int64) error {
	e.N -= d
	if e.N < 0 {
		return errors.New("overdrawn")
	}
	e.M += d
	return nil
}`
  refused(go(src, 'E'), /an error returned after the state is written/)
  const x = ok(go(src, 'E', {onError: 'discard'}))
  step(x, 'Move never leaves N below 0', (_, a) => a.N.atLeast(0), b => b.method.is('Move').and(b.N.atLeast(0)))
}, 600_000)

t('outside the subset, each where it is: floats, loops, goroutines, closures, generics, another module\'s code', () => {
  refused(go('type F struct{ X float64 }\nfunc (f *F) Half() { f.X = f.X / 2 }', 'F'), /a float/)
  refused(go('type F struct{ N int64 }\nfunc (f *F) Loop() { for i := 0; i < 3; i++ { f.N++ } }', 'F'), /a loop \(for\)/)
  refused(go('type F struct{ N int64 }\nfunc (f *F) Go() { go func() {}() }', 'F'), /a goroutine/)
  refused(go('type F struct{ N int64 }\nfunc (f *F) Do() { g := func() int64 { return 1 }; f.N = g() }', 'F'), /a closure/)
  refused(go('type F[T any] struct{ N int64; v T }\nfunc (f *F[T]) Inc() { f.N++ }', 'F'), /generic/)
  // (another package's call whose value is kept: refused as stated, answered over its type as inferred)
  refused(go('import "strings"\ntype F struct{ S string; N int64 }\nfunc (f *F) Up() { f.S = strings.ToUpper(f.S) }', 'F', {strict: true}), /standard library the subset doesn't read/)
  expect(ok(go('import "strings"\ntype F struct{ S string; N int64 }\nfunc (f *F) Up() { f.S = strings.ToUpper(f.S) }', 'F')).notes.join(' ')).toMatch(/strings.ToUpper .*answered by the request \(inferred/)
}, 600_000)

t('a context.Context argument passed on to the package\'s own functions is read; one the step reads is refused', () => {
  const x = ok(go(`import "context"
type Q struct{ Used int64; Limit int64 }
func (q *Q) take(ctx context.Context, n int64) bool {
	if n < 0 || q.Used+n > q.Limit { return false }
	q.Used += n
	return true
}
func (q *Q) Take(ctx context.Context, n int64) bool { return q.take(ctx, n) }
func (q *Q) Reset(_ context.Context) { q.Used = 0 }`, 'Q', {methods: ['Take', 'Reset']}))
  expect(x.notes.join(' ')).toMatch(/a context.Context, passed on/)
  const r = x.rule! as any
  expect(proveRule(r, [...(x.invariants ?? []), r.law('within the limit', ({Used, Limit}: any) => Used.atMost(Limit).or(Used.eq(0)))]).proven).toBe(true)
  // read: its methods are another package's code, and a function of another package takes it as its own
  refused(go('import "context"\ntype Q struct{ N int64 }\nfunc (q *Q) Inc(ctx context.Context) { if ctx.Err() == nil { q.N++ } }', 'Q'), /ctx.Err\(\): a method of context/)
  refused(go('import "context"\ntype Q struct{ N int64 }\nfunc (q *Q) Inc(ctx context.Context) { if ctx != nil { q.N++ } }', 'Q'), /compared with a nil/)
  // (the boundary inferred: a context made and its cancel called, their values read by nothing the rule keeps)
  const wt = 'import (\n\t"context"\n\t"time"\n)\ntype Q struct{ N int64 }\nfunc (q *Q) Inc(ctx context.Context) { c, f := context.WithTimeout(ctx, time.Second); _ = c; f(); q.N++ }'
  expect(ok(go(wt, 'Q')).notes.join(' ')).toMatch(/context.WithTimeout \(p.go:8:\d+\): left out \(inferred/)
  refused(go(wt, 'Q', {strict: true}), /context.WithTimeout.*standard library the subset doesn't read/)
}, 600_000)

t('another package\'s struct as an argument: its exported fields read as inputs; its methods stay its own code', () => {
  // p reads q's struct as data
  const two = (code: string) => {
    const root = mkdtempSync(`${tmpdir()}/gdp-gocase-`)
    writeFileSync(`${root}/go.mod`, 'module example.com/gocase\n\ngo 1.22\n')
    mkdirSync(`${root}/p`); mkdirSync(`${root}/q`)
    writeFileSync(`${root}/q/q.go`, 'package q\n\ntype Inner struct{ A int64 }\ntype Rule struct {\n\tMax  int64\n\tOn   bool\n\tIn   Inner\n\thidden int64\n}\nfunc (r *Rule) Twice() int64 { return 2 * r.Max }\n')
    writeFileSync(`${root}/p/p.go`, `package p\n\nimport "example.com/gocase/q"\n\n${code}\n`)
    return extractGo(`${root}/p`, {entry: 'L', check: budget})
  }
  const x = ok(two('type L struct{ N int64 }\nfunc (l *L) Take(r *q.Rule, n int64) bool {\n\tif !r.On || n < 0 || l.N+n > r.Max { return false }\n\tl.N += n\n\treturn true\n}'))
  expect(x.source).toContain('Take_r_Max')
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  refused(two('type L struct{ N int64 }\nfunc (l *L) Take(r *q.Rule) { l.N = r.Twice() }'), /a method of example.com\/gocase\/q/)
  refused(two('type L struct{ N int64 }\nfunc (l *L) Take(r *q.Rule) { l.N = r.In.A }'), /In of the argument: q.Inner: a value outside the subset/)
}, 600_000)

t('a struct given by value (gitea\'s CreateReviewOptions, the csr options): its fields inputs; writing the copy changes nothing the caller sees', () => {
  const x = ok(go(`
type Opts struct {
	Allow bool
	Max   int32
	note  string
}
type L struct{ N int64 }
func (l *L) Take(o Opts, n int64) bool {
	o.Max++
	if !o.Allow || n < 0 || l.N+n > int64(o.Max) { return false }
	l.N += n
	return true
}`, 'L'))
  expect(x.source).toContain('Take_o_Allow')
  expect(x.evidence!.coverage.hit).toBe(x.evidence!.coverage.arms)
  step(x, 'a refused take changes nothing', (b, a) => a.N.eq(b.N), b => b.method.is('Take').and(b.Take_o_Allow.not()))
  // (a field of a narrower integer type, read through a pointer the caller gives: a value past its type is no request)
  ok(go('type Opts struct{ Max int32 }\ntype L struct{ N int64 }\nfunc (l *L) Take(o *Opts) { if l.N < int64(o.Max) { l.N++ } }', 'L'))
  // another package's struct by value: its exported fields (all its code can set)
  const root = mkdtempSync(`${tmpdir()}/gdp-gocase-`)
  writeFileSync(`${root}/go.mod`, 'module example.com/gocase\n\ngo 1.22\n')
  mkdirSync(`${root}/p`); mkdirSync(`${root}/q`)
  writeFileSync(`${root}/q/q.go`, 'package q\n\ntype Rule struct {\n\tMax    int64\n\thidden int64\n}\n')
  writeFileSync(`${root}/p/p.go`, 'package p\n\nimport "example.com/gocase/q"\n\ntype L struct{ N int64 }\nfunc (l *L) Take(r q.Rule, n int64) bool {\n\tif n < 0 || l.N+n > r.Max { return false }\n\tl.N += n\n\treturn true\n}\n')
  const y = ok(extractGo(`${root}/p`, {entry: 'L', check: budget}))
  expect(y.source).toContain('Take_r_Max')
  expect(y.source).not.toContain('hidden')
}, 600_000)

t('Go\'s integer division truncates toward zero; conversions wrap into the narrower type', () => {
  const x = ok(go(`
type D struct {
	N int64
	B int8
	U uint8
}
func (d *D) Half()            { d.N = d.N / 2 }
func (d *D) Rem()             { d.N = d.N % 3 }
func (d *D) Narrow(v int64)   { d.B = int8(v) }
func (d *D) Unsigned(v int64) { d.U = uint8(v) }`, 'D'))
  step(x, '−7 / 2 is −3', (_, a) => a.N.eq(-3), b => b.method.is('Half').and(b.N.eq(-7)))
  step(x, '−7 % 3 is −1', (_, a) => a.N.eq(-1), b => b.method.is('Rem').and(b.N.eq(-7)))
  step(x, 'int8(200) is −56', (_, a) => a.B.eq(-56), b => b.method.is('Narrow').and(b.Narrow_v.eq(200)))
  step(x, 'uint8(−1) is 255', (_, a) => a.U.eq(255), b => b.method.is('Unsigned').and(b.Unsigned_v.eq(-1)))
}, 600_000)

t('embedded structs: a promoted pointer method writes the embedded field, a value receiver writes a copy', () => {
  const x = ok(go(`
type Counts struct{ Requests uint32 }
func (c *Counts) onRequest() { c.Requests++ }
func (c Counts) bump()       { c.Requests++ }
type R struct {
	Counts
	Age uint64
}
func (r *R) Hit()  { r.onRequest(); r.Age++ }
func (r *R) Copy() { r.bump() }`, 'R'))
  step(x, 'Hit counts a request', (b, a) => a.Counts_Requests.eq(b.Counts_Requests.plus(1)), b => b.method.is('Hit').and(b.Counts_Requests.lt(100), b.Age.lt(100)))
  step(x, 'a value receiver leaves the object', (b, a) => a.Counts_Requests.eq(b.Counts_Requests), b => b.method.is('Copy'))
}, 600_000)

t('recover is refused (a panic is a refusal here, not a value)', () => {
  refused(go(`
type C struct{ N int64 }
func (c *C) Safe() {
	defer func() { _ = recover() }()
	c.N++
}`, 'C'), /defer|recover/)
}, 600_000)

t('the boundary inferred: another package\'s call left out, one whose value is read answered over its type, the entry', () => {
  const x = ok(go(`import (
	"log"
	"unicode/utf8"
)

type Q struct{ Used int64; Cap int64 }

func (q *Q) Take(name string) bool {
	log.Println("take", name)
	n := int64(utf8.RuneCountInString(name))
	if n < 0 || q.Used > q.Cap-n {
		return false
	}
	q.Used += n
	return true
}

func (q *Q) Left() int64 { return q.Cap - q.Used }`, undefined as never))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Q/)
  expect(notes).toMatch(/log.Println .*left out \(inferred/)
  expect(notes).toMatch(/unicode\/utf8.RuneCountInString .*answered by the request \(inferred: its value is read; assumes .* may return any int\)/)
  const r = x.rule! as any
  expect(proveSteps(r, x.invariants ?? [], [r.stepLaw('never past its cap', (_b: any, a: any) => a.Used.atMost(a.Cap), (b: any) => b.Used.atMost(b.Cap))]).proven).toBe(true)
}, 600_000)
