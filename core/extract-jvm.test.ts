// The JVM front ends (core/extract-jvm.ts): rules read from Java through javac's tree API and from Kotlin through the
// compiler's PSI, each checked against the code it was read from, compiled and run through core/jvm/Harness.java.
// The adversarial cases: int's wraparound past MAX_VALUE (and Math.addExact's trap), a switch's fallthrough, a
// compare-and-set loop, Optional, a map of records, a lock's try/finally, the clock and an answered call rewritten for
// the check; Kotlin's nullability, when, a data class's copy, an immutable class's step, a map's [] and ?:.
// Skipped where no JDK (Java) or no kotlinc (Kotlin) is installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveRule, proveSteps} from './dsl.ts'
import {type JvmOptions, extractJava, extractKotlin} from './extract-jvm.ts'

const javac = process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac'
const hasJdk = (() => { try { execFileSync(javac, ['-version'], {stdio: 'ignore'}); return true } catch { return false } })()
const hasKt = hasJdk && (() => { try { if (process.env.KOTLIN_HOME) return true; execFileSync('sh', ['-c', 'command -v kotlinc'], {stdio: 'ignore'}); return true } catch { return false } })()
const tj = hasJdk ? test : test.skip, tk = hasKt ? test : test.skip
const CHECK = {runs: 30, depth: 6, states: 60}
const java = (code: string, entry: string, more: Partial<JvmOptions> = {}, extra: Record<string, string> = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-javacase-`)
  mkdirSync(`${dir}/demo`, {recursive: true})
  writeFileSync(`${dir}/demo/${entry}.java`, `package demo;\n${code}`)
  for (const [f, src] of Object.entries(extra)) writeFileSync(`${dir}/demo/${f}`, `package demo;\n${src}`)
  return extractJava(`${dir}/demo/${entry}.java`, {entry, root: dir, check: CHECK, ...more})
}
const kotlin = (code: string, entry: string, more: Partial<JvmOptions> = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-ktcase-`), file = `${dir}/Case.kt`
  writeFileSync(file, `package demo\n${code}`)
  return extractKotlin(file, {entry, check: CHECK, ...more})
}
type X = ReturnType<typeof java>
const ok = (x: X) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type R = {stepLaw: (n: string, t: unknown, w: unknown) => never, law: (n: string, f: (s: any) => unknown) => never}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const step = (x: X, name: string, then: (b: any, a: any) => any, when: (b: any) => any) => {
  const r = x.rule! as never as R
  const v = proveSteps(r as never, x.invariants ?? [], [r.stepLaw(name, then, when)])
  if (!v.proven) throw new Error(`${name}: ${JSON.stringify({goal: v.goal, witness: v.witness})}`)
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const inv = (x: X, name: string, holds: (s: any) => any) => proveRule(x.rule! as never, [...(x.invariants ?? []), (x.rule! as never as R).law(name, holds)])

tj('int wraps past MAX_VALUE as Java\'s does; Math.addExact traps (an ArithmeticException, kept as the result)', () => {
  const x = ok(java(`
public class Meter {
  private int hits;
  private long total;
  public Meter(int start) { this.hits = start; }
  public int hit() { hits++; return hits; }
  public void add(int k) { total = Math.addExact(total, k); }
  public int exact(int k) { return Math.addExact(hits, k); }
}`, 'Meter', {failures: 'kept'}))
  expect(x.source).toContain('4294967296')
  step(x, 'a hit past MAX_VALUE wraps to MIN_VALUE', (_b, a) => a.hits.eq(-2147483648), b => b.method.is('hit').and(b.hits.eq(2147483647)))
  step(x, 'exact fails past MAX_VALUE, the count as it was', (b, a) => a.failed.and(a.hits.eq(b.hits)), b => b.method.is('exact').and(b.hits.eq(2147483647)).and(b.exact_k.eq(1)))
})

tj('a switch on an enum: a case falling through into the next, the default; a static constant folded', () => {
  const x = ok(java(`
public class Grade {
  enum Outcome { OK, SLOW, SLOW_ERROR, ERROR }
  static final int SCALE = 10;
  int slow, failed, calls;
  public void record(Outcome o) {
    calls += 1;
    switch (o) {
      case SLOW_ERROR:
        failed += SCALE;
      case SLOW:
        slow++;
        break;
      case ERROR:
        failed += SCALE;
        break;
      default:
        break;
    }
  }
}`, 'Grade'))
  expect(x.source).toContain("oneOf('OK', 'SLOW', 'SLOW_ERROR', 'ERROR')")
  step(x, 'a slow error counts as slow too (it falls through)', (b, a) => a.slow.eq(b.slow.plus(1)).and(a.failed.eq(b.failed.plus(10))), b => b.o.is('SLOW_ERROR').and(b.slow.lt(1000)).and(b.failed.lt(1000)).and(b.slow.atLeast(0)).and(b.failed.atLeast(0)))
})

tj('a compare-and-set loop read as its first pass; an AtomicInteger as the int it holds; Math.max and min', () => {
  const x = ok(java(`
import java.util.concurrent.atomic.AtomicInteger;
public class Tokens {
  final int max;
  final AtomicInteger count = new AtomicInteger();
  public Tokens(int max) { this.max = max; count.set(max); }
  public boolean take() {
    while (true) {
      int cur = count.get();
      if (cur == 0) return false;
      if (count.compareAndSet(cur, Math.max(cur - 1, 0))) return true;
    }
  }
  public void give() {
    for (;;) {
      int cur = count.get();
      if (cur >= max) break;
      if (count.compareAndSet(cur, Math.min(cur + 1, max))) break;
    }
  }
}`, 'Tokens'))
  expect(inv(x, 'the count stays within 0 and max', s => s.count.atLeast(0).and(s.count.atMost(s.max_)).or(s.max_.lt(0))).proven).toBe(true)
})

tj('a map of records, Optional, a ReentrantLock\'s try/finally: the step atomic, one key written a step', () => {
  const x = ok(java(`
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.locks.ReentrantLock;
public class Windows {
  record Window(long start, int count) {}
  private final Map<String, Window> windows = new ConcurrentHashMap<>();
  private final ReentrantLock lock = new ReentrantLock();
  private Optional<Long> last = Optional.empty();
  private final int limit;
  public Windows(int limit) { this.limit = limit; }
  public boolean hit(String key, long now) {
    lock.lock();
    try {
      last = Optional.of(now);
      Window w = windows.get(key);
      if (w == null || now - w.start() >= 60) { windows.put(key, new Window(now, 1)); return true; }
      if (w.count() >= limit) return false;
      windows.put(key, new Window(w.start(), w.count() + 1));
      return true;
    } finally {
      lock.unlock();
    }
  }
  public long lastOr(long d) { return last.orElse(d); }
  public boolean seen(String key) { return windows.containsKey(key); }
}`, 'Windows'))
  expect(x.notes.join(' ')).toMatch(/the step is atomic/)
  step(x, 'a hit is remembered', (_b, a) => a.last_none.not(), b => b.method.is('hit'))
})

tj('the clock and an answered call of other code, each the request\'s (the check\'s copy of the code rewritten)', () => {
  const x = ok(java(`
public class Lease {
  private long expires;
  private int grants;
  public boolean grant(String who) {
    long now = System.currentTimeMillis();
    if (now < expires) return false;
    expires = now + Quota.ttl(who);
    grants++;
    return true;
  }
}`, 'Lease', {answers: {'Quota.ttl': 'int'}}, {'Quota.java': 'public class Quota { public static int ttl(String who) { throw new IllegalStateException("other code"); } }'}))
  expect(x.notes.join(' ')).toMatch(/answered by the request/)
  step(x, 'a grant sets the lease from now', (b, a) => a.expires.eq(b.ttl.plus(b.now)), b => b.expires.atMost(b.now))
})

tj('the boundary inferred: a field @Autowired (a store), a constructor\'s injected interface (its call an answer the harness stubs), the entry', () => {
  const x = ok(java(`
public class Counter {
  @Autowired private Repo repo;
  private final Limits limits;
  private int total;
  public Counter(Limits limits) { this.limits = limits; }
  public boolean hit(String key) {
    Integer n = repo.get(key);
    int cur = n == null ? 0 : n;
    if (cur >= limits.limitFor(key)) return false;
    repo.put(key, cur + 1);
    total++;
    return true;
  }
  public int total() { return total; }
}`, 'Counter', {entry: undefined}, {
    'Repo.java': 'public interface Repo { Integer get(String key); void put(String key, Integer v); }',
    'Limits.java': 'public interface Limits { int limitFor(String key); }',
    'Autowired.java': 'public @interface Autowired {}',
  }))
  const notes = x.notes.join(' ')
  expect(notes).toMatch(/the entry inferred: Counter/)
  expect(notes).toMatch(/repo: an injected dependency \(marked so\)/)
  expect(notes).toMatch(/answered by the request \(inferred/)
  step(x, 'a hit counts one, or none where it is refused', (b, a) => a.total.eq(b.total.plus(1)).or(a.total.eq(b.total)).and(a.hit_result.iff(a.total.eq(b.total.plus(1)))), b => b.total.lt(1000).and(b.total.atLeast(0)))
})

tj('a throw is the step\'s refusal; a failure after a write is refused unless the caller drops the write', () => {
  const src = `
public class Gate {
  private int open;
  public void enter(int n) {
    if (n < 0) throw new IllegalArgumentException("n < 0");
    open += n;
    if (open > 100) throw new IllegalStateException("full");
  }
}`
  const bad = java(src, 'Gate')
  expect(bad.ok).toBe(false)
  expect(bad.refusals[0]!.what).toMatch(/after the state is written/)
  ok(java(src, 'Gate', {onError: 'discard'}))
})

tj('refused where it leaves the subset, each with why', () => {
  const cases: [string, RegExp][] = [
    ['for (int i = 0; i < n; i++) x++;', /a loop/],
    ['try { x = n; } catch (RuntimeException e) { x = 0; }', /try/],
    ['java.util.function.IntUnaryOperator f = v -> v + 1; x = f.applyAsInt(n);', /lambda|other code/],
    ['int[] a = new int[3]; x = a[0];', /array/],
  ]
  for (const [body, why] of cases) {
    const r = java(`public class C { int x; public void go(int n) { ${body} } }`, 'C')
    expect(r.ok).toBe(false)
    expect(r.refusals[0]!.what).toMatch(why)
  }
})

tk('Kotlin: when on an enum, a nullable Long (?:, !!, smart casts), check, @Synchronized', () => {
  const x = ok(kotlin(`
enum class State { CLOSED, OPEN, HALF_OPEN }
class Breaker(private val threshold: Int, private val coolDown: Long) {
  var state = State.CLOSED
    private set
  private var failures = 0
  private var openedAt: Long? = null
  @Synchronized
  fun onFailure(now: Long) {
    when (state) {
      State.CLOSED -> { failures++; if (failures >= threshold) { state = State.OPEN; openedAt = now } }
      State.HALF_OPEN -> { state = State.OPEN; openedAt = now }
      State.OPEN -> {}
    }
  }
  @Synchronized
  fun allow(now: Long): Boolean {
    if (state == State.OPEN) {
      val at = openedAt ?: return false
      if (now - at < coolDown) return false
      state = State.HALF_OPEN
    }
    return true
  }
  fun onSuccess() { check(state != State.OPEN) { "open" }; state = State.CLOSED; failures = 0; openedAt = null }
}`, 'Breaker', {failures: 'kept'}))
  expect(inv(x, 'an open breaker knows when it opened', s => s.state.is('OPEN').not().or(s.openedAt_none.not())).proven).toBe(true)
})

tk('Kotlin: a map\'s [] with ?:, require, Int wraparound, coerceAtLeast', () => {
  const x = ok(kotlin(`
class Counts(private val cap: Int) {
  private val seen = mutableMapOf<String, Int>()
  private var total = 0
  fun add(key: String, n: Int) {
    require(n >= 0) { "n" }
    seen[key] = ((seen[key] ?: 0) + n).coerceAtMost(cap)
    total += n
  }
  fun countOf(key: String): Int = seen[key] ?: 0
}`, 'Counts', {onError: 'discard'}))
  expect(x.source).toContain('4294967296')
})

tk('Kotlin: an immutable data class\'s method returning its next value is a step to it; copy, scope functions', () => {
  const x = ok(kotlin(`
data class Budget(val limit: Int, val spent: Int = 0) {
  init { limit.takeIf { it >= 0 }.let { requireNotNull(it) { "limit" } } }
  fun spend(n: Int): Budget = if (n < 0 || spent + n > limit) this else copy(spent = spent + n)
  fun reset(): Budget = copy(spent = 0)
  fun left(): Int = limit - spent
}`, 'Budget', {methods: ['spend', 'reset', 'left']}))
  expect(inv(x, 'never past the limit', s => s.spent.atMost(s.limit)).proven).toBe(false)
  step(x, 'a spend within the limit adds it', (b, a) => a.spent.eq(b.spent.plus(b.spend_n)), b => b.method.is('spend').and(b.spend_n.atLeast(0)).and(b.spent.plus(b.spend_n).atMost(b.limit)).and(b.spent.atLeast(0)))
})

tk('Kotlin: the boundary inferred: a lateinit property @Autowired (a store), the entry', () => {
  const x = ok(kotlin(`
annotation class Autowired
interface Seen { fun get(key: String): Int?; fun put(key: String, n: Int) }
class Visits {
  @Autowired lateinit var seen: Seen
  private var unique = 0
  fun visit(page: String): Boolean {
    val n = seen.get(page)
    if (n == null) unique++
    seen.put(page, (n ?: 0) + 1)
    return n == null
  }
}`, 'Visits', {entry: undefined}))
  expect(x.notes.join(' ')).toMatch(/the entry inferred: Visits/)
  expect(x.notes.join(' ')).toMatch(/seen: an injected dependency \(marked so\)/)
})

tk('Kotlin: refused where it leaves the subset, each with why', () => {
  const r = kotlin(`class C { var x = 0\n fun go(xs: List<Int>) { for (v in xs) x += v } }`, 'C')
  expect(r.ok).toBe(false)
  expect(r.refusals[0]!.what).toMatch(/loop/)
})
