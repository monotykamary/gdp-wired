// The CLI on a small file in each language (core/cli.ts): the rule read with nothing configured, one law stated in the
// code's own form proven, one broken with the run that breaks it, and the exit code 1. Each skipped where its toolchain
// isn't installed (the suite's cli-<lang> jobs install them).
import {expect, test} from 'bun:test'
import {execFileSync, spawnSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, readFileSync as readAdv, realpathSync, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {dirname} from 'node:path'
import {pathToFileURL} from 'node:url'
import {check, colors} from './cli.ts'
import {lawsIn, parse} from './laws.ts'

const has = (cmd: string, ...a: string[]) => { try { execFileSync(cmd, a, {stdio: 'ignore'}); return true } catch { return false } }
const javac = process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac'
// The JVM front ends need a JDK 17 or later, Kotlin's also kotlinc 2.4 (the compiler its reader is built against): an
// older or other toolchain, which the reader refuses saying so, is skipped here saying so.
const jvmWhy = (kt: boolean): string | undefined => {
  let v = ''
  try { v = execFileSync('sh', ['-c', '"$0" -version 2>&1', javac], {encoding: 'utf8'}) } catch { return 'no javac' }
  const m = /javac (\d+)(?:\.(\d+))?/.exec(v), major = m ? (m[1] === '1' ? Number(m[2]) : Number(m[1])) : 0
  if (major < 17) return `${v.trim()}: a JDK 17 or later is needed`
  if (!kt) return undefined
  let home = process.env.KOTLIN_HOME
  if (!home) { try { home = dirname(dirname(realpathSync(execFileSync('sh', ['-c', 'command -v kotlinc'], {encoding: 'utf8'}).trim()))) } catch { return 'no kotlinc' } }
  let kv: string | undefined
  for (const f of [`${home}/build.txt`, `${home}/libexec/build.txt`]) { try { kv = readAdv(f, 'utf8').trim(); break } catch { /* not there */ } }
  return kv !== undefined && !kv.startsWith('2.4.') ? `kotlinc ${kv}: the Kotlin reader is built against kotlinc 2.4.21` : undefined
}
const jvm = (lang: string, kt: boolean) => () => { const why = jvmWhy(kt); if (why) console.warn(`${lang} skipped: ${why}`); return !why }
const TOOLS: Record<string, () => boolean> = {
  python: () => has('python3', '--version'), ruby: () => has('ruby', '-e', 'require "prism"'), elixir: () => has('elixir', '-e', ':ok'),
  java: jvm('java', false), kotlin: jvm('kotlin', true),
  go: () => has('go', 'version'), rust: () => has('cargo', '--version'), swift: () => has(process.env.GDP_SWIFT ?? 'swift', '--version'), c: () => has('clang', '--version'), cpp: () => has('clang++', '--version'), ts: () => true,
  effect: () => true, xstate: () => true,
}
// The case's files (the first the one checked), written to a fresh directory (its node_modules, where the code imports a
// package, this repository's: effect 4.x, xstate 5.x).
const files = (fs: Record<string, string>, modules = false): string => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-clicase-`)
  for (const [f, text] of Object.entries(fs)) { mkdirSync(`${dir}/${f}`.replace(/\/[^/]*$/, ''), {recursive: true}); writeFileSync(`${dir}/${f}`, text) }
  if (modules) symlinkSync(new URL('../node_modules', import.meta.url).pathname, `${dir}/node_modules`)
  return dir
}
const CASES: Record<string, {files: Record<string, string>, target?: string, modules?: boolean}> = {
  python: {files: {'limiter.py': `
def gdp_law(text):
    return lambda f: f


class Limiter:
    def __init__(self, limit: int):
        self.limit = limit
        self.used = 0

    # gdp: law a counted hit adds its cost: result implies used == old(used) + cost
    @gdp_law("every hit counts: used == old(used) + cost")
    def hit(self, cost: int) -> bool:
        if cost <= 0 or self.used + cost > self.limit:
            return False
        self.used += cost
        return True
`}},
  ruby: {files: {'limiter.rb': `
class Limiter
  def initialize(limit)
    @limit = limit
    @count = 0
  end

  # gdp: law a hit counts at most one: @count <= old(@count) + 1
  # gdp: law every hit counts: @count == old(@count) + 1
  def hit
    return false if @count >= @limit
    @count += 1
    true
  end
end
`}},
  elixir: {files: {'counter.ex': `
defmodule Counter do
  use GenServer
  @type t :: %{count: non_neg_integer, limit: non_neg_integer}
  def init({limit}), do: {:ok, %{count: 0, limit: limit}}
  # gdp: law a hit counts at most one: count <= old(count) + 1
  @gdp_law "every hit counts: count == old(count) + 1"
  def handle_call(:hit, _from, %{count: c, limit: l} = s) when c >= l, do: {:reply, :full, s}
  def handle_call(:hit, _from, s), do: {:reply, :ok, %{s | count: s.count + 1}}
end
`}},
  java: {files: {'demo/Limiter.java': `package demo;

@interface GdpLaw { String value(); }

public class Limiter {
  private final int limit;
  private int count;
  public Limiter(int limit) { this.limit = limit; }
  // gdp: law a hit counts at most one: count <= old(count) + 1
  @GdpLaw("every hit counts: this.count == old(this.count) + 1")
  public boolean hit() {
    if (count >= limit) return false;
    count++;
    return true;
  }
}
`}},
  kotlin: {files: {'Limiter.kt': `package demo

annotation class GdpLaw(val value: String)

class Limiter(private val limit: Int) {
    private var count = 0
    // gdp: law a hit counts at most one: count <= old(count) + 1
    @GdpLaw("every hit counts: count == old(count) + 1")
    fun hit(): Boolean {
        if (count >= limit) return false
        count += 1
        return true
    }
}
`}},
  go: {files: {'p/limiter.go': `package p

type Limiter struct{ count, limit int }

// gdp: law a hit counts at most one: count <= old(count) + 1
// gdp: law every hit counts: l.count == old(l.count) + 1
func (l *Limiter) Hit() bool {
	if l.count >= l.limit {
		return false
	}
	l.count++
	return true
}

func (l *Limiter) SetLimit(n int) {
	if n >= 0 {
		l.limit = n
	}
}
`, 'go.mod': 'module example.com/clicase\n\ngo 1.22\n'}, target: 'p'},
  rust: {files: {'src/lib.rs': `
pub struct Limiter { count: u32, limit: u32 }

impl Limiter {
    pub fn new(limit: u32) -> Self { Self { count: 0, limit } }
    #[doc = "gdp: law a hit counts at most one: self.count <= old(self.count) + 1"]
    /// gdp: law every hit counts: count == old(count) + 1
    pub fn hit(&mut self) -> bool {
        if self.count >= self.limit { return false; }
        self.count += 1;
        true
    }
}
`, 'Cargo.toml': '[package]\nname = "clicase"\nversion = "0.1.0"\nedition = "2021"\npublish = false\n\n[lib]\npath = "src/lib.rs"\n'}, target: '.'},
  swift: {files: {'limiter.swift': `
final class Limiter {
  private var count = 0
  let limit: Int
  init(limit: Int) { self.limit = limit }

  // gdp: law a hit counts at most one: count <= old(count) + 1
  // gdp: law every hit counts: count == old(count) + 1
  func hit() -> Bool {
    if count >= limit { return false }
    count += 1
    return true
  }
}
`}},
  c: {files: {'lim.c': `
struct lim { int count; int limit; };

// gdp: law a hit counts at most one: count <= old(count) + 1
// gdp: law every hit counts: l->count == old(l->count) + 1
int hit(struct lim *l) {
  if (l->count >= l->limit) return 0;
  l->count++;
  return 1;
}

void set_limit(struct lim *l, int n) { if (n >= 0 && n < 1000) l->limit = n; }
`}},
  cpp: {files: {'lim.cpp': `
class Lim {
 public:
  explicit Lim(int limit) : limit_(limit) {}
  // gdp: law a hit counts at most one: count_ <= old(count_) + 1
  // gdp: law every hit counts: this->count_ == old(this->count_) + 1
  bool hit() {
    if (count_ >= limit_) return false;
    count_++;
    return true;
  }
 private:
  int limit_;
  int count_ = 0;
};
`}},
  ts: {files: {'limiter.ts': `
export class Limiter {
  private count = 0
  constructor(private readonly limit: number) {}
  // gdp: law a hit counts at most one: this.count <= old(this.count) + 1
  // gdp: law every hit counts: count == old(count) + 1
  hit(): boolean {
    if (this.count >= this.limit) return false
    this.count++
    return true
  }
}
`}},
  // An Effect service: its Refs the state, the laws above its make effect; read with effect from the file's project.
  effect: {modules: true, files: {'limiter.ts': `
import {Effect, Ref} from 'effect'

// gdp: law a hit counts at most one: count <= old(count) + 1
// gdp: law every hit counts: count == old(count) + 1
export const make = (limit: number) => Effect.gen(function* () {
  const count = yield* Ref.make(0)
  const hit = Effect.fn('hit')(function* () {
    const c = yield* Ref.get(count)
    if (c >= limit) return false
    yield* Ref.set(count, c + 1)
    return true
  })
  return {hit}
})
`}},
  // An XState machine: its context the state, `value` its state, `event` the event; xstate from the file's project.
  xstate: {modules: true, files: {'counter.ts': `
import {assign, setup} from 'xstate'

// gdp: law a hit counts at most one: count <= old(count) + 1
// gdp: law every hit counts: count == old(count) + 1
// gdp: law it stays open: value == "open"
export const counter = setup({
  types: {} as {context: {count: number, limit: number}},
  guards: {room: ({context}) => context.count < context.limit},
}).createMachine({
  context: {count: 0, limit: 3},
  initial: 'open',
  states: {open: {on: {hit: {guard: 'room', actions: assign({count: ({context}) => context.count + 1})}}}},
})
`}},
}

for (const [lang, c] of Object.entries(CASES)) {
  (TOOLS[lang]!() ? test : test.skip)(`${lang}: a law stated in the code proven, one broken with its run, exit 1`, async () => {
    const target = `${files(c.files, c.modules)}/${c.target ?? Object.keys(c.files)[0]}`
    const {rules, exit} = await check([target], {ms: 5000, propose: false, check: {runs: 30, depth: 6, states: 60}})
    const r = rules.find(x => x.ok) ?? rules[0]!
    if (!r.ok) throw new Error(`refused: ${JSON.stringify(r.refusals)}`)
    const by = (n: string) => r.laws.find(l => l.name === n) ?? (() => { throw new Error(`no law ${n}: ${JSON.stringify(r.laws)}`) })()
    expect(by(lang === 'python' ? 'a counted hit adds its cost' : 'a hit counts at most one').verdict).toBe('proven')
    const broken = by('every hit counts')
    expect(broken.verdict).toBe('broken')
    expect(broken.run!.length).toBeGreaterThan(0)
    expect(broken.run!.at(-1)!).toMatch(/hit/i)
    if (lang === 'xstate') expect(by('it stays open').verdict).toBe('proven')
    expect(exit).toBe(1)
    // (every law stated in the code is reported, each once at least: none dropped by any language's reader)
    const stated = Object.entries(c.files).flatMap(([f, text]) => lawsIn(text, f.split('/').pop()!).map(l => l.where))
    const told = new Set(rules.flatMap(x => x.laws.map(l => l.where)))
    expect(stated.filter(w => !told.has(w))).toEqual([])
  }, 300_000)
}

// `check .` in the crate: the target is printed as `.`, not as its absolute path.
;(TOOLS.rust!() ? test : test.skip)('rust: check . in the crate prints the target as ., not its absolute path', async () => {
  const d = files(CASES.rust!.files), was = process.cwd()
  process.chdir(d)
  try { const {rules} = await check(['.'], {ms: 2000, propose: false, check: {runs: 10, depth: 4, states: 20}}); expect(rules[0]!.file).toBe('.') } finally { process.chdir(was) }
}, 300_000)

// One way in: each front end called the short way (a file: URL and nothing else: the entry inferred, effect and xstate
// from the file's project; Go and Rust given a file of the package or crate) reads the rule its call as it was reads
// (the path or the code, the entry named, the module given), on the same cases.
type Read = {ok: boolean, source?: string, rule?: {machine: unknown}, refusals: unknown[]}
const url = (p: string) => pathToFileURL(p)
const WAYS: Record<string, (d: string) => Promise<[Read, Read]>> = {
  python: async d => { const {extractPython: f} = await import('./extract-py.ts'); return [f(`${d}/limiter.py`, {entry: 'Limiter'}), f(url(`${d}/limiter.py`))] },
  ruby: async d => { const {extractRuby: f} = await import('./extract-rb.ts'); return [f(`${d}/limiter.rb`, {entry: 'Limiter'}), f(url(`${d}/limiter.rb`))] },
  elixir: async d => { const {extractElixir: f} = await import('./extract-ex.ts'); return [f(`${d}/counter.ex`, {entry: 'Counter'}), f(url(`${d}/counter.ex`))] },
  java: async d => { const {extractJava: f} = await import('./extract-jvm.ts'); return [f(`${d}/demo/Limiter.java`, {entry: 'Limiter'}), f(url(`${d}/demo/Limiter.java`))] },
  kotlin: async d => { const {extractKotlin: f} = await import('./extract-jvm.ts'); return [f(`${d}/Limiter.kt`, {entry: 'Limiter'}), f(url(`${d}/Limiter.kt`))] },
  go: async d => { const {extractGo: f} = await import('./extract-go.ts'); return [f(`${d}/p`, {entry: 'Limiter'}), f(url(`${d}/p/limiter.go`))] },
  // (Rust, the entry named: every pub fn of its impl read, `new` too, so the methods are named with it)
  rust: async d => { const {extractRust: f} = await import('./extract-rs.ts'); return [f(d, {entry: 'Limiter', methods: ['hit']}), f(url(`${d}/src/lib.rs`))] },
  swift: async d => { const {extractSwift: f} = await import('./extract-swift.ts'); return [f(`${d}/limiter.swift`, {entry: 'Limiter'}), f(url(`${d}/limiter.swift`))] },
  // (C: `methods`, the name every front end has for the requests read; `functions` its old name)
  c: async d => { const {extractC: f} = await import('./extract-c.ts'); return [f(`${d}/lim.c`, {entry: 'lim', functions: ['hit', 'set_limit']}), f(url(`${d}/lim.c`), {methods: ['hit', 'set_limit']})] },
  cpp: async d => { const {extractCpp: f} = await import('./extract-c.ts'); return [f(`${d}/lim.cpp`, {entry: 'Lim'}), f(url(`${d}/lim.cpp`))] },
  ts: async d => { const {extract: f} = await import('./extract.ts'); return [f(readAdv(`${d}/limiter.ts`, 'utf8'), {file: `${d}/limiter.ts`, entry: 'Limiter'}), f(url(`${d}/limiter.ts`))] },
  effect: async d => { const {extractEffect: f} = await import('./effect.ts'), effect = await import('effect'); return [f(readAdv(`${d}/limiter.ts`, 'utf8'), {file: `${d}/limiter.ts`, entry: 'make', effect}), f(url(`${d}/limiter.ts`))] },
  xstate: async d => { const {extractXState: f} = await import('./extract.ts'), xstate = await import('xstate'); return [f(readAdv(`${d}/counter.ts`, 'utf8'), {file: `${d}/counter.ts`, entry: 'counter', xstate}), f(url(`${d}/counter.ts`))] },
}
for (const [lang, way] of Object.entries(WAYS)) {
  (TOOLS[lang]!() ? test : test.skip)(`${lang}: one way in, a URL and nothing else read the rule the call as it was reads`, async () => {
    const [was, now] = await way(files(CASES[lang]!.files, CASES[lang]!.modules))
    if (!was.ok) throw new Error(`refused: ${JSON.stringify(was.refusals)}`)
    expect(now.ok).toBe(true)
    expect(now.source).toBe(was.source)
    expect(JSON.stringify(now.rule!.machine)).toBe(JSON.stringify(was.rule!.machine))
  }, 600_000)
}

test('the forms a law is stated in, and the expression syntax', () => {
  const text = [
    '# gdp: law a: x <= 1', '// gdp: law b: x >= old(x)', '-- gdp: law c: not failed', '/* gdp: law d: x == 1 */',
    '@GdpLaw("e: x != \\"s\\"")', '@gdp.law("f: x < 2")', '@gdp_law "g: x > 0"', '#[doc = "gdp: law h: x <= y + 1"]',
    'x = 1  # not a law', '# gdp: skip',
  ].join('\n')
  expect(lawsIn(text, 'f').map(l => `${l.name}|${l.expr}|${l.line}`)).toEqual(['a|x <= 1|1', 'b|x >= old(x)|2', 'c|not failed|3', 'd|x == 1|4', 'e|x != "s"|5', 'f|x < 2|6', 'g|x > 0|7', 'h|x <= y + 1|8'])
  for (const e of ['a and b or not c', 'x <= y + 2 * z implies failed', 'forall k in m: m[k].spent <= m[k].limit', 'cache["hits:" + s] > 0', 'cache[f"hits:{s}"] > 0',
    'team.max_budget is not None', 'k not in m', 'mode == :closed', 'old(x) - 1 >= before.y', 'get_spend(...) >= 0', 'min(a, b) <= max(a, b)', 'x ≤ y ∧ ¬p → q', 'l->count == old(l->count) + 1']) expect(() => parse(e)).not.toThrow()
  expect(() => parse('x <= ')).toThrow()
  expect(() => parse('x <= 1.5')).toThrow(/whole/)
})

test('a law is known by its name, after.x and before.x are the view of a step, and what isn\'t read is refused', async () => {
  const dir = files({'w.ts': `
export class W {
  n = 0
  // gdp: law up: after.n >= before.n
  // gdp: law twice: n >= 0
  // gdp: law twice: n >= 1
  // gdp: law no expression
  // gdp: law a call with arguments: f(n) >= 0
  // gdp: law a key by a method: this.m.get(1) >= 0
  inc(): void { this.n++ }
}
`})
  const {rules, exit} = await check([`${dir}/w.ts`], {ms: 2000, propose: false})
  const v = Object.fromEntries(rules[0]!.laws.map(l => [`${l.name}@${l.where}`, `${l.verdict}: ${l.why ?? ''}`]))
  expect(v['up@w.ts:4']).toMatch(/^proven/)
  expect(v['twice@w.ts:5']).toMatch(/not read: a law of this name is stated twice/)
  expect(v['twice@w.ts:6']).toMatch(/not read: a law of this name is stated twice/)
  expect(v['no expression@w.ts:7']).toMatch(/not read: .*<name>: <expr>/)
  expect(v['a call with arguments@w.ts:8']).toMatch(/not read: no f/)
  expect(v['a key by a method@w.ts:9']).toMatch(/not read: no this\.m/)
  expect(v['a call with arguments@w.ts:8']).not.toMatch(/write the key/)
  expect(exit).toBe(2)
})

test('gdp.toml, pyproject.toml\'s [tool.gdp] and package.json\'s "gdp": the options of every rule and of one', async () => {
  const {configFor, toml} = await import('./cli.ts')
  expect(toml('failures = "kept" # all\n[rules.H]\nmethods = ["a", \'b\']\nstores.c.attrs = {"d.e" = "None", n = 3}\n[rules."x.y"]\nstrict = true\n'))
    .toEqual({failures: 'kept', rules: {H: {methods: ['a', 'b'], stores: {c: {attrs: {'d.e': null, n: 3}}}}, 'x.y': {strict: true}}})
  expect(() => toml('x = [1,\n2]')).toThrow(/can't read/)
  const py = files({'pyproject.toml': '[project]\nname = "p"\ndeps = [\n  "a",\n]\n[tool.gdp]\nfailures = "kept"\n[tool.gdp.rules.H]\nmethods = ["hit"]\n[tool.other]\nx = 1\n', 'src/m.py': ''})
  expect(configFor(`${py}/src`)).toMatchObject({all: {failures: 'kept'}, rules: {H: {methods: ['hit']}}})
  const js = files({'package.json': '{"name": "p", "gdp": {"onError": "discard", "rules": {"W": {"methods": ["inc"]}}}}', 'src/w.ts': ''})
  expect(configFor(`${js}/src`)).toMatchObject({all: {onError: 'discard'}, rules: {W: {methods: ['inc']}}})
  // (a rule's options from gdp.toml: SessionLimit's request and its kept failure)
  const dir = files({'s.py': `
class SessionLimit:
    def __init__(self, cache, limit: int):
        self.cache = cache
        self.limit = limit

    # gdp: law each hit counts one: cache["hits:" + session] == old(cache["hits:" + session]) + 1
    async def hit(self, session: str) -> None:
        key = f"hits:{session}"
        n = await self.cache.get(key)
        n = (n or 0) + 1
        await self.cache.set(key, n)
        if n > self.limit:
            raise RuntimeError("over the limit")
`, 'gdp.toml': '[rules.SessionLimit]\nfailures = "kept"\n'})
  if (!TOOLS.python!()) return
  const {rules} = await check([`${dir}/s.py`], {ms: 3000, propose: false})
  expect(rules[0]!.laws.map(l => l.verdict)).toEqual(['proven'])
})

// The adversarial round's Java shapes (research/langs/adversarial: j01, j03, j04, a dependency handed `this`): the CLI
// reports each rule refused and its law not read, never proven.
;(TOOLS.java!() ? test : test.skip)('the CLI refuses a dependency given the rule\'s state (the adversarial j01, j03, j04)', async () => {
  for (const id of ['j01', 'j03', 'j04']) {
    const src = readAdv(new URL(`../research/langs/adversarial/${id}/Meter.java`, import.meta.url).pathname, 'utf8')
    const dir = files({'Meter.java': src.replace(/^public class Meter \{/m, '// gdp: law n stays zero: n == 0\npublic class Meter {')})
    const {rules, exit} = await check([`${dir}/Meter.java`], {ms: 3000, propose: false, check: {runs: 30, depth: 6, states: 60}})
    expect(rules.length).toBe(1)
    expect(rules[0]!.ok).toBe(false)
    expect(rules[0]!.refusals.map(r => r.what).join('; ')).toMatch(/given the rule's state/)
    expect(rules[0]!.laws.every(l => l.verdict !== 'proven')).toBe(true)
    expect(exit).toBe(2)
  }
}, 180_000)

// Color: only on a terminal; piped, with --json, NO_COLOR (any value) or TERM=dumb plain; FORCE_COLOR on. Uncolored, the
// text is what it was, byte for byte (the colored text less its escapes).
test('color on a terminal only, NO_COLOR over a terminal, FORCE_COLOR on, and the same text without it', () => {
  expect(colors({}, true)).toBe(true)
  expect(colors({}, false)).toBe(false)
  expect(colors({NO_COLOR: ''}, true)).toBe(false)
  expect(colors({NO_COLOR: '1'}, true)).toBe(false)
  expect(colors({TERM: 'dumb'}, true)).toBe(false)
  expect(colors({FORCE_COLOR: '1'}, false)).toBe(true)
  expect(colors({FORCE_COLOR: '0'}, true)).toBe(true)
  expect(colors({FORCE_COLOR: '0', NO_COLOR: '1'}, true)).toBe(false)
  expect(colors({FORCE_COLOR: '1'}, true, true)).toBe(false)
  const dir = files({'wallet.ts': `export class Wallet {
  balance = 0
  // gdp: law a debit never overdraws: balance >= 0
  debit(x: number): boolean { if (x <= 0) throw new Error('positive'); if (x > this.balance) return false; this.balance -= x; return true }
  // gdp: law a credit adds one more: balance == old(balance) + x + 1
  credit(x: number): void { if (x <= 0) throw new Error('positive'); this.balance += x }
}
`})
  const env = Object.fromEntries(Object.entries(process.env).filter(([k]) => !['NO_COLOR', 'FORCE_COLOR'].includes(k)))
  const run = (more: Record<string, string>, ...flags: string[]) => spawnSync('bun', [new URL('./cli.ts', import.meta.url).pathname, 'check', `${dir}/wallet.ts`, '--no-propose', ...flags], {env: {...env, ...more}, encoding: 'utf8'})
  const piped = run({}), forced = run({FORCE_COLOR: '1'}), json = run({FORCE_COLOR: '1'}, '--json')
  expect(piped.status).toBe(1)
  expect(piped.stdout).not.toContain('\x1b[')
  expect(piped.stdout).toContain('    proven   a debit never overdraws  (wallet.ts:3)\n')
  expect(piped.stdout).toContain('    broken   a credit adds one more  (wallet.ts:5)\n')
  expect(piped.stdout).toContain('1 of 2 stated laws proven, 1 broken, 0 unknown, 0 not read\n')
  expect(forced.stdout).toContain('\x1b[32mproven\x1b[0m   a debit never overdraws  \x1b[2m(wallet.ts:3)\x1b[0m')
  expect(forced.stdout).toContain('\x1b[31mbroken\x1b[0m')
  expect(forced.stdout).toContain('\x1b[32m1\x1b[0m of 2 stated laws proven, \x1b[31m1\x1b[0m broken')
  expect(forced.stdout.split('\x1b').map((p, i) => (i ? p.replace(/^\[\d+m/, '') : p)).join('')).toBe(piped.stdout)
  expect(json.stdout).not.toContain('\x1b[')
}, 180_000)


// Two classes of one Python file with no bases (`class X:`), each its laws: a field named `state` read bare, a set read
// before the step (`k in old(s)`); a variant that breaks one comes back broken with its run.
;(TOOLS.python!() ? test : test.skip)('the CLI on two classes with no bases: their laws by class, a field named state, k in old(s)', async () => {
  const dir = files({'fate.py': `
from typing import Literal


class Fate:
    # gdp: law modal only after tries strikes: state != "modal" or fails >= tries

    def __init__(self, tries: int):
        if tries < 1:
            raise ValueError("tries")
        self.tries = tries
        self.state: Literal["queued", "placed", "modal"] = "queued"
        self.fails = 0
        self.vm = ""
        self.avoid: set[str] = set()

    def place(self, vm: str) -> None:
        if self.state == "queued":
            self.state = "placed"
            self.vm = vm

    # gdp: law one strike per VM: fails == old(fails) or vm not in old(avoid)
    def failed(self, vm: str) -> None:
        if self.state != "placed" or self.vm != vm:
            return
        self.state = "queued"
        if vm in self.avoid:
            return
        self.avoid.add(vm)
        self.fails += 1
        if self.fails >= self.tries:
            self.state = "modal"


class Counter:
    # gdp: law at most cap: n <= cap

    def __init__(self, cap: int):
        if cap < 0:
            raise ValueError("cap")
        self.cap = cap
        self.n = 0

    def hit(self) -> None:
        if self.n < self.cap:
            self.n += 1
`})
  const {rules, exit} = await check([`${dir}/fate.py`], {ms: 5000, propose: false})
  expect(rules.map(r => [r.entry, r.laws.map(l => [l.name, l.verdict])])).toEqual([
    ['Fate', [['modal only after tries strikes', 'proven'], ['one strike per VM', 'proven']]], ['Counter', [['at most cap', 'proven']]]])
  expect(exit).toBe(0)
  // (the strike charged whatever VM: the law about distinct VMs broken, with its run)
  writeFileSync(`${dir}/fate.py`, readAdv(`${dir}/fate.py`, 'utf8').replace('        if vm in self.avoid:\n            return\n', ''))
  const b = await check([`${dir}/fate.py`], {ms: 5000, propose: false})
  const law = b.rules[0]!.laws.find(l => l.name === 'one strike per VM')!
  expect(law.verdict).toBe('broken')
  expect(law.run!.join('\n')).toMatch(/failed\(vm=/)
  expect(b.exit).toBe(1)
}, 180_000)

// A law about an argument the code ignores (the bug is that it does): the argument kept in the rule, the law broken.
;(TOOLS.python!() ? test : test.skip)('the CLI on a law reading an argument the code ignores: broken, with its run', async () => {
  const dir = files({'waits.py': `
class Waits:
    def __init__(self):
        self.fails = 0

    # gdp: law a wait counts only where a start failed: fails == old(fails) or start_failed
    def waited(self, start_failed: bool) -> None:
        self.fails += 1
`})
  const {rules, exit} = await check([`${dir}/waits.py`], {ms: 5000, propose: false})
  expect(rules[0]!.laws.map(l => l.verdict)).toEqual(['broken'])
  expect(rules[0]!.laws[0]!.run!.join('\n')).toMatch(/waited\(start_failed=false\)/)
  expect(exit).toBe(1)
}, 180_000)

// from = "any": a law proven only with an invariant the search finds holds from the start, not from every state the laws
// allow; stated beside it, the invariant makes the two one inductive set, proven from any state.
;(TOOLS.python!() ? test : test.skip)('the CLI from any state: a law needing an invariant refuted from a state alone, proven with it stated', async () => {
  const code = (helper: boolean) => `
class Mirror:
    # gdp: law b within 3: b <= 3
${helper ? '    # gdp: law a within 3: a <= 3\n' : ''}
    def __init__(self):
        self.a = 0
        self.b = 0

    def hit(self) -> None:
        if self.a < 3:
            self.a += 1
        self.b = self.a
`
  const dir = files({'mirror.py': code(false), 'gdp.toml': 'from = "any"\n'})
  const a = await check([`${dir}/mirror.py`], {ms: 5000, propose: false})
  // (true from the start, not inductive alone: unknown, the law it needs said)
  expect(a.rules[0]!.laws.map(l => l.verdict)).toEqual(['unknown'])
  expect(a.rules[0]!.laws[0]!.why).toMatch(/not inductive from every state the laws allow/)
  const reach = await check([`${dir}/mirror.py`], {ms: 5000, propose: false, from: 'reachable'})
  expect(reach.rules[0]!.laws.map(l => l.verdict)).toEqual(['proven'])
  writeFileSync(`${dir}/mirror.py`, code(true))
  const b = await check([`${dir}/mirror.py`], {ms: 5000, propose: false})
  expect(b.rules[0]!.laws.map(l => [l.verdict, l.from])).toEqual([['proven', 'any'], ['proven', 'any']])
}, 180_000)

// Laws of "eventually" in the code's comments: `<from> leads to <to> by <rank> via [<cond> ->] <method>(<arg> = <value>)`,
// an episode of the class (a subclass whose requests gdp.toml names) where other requests would undo the progress.
;(TOOLS.python!() ? test : test.skip)('the CLI on laws of "eventually": proven with their rank and helpful requests, not where a step undoes it', async () => {
  const dir = files({'retry.py': `
from typing import Literal


class Retry:
    # gdp: law a waiting job ends: state == "waiting" leads to state != "waiting" by tries - fails via fail(boat = true)

    def __init__(self, tries: int):
        if tries < 1:
            raise ValueError("tries")
        self.tries = tries
        self.fails = 0
        self.state: Literal["waiting", "done", "gave_up"] = "waiting"

    def fail(self, boat: bool) -> None:
        if self.state != "waiting" or not boat:
            return
        self.fails += 1
        if self.fails >= self.tries:
            self.state = "gave_up"

    def finish(self) -> None:
        if self.state == "waiting":
            self.state = "done"


class Resettable(Retry):
    # gdp: law a job of a resettable kind ends: state == "waiting" leads to state != "waiting" by tries - fails via fail(boat = true)
    def reset(self) -> None:
        self.fails = 0
`})
  const {rules} = await check([`${dir}/retry.py`], {ms: 5000, propose: false})
  const v = Object.fromEntries(rules.flatMap(r => r.laws.map(l => [`${r.entry}: ${l.name}`, l.verdict])))
  expect(v['Retry: a waiting job ends']).toBe('proven')
  expect(v['Resettable: a job of a resettable kind ends']).toBe('unknown')
}, 180_000)


// No law stated is dropped: a class that writes no state is read (its law a decision's); a law on a method is the
// class's even where a module function of its name comes later; one that no rule takes is reported not read, exit 2.
;(TOOLS.python!() ? test : test.skip)('the CLI accounts for every law: a stateless class, a later function of a method\'s name, a law no rule takes', async () => {
  const dir = files({'m.py': `
class Ok:
    def __init__(self):
        self.n = 0

    def hit(self) -> None:
        self.n += 1


class Gate:
    # gdp: law nothing but health answers without the token: health or token_ok or not result
    def allows(self, health: bool, token_ok: bool) -> bool:
        return health or token_ok


class Store:
    def __init__(self):
        self.n = 0

    # gdp: law a made tree was asked for: not result or ok
    def make_tree(self, ok: bool) -> bool:
        if ok:
            self.n += 1
        return ok


def make_tree(tid: str) -> dict:
    return {}


class Spin:
    def __init__(self):
        self.n = 0

    # gdp: law spins stop: n >= 0
    def spin(self) -> None:
        while self.n < 3:
            self.n += 1
`})
  const {rules, exit} = await check([`${dir}/m.py`], {ms: 5000, propose: false})
  const v = Object.fromEntries(rules.flatMap(r => r.laws.map(l => [l.name, [r.entry, l.verdict]])))
  expect(v['nothing but health answers without the token']).toEqual(['Gate', 'proven'])
  expect(v['a made tree was asked for']).toEqual(['Store', 'proven'])
  expect(v['spins stop']![1]).toBe('not read')
  const stated = lawsIn(readAdv(`${dir}/m.py`, 'utf8'), 'm.py').map(l => l.where), told = new Set(rules.flatMap(r => r.laws.map(l => l.where)))
  expect(stated.filter(w => !told.has(w))).toEqual([])
  expect(exit).toBe(2)
}, 180_000)

// A start whose constructor arithmetic passes 2^53 - 1 is outside the rule's numbers, as a step past them is: left out of
// the check (and said so), not a refusal of the class.
;(TOOLS.python!() ? test : test.skip)('the CLI on a constructor whose arithmetic may pass 2^53: those starts left out, the class read', async () => {
  const dir = files({'t.py': `
class Tries:
    # gdp: law never past its tries: made <= max_tries or made == 0
    def __init__(self, max_tries: int, max_wait: int, t0: float):
        self.max_tries = max_tries
        self.deadline = t0 + max_wait
        self.made = 0

    def another(self, now: float) -> bool:
        return self.made < self.max_tries and now <= self.deadline

    def never_up(self) -> None:
        if self.made < self.max_tries:
            self.made += 1
`})
  const {rules} = await check([`${dir}/t.py`], {ms: 5000, propose: false})
  expect(rules[0]!.ok).toBe(true)
  expect(rules[0]!.laws.map(l => l.verdict)).toEqual(['proven'])
}, 180_000)

// What the code names, a law names the same: a field named failed (the keyword yields to it), a module's constant, a
// class found by its statement (never a word of a docstring); a sum it can't take is a law not read, never a crash.
;(TOOLS.python!() ? test : test.skip)('the CLI reads laws in the code\'s names: a field named failed, a module constant, a class not taken from prose; an integer sum read', async () => {
  const dir = files({'n.py': `
LIMIT = 3


class Creation:
    # gdp: law every start boat made no VM for is given back: refunded == failed
    # gdp: law at most LIMIT asks: asks <= LIMIT

    def __init__(self):
        self.failed = 0
        self.refunded = 0
        self.asks = 0

    def made(self, asked: int, got: int) -> None:
        """(the record holds what boat made)"""
        if self.asks < LIMIT:
            self.asks += 1
        if got < asked:
            self.failed += asked - got
            self.refunded += asked - got


class Pending:
    def __init__(self):
        self.pending: dict[str, int] = {}
        self.need = 0

    # gdp: law the need is the pending sum: need == sum(pending)
    def add(self, name: str, slots: int) -> None:
        if name in self.pending:
            return
        self.pending[name] = slots
        self.need += slots
`, 'gdp.toml': 'from = "any"\n'})
  const {rules} = await check([`${dir}/n.py`], {ms: 5000, propose: false})
  const v = Object.fromEntries(rules.flatMap(r => r.laws.map(l => [l.name, [r.entry, l.verdict]])))
  expect(v['every start boat made no VM for is given back']).toEqual(['Creation', 'proven'])
  expect(v['at most LIMIT asks']).toEqual(['Creation', 'proven'])
  // (a sum of a map of integers: its positive parts less its negative parts; from any state it needs the laws about them)
  expect(v['the need is the pending sum']![1]).not.toBe('not read')
}, 180_000)

// What supercomputer's rules hit, each read as the code means it: a constant bound to another's name, a field never
// shadowed by another method's argument, a product of factors the path keeps at 0 or above, a comparison with x // k, a
// sum of a map of integers after a step, a function's law never a same-named method's, a class's last law its own, a
// gdp.toml rule only where the file defines it; and from any state, the largest inductive set of laws proven, a law
// outside it said to need one beside it.
;(TOOLS.python!() ? test : test.skip)('the CLI on supercomputer\'s shapes: aliases, shadowing, guarded products, floor division, integer sums, scoping, Houdini', async () => {
  const dir = files({'s.py': `
IDLE = 60
LONG = IDLE


# gdp: law a demand keeps a VM no longer than the idle time: not declared or result <= 60
def release_ttl(declared: bool) -> int:
    if declared:
        return LONG
    return IDLE


# gdp: law a share of a count never exceeds the count: share_pct > 100 or limit <= 0 or result <= limit
def ceiling(share_pct: int, limit: int) -> int:
    if share_pct <= 0 or limit <= 0:
        return 0
    return share_pct * limit // 100


# gdp: law a batch's budget is within the starts left: result <= max(0, left)
def budget(left: int, share_pct: int, cap: int) -> int:
    if share_pct < 0 or cap < 0:
        raise ValueError("at least 0")
    if left <= 0:
        return 0
    k = min(left, max(2, share_pct * left // 100))
    if cap > 0:
        return min(k, cap)
    return k


class Entry:
    def __init__(self):
        self.up = True
        self.lease = "none"
        self.until = 0

    # gdp: law a warm lease never takes a VM about to stop: lease == old(lease) or (up and until > now + 8)
    def lease_warm(self, now: int) -> None:
        if self.up and self.until > now + 8:
            self.lease = "ours"

    def release(self, now: int, up: bool) -> None:
        self.lease = "none"
        self.up = up


class Grow:
    def __init__(self, vms: int):
        self.vms = vms
        self.free = vms

    # gdp: law a step grows by a quarter of the pool at most: result <= 1 or result <= vms // 4
    def grow(self) -> int:
        if self.free <= 0:
            return 0
        k = min(self.free, max(1, self.vms // 4))
        self.free -= k
        return k


class Pending:
    def __init__(self):
        self.pending: dict[str, int] = {}
        self.need = 0

    def add(self, name: str, slots: int) -> None:
        if slots < 0 or name in self.pending:
            return
        self.pending[name] = slots
        self.need += slots

    # gdp: law a row back keeps the need the pending sum: need == sum(pending)
    def back(self, name: str) -> None:
        if name not in self.pending:
            return
        self.need -= self.pending.pop(name)


class Item:
    # gdp: law finished at most once: finishes <= 1
    # gdp: law taken at most once more than lost: runs <= tries + 1

    def __init__(self):
        self.queued = True
        self.runs = 0
        self.tries = 0
        self.finishes = 0

    def take(self) -> None:
        if self.queued:
            self.queued = False
            self.runs += 1

    def lose(self) -> None:
        if not self.queued and self.tries == 0:
            self.tries = 1
            self.queued = True
        elif not self.queued and self.finishes == 0:
            self.finishes = 1


class Holder:
    """Holds the time budgets."""

    def __init__(self):
        self.n = 0

    def hit(self) -> None:
        self.n += 1

    # gdp: law at most one hold a call: n <= old(n) + 1


def hit(x: int) -> int:
    return x
`, 'gdp.toml': 'from = "any"\n[rules.budgets]\n'})
  const {rules} = await check([`${dir}/s.py`], {ms: 8000, propose: false})
  const v = Object.fromEntries(rules.flatMap(r => r.laws.map(l => [l.name, [r.entry, l.verdict]])))
  expect(v['a demand keeps a VM no longer than the idle time']).toEqual(['release_ttl', 'proven'])
  expect(v['a share of a count never exceeds the count']).toEqual(['ceiling', 'proven'])
  expect(v['a warm lease never takes a VM about to stop']).toEqual(['Entry', 'proven'])
  expect(v["a batch's budget is within the starts left"]).toEqual(['budget', 'proven'])
  expect(v['a step grows by a quarter of the pool at most']).toEqual(['Grow', 'proven'])
  expect(v['finished at most once']).toEqual(['Item', 'proven'])
  expect(v['taken at most once more than lost']).toEqual(['Item', 'unknown'])
  expect(v['at most one hold a call']).toEqual(['Holder', 'proven'])
  expect(rules.some(r => r.entry === 'budgets')).toBe(false)
  // (a sum of integers after a step: from the start, the search finds the sums' laws; from any state it needs them)
  const reach = await check([`${dir}/s.py`], {ms: 8000, propose: false, from: 'reachable', entry: 'Pending'})
  expect(reach.rules[0]!.laws.map(l => l.verdict)).toEqual(['proven'])
}, 300_000)
