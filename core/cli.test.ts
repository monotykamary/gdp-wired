// The CLI on a small file in each language (core/cli.ts): the rule read with nothing configured, one law stated in the
// code's own form proven, one broken with the run that breaks it, and the exit code 1. Each skipped where its toolchain
// isn't installed (the suite's cli-<lang> jobs install them).
import {expect, test} from 'bun:test'
import {execFileSync, spawnSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, readFileSync as readAdv, symlinkSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {pathToFileURL} from 'node:url'
import {check, colors} from './cli.ts'
import {lawsIn, parse} from './laws.ts'

const has = (cmd: string, ...a: string[]) => { try { execFileSync(cmd, a, {stdio: 'ignore'}); return true } catch { return false } }
const javac = process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac'
const TOOLS: Record<string, () => boolean> = {
  python: () => has('python3', '--version'), ruby: () => has('ruby', '-e', 'require "prism"'), elixir: () => has('elixir', '-e', ':ok'),
  java: () => has(javac, '-version'), kotlin: () => has(javac, '-version') && (!!process.env.KOTLIN_HOME || has('sh', '-c', 'command -v kotlinc')),
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
  }, 300_000)
}

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
  rust: async d => { const {extractRust: f} = await import('./extract-rs.ts'); return [f(d, {entry: 'Limiter'}), f(url(`${d}/src/lib.rs`))] },
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

