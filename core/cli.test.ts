// The CLI on a small file in each language (core/cli.ts): the rule read with nothing configured, one law stated in the
// code's own form proven, one broken with the run that breaks it, and the exit code 1. Each skipped where its toolchain
// isn't installed (the suite's cli-<lang> jobs install them).
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdirSync, mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {check} from './cli.ts'
import {lawsIn, parse} from './laws.ts'

const has = (cmd: string, ...a: string[]) => { try { execFileSync(cmd, a, {stdio: 'ignore'}); return true } catch { return false } }
const javac = process.env.JAVA_HOME ? `${process.env.JAVA_HOME}/bin/javac` : 'javac'
const TOOLS: Record<string, () => boolean> = {
  python: () => has('python3', '--version'), ruby: () => has('ruby', '-e', 'require "prism"'), elixir: () => has('elixir', '-e', ':ok'),
  java: () => has(javac, '-version'), kotlin: () => has(javac, '-version') && (!!process.env.KOTLIN_HOME || has('sh', '-c', 'command -v kotlinc')),
  go: () => has('go', 'version'), rust: () => has('cargo', '--version'), c: () => has('clang', '--version'), cpp: () => has('clang++', '--version'), ts: () => true,
}
// The case's files (the first the one checked), written to a fresh directory.
const files = (fs: Record<string, string>): string => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-clicase-`)
  for (const [f, text] of Object.entries(fs)) { mkdirSync(`${dir}/${f}`.replace(/\/[^/]*$/, ''), {recursive: true}); writeFileSync(`${dir}/${f}`, text) }
  return dir
}
const CASES: Record<string, {files: Record<string, string>, target?: string}> = {
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
}

for (const [lang, c] of Object.entries(CASES)) {
  (TOOLS[lang]!() ? test : test.skip)(`${lang}: a law stated in the code proven, one broken with its run, exit 1`, async () => {
    const target = `${files(c.files)}/${c.target ?? Object.keys(c.files)[0]}`
    const {rules, exit} = await check([target], {ms: 5000, propose: false, check: {runs: 30, depth: 6, states: 60}})
    const r = rules.find(x => x.ok) ?? rules[0]!
    if (!r.ok) throw new Error(`refused: ${JSON.stringify(r.refusals)}`)
    const by = (n: string) => r.laws.find(l => l.name === n) ?? (() => { throw new Error(`no law ${n}: ${JSON.stringify(r.laws)}`) })()
    expect(by(lang === 'python' ? 'a counted hit adds its cost' : 'a hit counts at most one').verdict).toBe('proven')
    const broken = by('every hit counts')
    expect(broken.verdict).toBe('broken')
    expect(broken.run!.length).toBeGreaterThan(0)
    expect(broken.run!.at(-1)!).toMatch(/hit/i)
    expect(exit).toBe(1)
  }, 300_000)
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
