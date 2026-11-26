// The Ruby front end (core/extract-rb.ts): rules read from Ruby through Prism, each checked against the Ruby code it
// was read from (core/rb/harness.rb). The adversarial cases: Ruby's truth (0 and "" are true), / and % of negatives
// (floor), a field nil until it is set, symbols as choices, a method's last expression as its result, raise, loops.
// Skipped where ruby (3.3 or later, with Prism) isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveRule, proveSteps, yes} from './dsl.ts'
import {buildLaw} from './laws.ts'
import {nativeWireDecoder, snapshotNativeBindings} from './native-wire.ts'
import {nativeSame, nativeSnapshot} from './source-check.ts'
import {type RbOptions, extractRuby} from './extract-rb.ts'

// The original callbacks below test model lowering. A checked kernel proof is
// mandatory, but an unregistered callback is never a native source proof. Each
// has a same-source registered companion in nativeClaims (not a generic law).
const modelOnly = {
  proven: false, checked: false, kernelProven: true, translation: 'unchecked',
  why: 'source translation unchecked: a source proof contains a law with no native interpretation',
}
const nativeClaims: Record<string, {expr: string, method?: string}> = {
  'a hit within the limit counts': {expr: 'old(limit) > old(count) implies count == old(count) + 1', method: 'hit'},
  'seen? is whether a hit was counted since the reset': {expr: 'result == (old(last) != nil)', method: 'seen?'},
  'the half and the rest make k again': {expr: 'half + half + rest == k', method: 'split'},
  'admitted only within the cap': {expr: 'not failed implies cache["hits:" + user] <= cap'},
  'errors only where ping raised a StandardError': {expr: 'errors > old(errors) implies Remote.ping.raises == "StandardError"', method: 'hit'},
  'never past its cap but by a raise': {expr: 'n > old(n) implies old(cap) > old(n)'},
  'soft counts an error only where ping raised': {expr: 'errors > old(errors) implies Remote.ping.raises', method: 'soft'},
}
const native = (x: ReturnType<typeof rb>, name: string, expr: string, method?: string) => {
  const b = buildLaw(x, {name, expr, ...(method ? {method} : {})})
  const v = b.kind === 'step'
    ? proveSteps(x.rule!, x.invariants ?? [], [b.law])
    : proveRule(x.rule!, [...(x.invariants ?? []), b.law])
  expect(v).toMatchObject({proven: true, checked: true, translation: 'sampled'})
  expect(v.translationChecks).toBeGreaterThan(0)
}

const hasRuby = (() => { try { execFileSync('ruby', ['-e', 'require "prism"'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasRuby ? test : test.skip
const rb = (code: string, entry: string, more: Partial<RbOptions> = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-rbcase-`), file = `${dir}/case.rb`
  writeFileSync(file, code)
  return extractRuby(file, {entry, root: dir, check: {runs: 30, depth: 6, states: 60}, ...more})
}
const ok = (x: ReturnType<typeof rb>) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const step = (x: ReturnType<typeof rb>, name: string, then: (b: any, a: any) => any, when: (b: any) => any) => {
  const r = x.rule! as never as {stepLaw: (n: string, t: unknown, w: unknown) => never}
  const v = proveSteps(r as never, x.invariants ?? [], [r.stepLaw(name, then, when)])
  expect(v).toMatchObject(modelOnly)
  const claim = nativeClaims[name]
  if (!claim) throw new Error(`missing equivalent native law: ${name}`)
  native(x, `${name} (native)`, claim.expr, claim.method)
}

// Default auto-search may use 10s, beyond Bun's 5s test default.
t('a counter with a limit: Ruby\'s truth (0 is true), a field nil until it is set, the last expression as the result', () => {
  const x = ok(rb(`
class Limiter
  attr_reader :count
  def initialize(limit)
    @limit = limit
    @count = 0
  end
  def hit
    return false if @count >= @limit
    @count += 1
    @last = @count
    true
  end
  def seen?
    @last ? true : false
  end
  def reset
    @count = 0
    @last = nil
  end
end`, 'Limiter', {methods: ['hit', 'seen?', 'reset']}))
  // (0 is true in Ruby: seen? after a reset is false only because @last is nil)
  step(x, 'a hit within the limit counts', (b, a) => a.count.eq(b.count.plus(1)), b => b.method.is('hit').and(b.limit.gt(b.count)))
  step(x, 'seen? is whether a hit was counted since the reset', (b, a) => a.seen_p_result.iff(b.last_none.not()), b => b.method.is('seen?'))
}, 30_000)

// Default auto-search may use 10s, beyond Bun's 5s test default.
t('/ and % of a negative floor, as Ruby\'s do; symbols are a choice; case/when on them', () => {
  const x = ok(rb(`
class Meter
  def initialize
    @half = 0
    @rest = 0
    @mode = :idle
  end
  def split(k)
    @half = k / 2
    @rest = k % 2
  end
  def set(m)
    case m
    when :idle then @mode = :idle
    when :busy then @mode = :busy
    else raise ArgumentError, "mode"
    end
  end
end`, 'Meter', {methods: ['split', 'set']}))
  expect(x.source).toContain("oneOf('idle', 'busy')")
  step(x, 'the half and the rest make k again', (b, a) => a.half.plus(a.half).plus(a.rest).eq(b.split_k), b => b.method.is('split'))
}, 30_000)

t('refused where it leaves the subset, each with why', () => {
  const loop = rb(`
class L
  def initialize; @n = 0; end
  def go; 3.times { @n += 1 }; end
end`, 'L', {methods: ['go']})
  expect(loop.ok).toBe(false)
  expect(loop.refusals[0]!.what).toMatch(/a block/)
  const fdiv = rb(`
class F
  def initialize; @x = 0; end
  def go(k); @x = k / 2.0; end
end`, 'F', {methods: ['go']})
  expect(fdiv.ok).toBe(false)
  expect(fdiv.refusals[0]!.what).toMatch(/float/)
})

// Default auto-search may use 10s, beyond Bun's 5s test default.
t('the boundary inferred: another class\'s call left out or answered (tagged: Ruby states no types), a store injected, the entry', () => {
  const x = ok(rb(`
module Metrics
  def self.count(*) = nil
end
module Quota
  def self.bonus(user) = user.length % 3
end
class Gate
  def initialize(cache, cap)
    @cache = cache
    @cap = cap
  end
  def hit(user = "")
    Metrics.count("hit", user)
    n = (@cache.get("hits:#{user}") || 0) + Quota.bonus(user) # gdp: answer int
    @cache.set("hits:#{user}", n)
    raise "over" if n > @cap
    n
  end
end
`, undefined as never, {failures: 'kept'}))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Gate/)
  expect(notes).toMatch(/Metrics.count .*left out \(inferred/)
  expect(notes).toMatch(/Quota.bonus .*answered by the request \(tagged/)
  expect(notes).toMatch(/Gate\(cache\): an injected dependency \(inferred/)
  step(x, 'admitted only within the cap', (_b, a) => a.failed.not().implies(a.cache_hits.at(_b.user.id).value.atMost(a.cap_)), () => yes)
}, 30_000)

// Default auto-search may use 10s, beyond Bun's 5s test default.
t('begin/rescue/else/ensure and a method\'s own rescue: another class\'s call may raise what a rescue catches, a raise by its class', () => {
  const x = ok(rb(`
module Remote
  def self.ping(*) = nil
  def self.log(*) = nil
end
class Full < IndexError; end
class Gate
  def initialize(cap)
    @cap = cap
    @n = 0
    @errors = 0
  end
  def hit(k)
    begin
      Remote.ping(k)
      raise Full if @n >= @cap
      @n += 1
    rescue KeyError
      return -2
    rescue IndexError
      return -1
    rescue => e
      @errors += 1
      return 0
    else
      @n += 0
    ensure
      Remote.log(k)
    end
    @n
  end
  def soft
    Remote.ping(1)
    @n
  rescue
    @errors += 1
    0
  end
end
`, 'Gate', {failures: 'kept'}))
  expect(x.source).toContain("ping_raises: oneOf('none', 'KeyError', 'IndexError', 'StandardError')")
  // Identical original call path, distinct method-scoped symbolic raise inputs.
  // Both native companions below must resolve their own input, never the first.
  const raises = x.names!.filter(n => n.code === 'Remote.ping.raises')
  expect(raises.map(n => n.method).sort((a, b) => (a ?? '').localeCompare(b ?? ''))).toEqual(['hit', 'soft'])
  expect(new Set(raises.map(n => n.rule)).size).toBe(2)
  step(x, 'errors only where ping raised a StandardError', (b, a) => a.errors.gt(b.errors).implies(b.ping_raises.is('StandardError')), b => b.method.is('hit'))
  step(x, 'never past its cap but by a raise', (b, a) => a.n.gt(b.n).implies(b.cap_.gt(b.n)), () => yes)
  step(x, 'soft counts an error only where ping raised', (b, a) => a.errors.gt(b.errors).implies(b.soft_ping_raises), b => b.method.is('soft'))
}, 30_000)

const nativeCounter = `
class Counter
  def initialize; @total = 0; end
  def credit(n = 7)
    @total += n
    n += 1
    n
  end
end`
t('native Ruby arguments are bound at entry, not after local reassignment; corrupt lowering and disabled replay refuse', () => {
  const x = ok(rb(nativeCounter, 'Counter'))
  native(x, 'entry n is retained', 'total == old(total) + n and result == n + 1', 'credit')
  const bad = buildLaw(x, {name: 'corrupted native credit', expr: 'result == n + 2', method: 'credit'})
  if (bad.kind !== 'step') throw Error('expected step law')
  bad.law.then = {op: '<=', a: {op: 'const', value: 0}, b: {op: 'const', value: 0}}
  const rejected = proveSteps(x.rule!, x.invariants ?? [], [bad.law], {search: false})
  expect(rejected).toMatchObject({proven: false, checked: false, kernelProven: true, translation: 'error', stuck: 'translation-error'})
  expect(rejected.translationWitness?.bindings).toHaveProperty('n')
  expect(rejected.translationWitness?.after).toHaveProperty('total')
  const disabled = rb(nativeCounter, 'Counter', {check: {runs: 0, states: 0, probes: false}})
  expect(disabled.ok).toBe(true)
  const law = buildLaw(disabled, {name: 'disabled credit', expr: 'total == old(total) + n', method: 'credit'})
  expect(proveSteps(disabled.rule!, disabled.invariants ?? [], [law.law], {search: false})).toMatchObject({
    proven: false, checked: false, kernelProven: true, translation: 'unchecked',
    why: 'source translation unchecked: source replay or native-law cross-check was disabled',
  })
}, 30_000)

// Exercise the real harness directly for defaults/alias history outside the
// frontend's array subset. Input labels are intentionally not native names.
const rubyWire = (source: string, requests: Record<string, unknown>[], hello: Record<string, unknown> = {}) => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-rbwire-`)
  try {
    const file = `${dir}/case.rb`, input = `${dir}/in.jsonl`, output = `${dir}/out.jsonl`
    writeFileSync(file, source)
    writeFileSync(input, [
      {op: 'hello', path: file, root: dir, cls: 'NativeFixture', leaves: [], answers: [], loads: [], stores: {}, ...hello},
      ...requests,
    ].map(r => JSON.stringify(r)).join('\n') + '\n')
    execFileSync('ruby', [new URL('./rb/harness.rb', import.meta.url).pathname, input, output], {stdio: 'pipe'})
    return readFileSync(output, 'utf8').trim().split('\n').map(line => JSON.parse(line) as Record<string, unknown>)
  } finally { rmSync(dir, {recursive: true, force: true}) }
}
t('Ruby native wire retains real aliases and pre-call defaults, freezes historical mutable values, refuses opaque state', () => {
  const rows = rubyWire(`class NativeFixture
    def instance_of?(_); true; end
    def nil?; true; end
    def initialize; @shared = [0]; end
    def mutate(v = @shared); v[0] += 1; end
  end`, [
    {op: 'new', a: []}, {op: 'call', id: 1, m: 'mutate', a: []}, {op: 'native', id: 1},
    {op: 'call', id: 1, m: 'mutate', a: []}, {op: 'native', id: 1},
  ])
  expect(rows[0]).toMatchObject({nativeSnapshot: 1, nativeBindings: 1, nativeObservations: 1, nativeEquality: 'scalar'})
  const decode = nativeWireDecoder()
  const binding1 = snapshotNativeBindings(decode, (rows[2]!.nativeBindings as {snapshot: unknown}).snapshot) as {v: number[]}
  const after1 = nativeSnapshot(decode(rows[3]!.snapshot)) as {shared: number[]}
  const binding2 = snapshotNativeBindings(decode, (rows[4]!.nativeBindings as {snapshot: unknown}).snapshot) as {v: number[]}
  const after2 = nativeSnapshot(decode(rows[5]!.snapshot)) as {shared: number[]}
  expect(binding1.v).toEqual([0]); expect(after1.shared).toEqual([1])
  expect(binding2.v).toEqual([1]); expect(after2.shared).toEqual([2])
  expect(nativeSame(binding1.v, after1.shared)).toBe(true)
  // Identity comparisons are between snapshots, not a snapshot and the decoder's mutable canonical object. The same native object persists across calls.
  expect(nativeSame(binding2.v, after2.shared)).toBe(true)
  expect(nativeSame(binding1.v, binding2.v)).toBe(true)
  expect(nativeSame(binding1.v, after2.shared)).toBe(true)
  const first = decode((rows[2]!.nativeObservations as {snapshot: unknown}).snapshot)
  const second = decode((rows[4]!.nativeObservations as {snapshot: unknown}).snapshot)
  expect(first).toMatchObject({invocation: 1, calls: {}})
  expect(second).toMatchObject({invocation: 2, calls: {}})
  const opaque = rubyWire('class NativeFixture; def initialize; @opaque = Time.at(0); end; end', [{op: 'new', a: []}, {op: 'native', id: 1}])
  expect(opaque[2]).toEqual({error: 'ArgumentError: unsupported native snapshot object Time'})
}, 30_000)

t('Ruby observed calls retain actual subclass names, reset uncalled keys and reject conflicting outcomes', () => {
  const patch = {answers: [{key: 'Remote.ping', pass: true, patch: {mod: 'Remote', path: ['ping']}}]}
  const source = `class Full < StandardError
      def class; StandardError; end
    end
    module Remote
      @calls = 0
      def self.ping
        @calls += 1
        raise Full if @calls == 1
        nil
      end
    end
    class NativeFixture
      def initialize; @errors = 0; end
      def hit; Remote.ping; 0; rescue StandardError; @errors += 1; 0; end
      def soft; Remote.ping; 0; rescue; @errors += 1; 0; end
      def quiet; 0; end
    end`
  const rows = rubyWire(source, [
    {op: 'new', a: []}, {op: 'call', id: 1, m: 'hit', a: []},
    {op: 'call', id: 1, m: 'soft', a: []}, {op: 'call', id: 1, m: 'quiet', a: []},
  ], patch)
  const decode = nativeWireDecoder()
  expect(decode((rows[2]!.nativeObservations as {snapshot: unknown}).snapshot)).toEqual({
    invocation: 1, calls: {'Remote.ping': {kind: 'raised', raised: 'Full'}},
  })
  expect(decode((rows[3]!.nativeObservations as {snapshot: unknown}).snapshot)).toEqual({
    invocation: 2, calls: {'Remote.ping': {kind: 'returned', value: null}},
  })
  expect(decode((rows[4]!.nativeObservations as {snapshot: unknown}).snapshot)).toEqual({invocation: 3, calls: {}})
  const conflict = rubyWire(`module Remote
      @calls = 0
      def self.ping; @calls += 1; end
    end
    class NativeFixture
      def initialize; @n = 0; end
      def hit; Remote.ping; Remote.ping; 0; end
    end`, [{op: 'new', a: []}, {op: 'call', id: 1, m: 'hit', a: []}], patch)
  expect(conflict[2]!.nativeObservations).toEqual({error: 'ArgumentError: inconsistent native call Remote.ping'})
  const typeConflict = rubyWire(`module Remote
      @calls = 0
      def self.ping; @calls += 1; @calls == 1 ? :same : "same"; end
    end
    class NativeFixture
      def initialize; @n = 0; end
      def hit; Remote.ping; Remote.ping; 0; end
    end`, [{op: 'new', a: []}, {op: 'call', id: 1, m: 'hit', a: []}], patch)
  expect(typeConflict[2]!.nativeObservations).toEqual({error: 'ArgumentError: inconsistent native call type Remote.ping'})
}, 30_000)

// The adversarial round (research/langs/adversarial): no false checked proof; what reaches the rule's state, refused.
import {cases as advCases, judge, ADV} from '../research/langs/adversarial/cases.test-lib.ts'
for (const c of advCases('Ruby')) t(`adversarial ${c.id}: ${c.attack}`, () => judge(c, extractRuby(`${ADV}${c.file}`, {entry: 'Meter', root: ADV, check: {runs: 30, depth: 6, states: 60}})))

// The reader fuzz's misreads (core/extract-fuzz.ts): a call of a constant nothing defines.
t('a call of a constant nothing under the root defines: refused (a NameError where it runs)', () => {
  const r = rb(`
module Mextrics
  def self.count(*) = nil
end
class Gate
  def initialize(cap)
    @cap = cap
    @n = 0
  end
  def hit(user = "")
    Metrics.count("hit", user)
    @n += 1
  end
end
`, 'Gate')
  expect(r.ok).toBe(false)
  expect(r.refusals[0]!.what).toMatch(/Metrics, a constant nothing under the root defines \(a NameError where it runs\)/)
})

t('arithmetic on other code\'s value left out (-nil raises): read, so refused where nothing states its type', () => {
  const r = rb(`
module Remote
  def self.log(*) = nil
end
class Gate
  def initialize(cap)
    @cap = cap
    @n = 0
  end
  def hit(k)
    - Remote.log(k)
    @n += 1
  end
end
`, 'Gate')
  expect(r.ok).toBe(false)
  expect(r.refusals.map(x => x.what).join('; ')).toMatch(/Remote.log/)
})

t('a module of the files read: a method it doesn\'t define, or one whose body calls what nothing defines; a local read before it is set is nil; another class\'s arguments evaluated', () => {
  const gate = (line: string, mod = 'def self.count(*) = nil') => rb(`
module Metrics
  ${mod}
end
class Gate
  def initialize(cap)
    @cap = cap
    @n = 0
  end
  def hit(user = "")
    ${line}
    @n += 1
  end
end
`, 'Gate')
  expect(gate('Metrics.log(user)').refusals.map(x => x.what).join('; ')).toMatch(/Metrics defines no log \(a NoMethodError where it runs\)/)
  expect(gate('Metrics.count(user)', 'def self.count(*) = nxil').refusals.map(x => x.what).join('; ')).toMatch(/Metrics.count calls nxil, which nothing defines/)
  expect(gate('Metrics.count(initialize)').ok).toBe(false)
  const x = ok(rb(`
class Limiter
  def initialize(limit)
    @limit = limit
    @count = 0
  end
  def hit
    count += 1
    @count += 1
  end
end
`, 'Limiter', {failures: 'kept'}))
  expect(x.source).toMatch(/failed/)
})

t('Ruby ||= and &&= on instance and local variables preserve nil-false truthiness and short-circuiting', () => {
  const x = ok(rb(`
class Memo
  def initialize
    @hits = 0
  end
  def bump_default
    @hits += 1
    10
  end
  def threshold
    @threshold ||= bump_default
  end
  def set_zero
    @threshold = 0
  end
  def clear_if_set
    @threshold &&= 5
  end
  def local_memo(x)
    v = x > 0 ? x : nil
    v ||= 7
    return v
  end
end
`, 'Memo'))
  expect(x.evidence!.mismatch).toBeUndefined()
  // Once @threshold is initialized (even to 0, which is truthy in Ruby), threshold() must not call bump_default again.
  native(x, 'threshold initializes once and preserves 0', 'old(threshold) != nil implies hits == old(hits)', 'threshold')
  native(x, 'threshold sets 10 when nil', 'old(threshold) == nil implies threshold == 10 and hits == old(hits) + 1', 'threshold')
  native(x, 'local_memo defaults nil to 7', 'x <= 0 implies result == 7', 'local_memo')
})

t('Ruby safe navigation (&.) evaluates receiver once, short-circuits on nil only, and preserves argument skipping', () => {
  const x = ok(rb(`
class SafeNav
  def initialize
    @val = nil
    @calls = 0
    @arg_evals = 0
  end
  def set_val(n)
    @val = n
  end
  def clear
    @val = nil
  end
  def fetch
    @calls += 1
    @val
  end
  def bump_arg
    @arg_evals += 1
    1
  end
  def plus_one
    fetch&.+ bump_arg
  end
  def chained
    @val&.+ 2&.* 3
  end
  def false_is_not_nil
    f = false
    f&.nil?
  end
end
`, 'SafeNav'))
  expect(x.evidence!.mismatch).toBeUndefined()
  native(x, 'plus_one calls fetch exactly once', 'calls == old(calls) + 1', 'plus_one')
  native(x, 'plus_one skips bump_arg when nil', 'old(val) == nil implies arg_evals == old(arg_evals)', 'plus_one')
  native(x, 'plus_one adds 1 when non-nil', 'old(val) != nil implies arg_evals == old(arg_evals) + 1', 'plus_one')
  native(x, 'false&.nil? is false, not nil', 'result == false', 'false_is_not_nil')
})

t('Ruby ActiveRecord attributes (attribute, enum, write_attribute/read_attribute, db/schema.rb) read and check natively', () => {
  const dir = mkdtempSync(`${tmpdir()}/gdp-rbar-`)
  execFileSync('mkdir', ['-p', `${dir}/db`])
  writeFileSync(`${dir}/db/schema.rb`, `
ActiveRecord::Schema.define do
  create_table "stock_items" do |t|
    t.integer "count_on_hand", default: 0, null: false
    t.boolean "backorderable", default: false, null: false
  end
end
`)
  const file = `${dir}/stock_item.rb`
  writeFileSync(file, `
class ApplicationRecord
  def initialize(attributes = {})
    @attributes = {}
    attributes.each { |k, v| write_attribute(k, v) }
  end
  def read_attribute(name) = @attributes[name.to_s]
  def write_attribute(name, val) = @attributes[name.to_s] = val
  def self.attribute(name, _type = nil, default: nil)
    define_method(name) { @attributes.key?(name.to_s) ? @attributes[name.to_s] : default }
    define_method("#{name}=") { |v| write_attribute(name, v) }
    define_method("#{name}?") { !!send(name) }
  end
  def self.alias_attribute(al, orig)
    define_method(al) { send(orig) }
    define_method("#{al}=") { |v| send("#{orig}=", v) }
  end
end

class StockItem < ApplicationRecord
  attribute :count_on_hand, :integer, default: 0
  attribute :backorderable, :boolean, default: false
  alias_attribute :stock, :count_on_hand

  def in_stock?
    count_on_hand > 0
  end

  def available?
    in_stock? || backorderable?
  end

  def reduce_count_on_hand_to_zero
    write_attribute(:count_on_hand, 0) if count_on_hand > 0
  end

  def set_count_on_hand(value)
    write_attribute(:count_on_hand, value)
  end

  def restock(n)
    return false if n <= 0
    self.stock = read_attribute(:count_on_hand) + n
    true
  end
end
`)
  const x = ok(extractRuby(file, {entry: 'StockItem', root: dir, check: {runs: 30, depth: 6, states: 60}}))
  expect(x.evidence!.mismatch).toBeUndefined()
  native(x, 'in_stock? reflects positive count_on_hand', 'result == (old(count_on_hand) > 0)', 'in_stock?')
  native(x, 'available? is in_stock or backorderable', 'result == (old(count_on_hand) > 0 or old(backorderable))', 'available?')
  native(x, 'reduce_count_on_hand_to_zero never leaves positive stock', 'count_on_hand <= 0', 'reduce_count_on_hand_to_zero')
  native(x, 'restock adds positive n', 'n > 0 implies count_on_hand == old(count_on_hand) + n', 'restock')
})
