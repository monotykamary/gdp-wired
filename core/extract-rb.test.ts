// The Ruby front end (core/extract-rb.ts): rules read from Ruby through Prism, each checked against the Ruby code it
// was read from (core/rb/harness.rb). The adversarial cases: Ruby's truth (0 and "" are true), / and % of negatives
// (floor), a field nil until it is set, symbols as choices, a method's last expression as its result, raise, loops.
// Skipped where ruby (3.3 or later, with Prism) isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveSteps} from './dsl.ts'
import {type RbOptions, extractRuby} from './extract-rb.ts'

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
  if (!v.proven) throw new Error(`${name}: ${JSON.stringify({goal: v.goal, witness: v.witness})}`)
}

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
})

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
})

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
