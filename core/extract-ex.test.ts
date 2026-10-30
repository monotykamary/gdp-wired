// The Elixir front end (core/extract-ex.ts): rules read from Elixir through Code.string_to_quoted, each checked
// against the module it was read from, compiled and run by core/ex/harness.exs. The cases: a GenServer's clauses on
// its message and its state (patterns, guards, cond, raise), a cast, a plain module's struct state updated immutably,
// div and rem truncating, and the refusals. Skipped where elixir isn't installed.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {proveSteps} from './dsl.ts'
import {type ExOptions, extractElixir} from './extract-ex.ts'

const hasElixir = (() => { try { execFileSync('elixir', ['-e', ':ok'], {stdio: 'ignore'}); return true } catch { return false } })()
const t = hasElixir ? test : test.skip
const ex = (code: string, entry: string, more: Partial<ExOptions> = {}) => {
  const file = `${mkdtempSync(`${tmpdir()}/gdp-excase-`)}/case.ex`
  writeFileSync(file, code)
  return extractElixir(file, {entry, check: {runs: 25, depth: 6, states: 50}, ...more})
}
const ok = (x: ReturnType<typeof ex>) => {
  if (!x.ok) throw new Error(`refused: ${JSON.stringify(x.refusals)}\n${x.source ?? ''}`)
  expect(x.evidence!.mismatch).toBeUndefined()
  expect(x.evidence!.requests).toBeGreaterThan(0)
  return x
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
const step = (x: ReturnType<typeof ex>, name: string, then: (b: any, a: any) => any, when: (b: any) => any) => {
  const r = x.rule! as never as {stepLaw: (n: string, t: unknown, w: unknown) => never}
  const v = proveSteps(r as never, x.invariants ?? [], [r.stepLaw(name, then, when)])
  if (!v.proven) throw new Error(`${name}: ${JSON.stringify({goal: v.goal, witness: v.witness})}`)
}

t('a GenServer: clauses on the message and the state, a guard, cond and raise, a cast', () => {
  const x = ok(ex(`
defmodule Counter do
  use GenServer
  @type t :: %{count: non_neg_integer, limit: pos_integer, mode: :open | :closed}
  def init({limit}), do: {:ok, %{count: 0, limit: limit, mode: :open}}
  def handle_call(:hit, _from, %{mode: :closed} = s), do: {:reply, :closed, s}
  def handle_call(:hit, _from, %{count: c, limit: l} = s) when c >= l, do: {:reply, :full, %{s | mode: :closed}}
  def handle_call(:hit, _from, s), do: {:reply, :ok, %{s | count: s.count + 1}}
  def handle_call({:take, n}, _from, s) do
    cond do
      n > s.count -> raise ArgumentError, "too many"
      true -> {:reply, s.count - n, %{s | count: s.count - n}}
    end
  end
  def handle_cast(:reset, s), do: {:noreply, %{s | count: 0, mode: :open}}
end`, 'Counter'))
  step(x, 'an open counter under its limit counts a hit', (b, a) => a.count.eq(b.count.plus(1)), b => b.method.is('hit').and(b.mode.is('open')).and(b.limit.gt(b.count)))
  step(x, 'a closed counter counts nothing', (b, a) => a.count.eq(b.count), b => b.method.is('hit').and(b.mode.is('closed')))
  step(x, 'a reset reopens it', (_b, a) => a.mode.is('open'), b => b.method.is('reset'))
}, 60_000)

t('a plain module over a struct: immutable updates, div and rem truncating toward zero', () => {
  const x = ok(ex(`
defmodule Halver do
  defstruct half: 0, rest: 0, n: 0
  def split(s, k), do: %{s | half: div(k, 2), rest: rem(k, 2), n: s.n + 1}
  def clear(%__MODULE__{} = s), do: Map.put(s, :half, 0)
end`, 'Halver'))
  step(x, 'the half and the rest make k again', (b, a) => a.half.plus(a.half).plus(a.rest).eq(b.split_k), b => b.method.is('split'))
}, 60_000)

t('refused where it leaves the subset, each with why', () => {
  const r = ex(`
defmodule Q do
  defstruct items: 0
  def push(s, x), do: %{s | items: Enum.count([x])}
end`, 'Q')
  expect(r.ok).toBe(false)
  expect(r.refusals[0]!.what).toMatch(/another module's code|outside the subset/)
}, 60_000)

t('the boundary inferred: another module\'s call left out or answered (tagged: Elixir states no types), the entry', () => {
  const x = ok(ex(`
defmodule Metrics do
  def count(_name, _n), do: :ok
end
defmodule Quota do
  def bonus(n), do: rem(n, 3)
end
defmodule Meter do
  use GenServer
  @type t :: %{used: integer, cap: integer}
  def init({cap}), do: {:ok, %{used: 0, cap: cap}}
  def handle_call({:take, n}, _from, s) do
    Metrics.count("take", n)
    extra = Quota.bonus(n) # gdp: answer int
    if s.used + n + extra > s.cap, do: {:reply, :full, s}, else: {:reply, :ok, %{s | used: s.used + n + extra}}
  end
end`, undefined as never))
  const notes = x.notes.join('\n')
  expect(notes).toMatch(/the entry inferred: Meter/)
  expect(notes).toMatch(/Metrics.count .*left out \(inferred/)
  expect(notes).toMatch(/Quota.bonus .*answered by the request \(tagged/)
  step(x, 'never past its cap', (_b, a) => a.used.atMost(a.cap), b => b.used.atMost(b.cap))
}, 60_000)
