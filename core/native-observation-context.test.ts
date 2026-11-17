// Runtime instrumentation controls only. These do not manufacture or assert proof verdicts.
import {expect, test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, readFileSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

function run(runtime: string, suffix: string, source: string) {
  const dir = mkdtempSync(join(tmpdir(), 'native-context-'))
  try {
    const file = join(dir, `control.${suffix}`)
    writeFileSync(file, source)
    return spawnSync(runtime, [file], {encoding: 'utf8', timeout: 30000, env: {...process.env, ERL_FLAGS: '+S 2:2'}})
  } finally { rmSync(dir, {recursive: true, force: true}) }
}

test('Ruby only records actual calls on the active source thread', () => {
  const harness = readFileSync(join(import.meta.dir, 'rb/harness.rb'), 'utf8')
  const boundary = harness.indexOf('\nfin, fout =')
  expect(boundary).toBeGreaterThan(0)
  const result = run('ruby', 'rb', harness.slice(0, boundary) + `
NATIVE_EVENTS[0] = {'invocation' => 1, 'calls' => {}}
NATIVE_ACTIVE_THREAD[0] = NATIVE_THREAD.call
Thread.new { native_call('other-thread') { 99 }; native_clock(99) }.join
raise 'foreign thread populated the frame' unless NATIVE_EVENTS[0]['calls'].empty? && !NATIVE_EVENTS[0].key?('clock')
native_call('current') { 7 }
native_clock(12)
raise 'actual source read missing' unless NATIVE_EVENTS[0]['calls']['current'] == {'kind' => 'returned', 'value' => 7} && NATIVE_EVENTS[0]['clock'] == 12
NATIVE_ACTIVE_THREAD[0] = nil
native_call('after-return') { 99 }
native_clock(99)
raise 'post-return read populated frame' unless NATIVE_EVENTS[0]['calls'].keys == ['current'] && NATIVE_EVENTS[0]['clock'] == 12
class MethodShadow
  def method(*) = raise('user reflection called')
  def target = 7
end
raise 'untrusted method lookup' unless NATIVE_METHOD.bind_call(MethodShadow.new, :target).call == 7
class EntryRace
  def hit(value = (Thread.new { hit(99) }.join; 7))
    @seen = value
  end
end
S.replace({'leaves' => [], 'discard' => false, 'clocks' => []})
OBJS[1] = EntryRace.new
result = call({'id' => 1, 'm' => 'hit', 'a' => []})
bindings = result.fetch('nativeBindings').fetch('snapshot').fetch('root').fetch('items').to_h
raise 'foreign same-method entry was captured' unless bindings['value'] == 7 && result['out'] == 7
puts 'NATIVE_SCOPE_OK'
`)
  expect(result.status, result.stderr).toBe(0)
  expect(result.stdout.trim()).toBe('NATIVE_SCOPE_OK')
}, 40000)

test('Elixir frames reject stale processes and stop capturing after method exit', () => {
  const harness = readFileSync(join(import.meta.dir, 'ex/harness.exs'), 'utf8')
  const start = harness.indexOf('defmodule GdpNative do'), end = harness.indexOf('\ndefmodule GdpClock do')
  expect(start).toBeGreaterThan(0); expect(end).toBeGreaterThan(start)
  const result = run('elixir', 'exs', harness.slice(start, end) + `
GdpNative.init()
GdpNative.begin_call(Control, :hit)
entry = GdpNative.capture(Control, :hit, [value: 1], [:value])
GdpNative.answered("current", fn -> 7 end)
GdpNative.clock(12)
parent = self()
stale = spawn(fn ->
  Process.put(:gdp_native_active, 1)
  send(parent, :ready)
  receive do
    :go ->
      GdpNative.answered("stale", fn -> self() end)
      GdpNative.clock(99)
      try do GdpNative.answered("stale-throw", fn -> throw(:stale_throw) end) catch :throw, :stale_throw -> :ok end
      try do GdpNative.answered("stale-exit", fn -> exit(:stale_exit) end) catch :exit, :stale_exit -> :ok end
      send(parent, :done)
  end
end)
receive do :ready -> :ok after 1000 -> raise "worker missing" end
GdpNative.leave(entry)
GdpNative.answered("after-return", fn -> 99 end)
if GdpNative.answered("inactive-unsupported", fn -> self() end) != self(), do: raise "inactive return changed"
try do
  GdpNative.answered("inactive-throw", fn -> throw(:original_throw) end)
  raise "throw swallowed"
catch :throw, :original_throw -> :ok end
try do
  GdpNative.answered("inactive-exit", fn -> exit(:original_exit) end)
  raise "exit swallowed"
catch :exit, :original_exit -> :ok end
first = GdpNative.finish_call()["nativeObservations"]["snapshot"]["root"]["items"] |> Map.new(fn [key, value] -> {key, value} end)
first_calls = first["calls"]["items"] |> Map.new(fn [key, value] -> {key, value} end)
if Map.keys(first_calls) != ["current"] or first["clock"] != 12, do: raise "first frame polluted"
GdpNative.begin_call(Control, :hit)
entry = GdpNative.capture(Control, :hit, [value: 2], [:value])
send(stale, :go)
receive do :done -> :ok after 1000 -> raise "worker did not finish" end
GdpNative.leave(entry)
second = GdpNative.finish_call()["nativeObservations"]["snapshot"]["root"]["items"] |> Map.new(fn [key, value] -> {key, value} end)
if second["calls"]["items"] != [] or Map.has_key?(second, "clock"), do: raise "stale process populated new frame"
IO.puts("NATIVE_SCOPE_OK")
`)
  expect(result.status, result.stderr).toBe(0)
  expect(result.stdout.trim()).toBe('NATIVE_SCOPE_OK')
}, 40000)
