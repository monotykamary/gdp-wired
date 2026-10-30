// The extractor's Elixir front end (`gdp-wired/extract-ex`): a module of a file read through Elixir's own parser
// (Code.string_to_quoted, core/ex/reader.exs, run with the elixir on the PATH or the one given), executed by the shared
// step executor (core/extract-step.ts), printed, built and checked as every front end's rule is, the check compiling
// the file as it ships and running it through core/ex/harness.exs. Elixir is needed only here, at extraction.
//
//   const x = extractElixir('lib/ex_break/breaker.ex')   // a path or a URL; the module inferred (or {entry: 'ExBreak.Breaker'})
//
// The subset: a module whose state is a value its functions return. A GenServer: init's {:ok, %{...}} the state (its
// argument the rule's params), each message of handle_call ({:reply, r, state}) and handle_cast ({:noreply, state}) a
// request; an Agent: each public function ending in Agent.update or Agent.get a request; plain functions: each public
// one a request on the struct's state (its first argument), returning the new state ({:ok, state} too; {:error, _} is
// the step's failure). Function clauses, case and cond, their patterns (variables, literals, ^pins, maps and structs
// by their keys) and guards; %{s | f: v}, Map.put, Map.merge with a literal, Map.get; integers (div and rem truncate,
// trunc(a / k)), atoms as choices, booleans, nil (only nil and false are false), the clock (System's and :os's times,
// DateTime.utc_now and DateTime.diff in seconds) the request's time; raise and an unmatched clause the step's failure.
//
// Refused, each where it is with why: other modules' code (but Map's and the clock's), anonymous functions, lists,
// float division, recursion, receive, and a state that isn't a map of scalars.
import {type Extraction} from './extract.ts'
import {Refusal, pathOf} from './extract-read.ts'
import {type Harness, type SModule, type StepOptions, type StepRead, extractStep, node} from './extract-step.ts'
export {proveRule, proveSteps} from './dsl.ts'

export type ExOptions = StepOptions & {elixir?: string}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
const here = (f: string) => new URL(`./ex/${f}`, import.meta.url).pathname
type ExModule = SModule & {shape?: string, msgs?: Record<string, unknown>, init?: unknown}

export function readElixir(file: string, module: string | undefined, elixir = 'elixir'): ExModule {
  const cp = node<CP>('node:child_process'), path = node<{resolve: (...p: string[]) => string}>('node:path')
  let out: string
  try { out = cp.execFileSync(elixir, [here('reader.exs'), JSON.stringify({file: path.resolve(file), module: module ?? null})], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(file, `the Elixir reader didn't run (${String((e as {stderr?: string}).stderr ?? (e as Error).message).split('\n').filter(Boolean).slice(0, 2).join(' | ')}): elixir is needed to extract Elixir`) }
  return JSON.parse(out) as ExModule
}
export function extractElixir(at: string | URL, opts: ExOptions = {}): Extraction & {read?: StepRead} {
  const file = pathOf(at)
  let mod: ExModule
  try {
    if (opts.stores && Object.keys(opts.stores).length) throw new Refusal(file, 'stores: not in the Elixir front end yet')
    if (Array.isArray(opts.entry)) throw new Refusal(file, 'one module a time (entry: its name)')
    mod = readElixir(file, opts.entry, opts.elixir)
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const harness = (): Harness => ({cmd: opts.elixir ?? 'elixir', args: [here('harness.exs')], hello: {path: mod.path, module: mod.module, shape: mod.shape, msgs: mod.msgs, init: mod.init}})
  return extractStep(mod, harness, opts)
}
