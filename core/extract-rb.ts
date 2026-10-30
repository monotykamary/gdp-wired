// The extractor's Ruby front end (`gdp-wired/extract-rb`): a class of a file read through Ruby's own parser (Prism,
// core/rb/reader.rb, run with the ruby on the PATH or the one given, 3.3 or later), executed by the shared step executor
// (core/extract-step.ts), printed, built and checked as every front end's rule is (core/extract.ts's fromModel), the
// check running the file as it ships through core/rb/harness.rb. Ruby is needed only here, at extraction.
//
//   const x = extractRuby('lib/semian/simple_state.rb', {root: 'lib', entry: 'Semian::Simple::State'})
//   if (!x.ok) console.log(x.refusals)
//
// The subset: a class (its initialize's arguments the rule's params; every field nil until it is set) and the methods
// given, its fields' types inferred from what the class assigns them (symbols a choice, nil beside numbers an optional
// number), an argument's from what it is compared with or computed into; Integers (unbounded: the rule's numbers stop
// at ±2^53), Floats at whole values, true, false, nil, Strings set and compared, Symbols as choices, constants of the
// code that are literals (read from every file under the root), attr_reader, attr_writer and attr_accessor, a method's
// last expression as its result, if, unless, the ternary, case/when on a value, early returns, &&, || and !, with
// Ruby's truth (only nil and false are false), raise (the step's refusal, or with failures: 'kept' its result), / and %
// as Ruby's (floor), nil?, zero?, positive?, negative?, abs, to_i, [a, b].min and .max, clamp, calls of the class's own
// methods (inlined), a Mutex's synchronize (the step atomic), Time.now.to_i, Process.clock_gettime and a clock object
// the caller states (`clocks`: an initialize keyword whose current_time or now is the request's time).
//
// Refused, each where it is with why: loops and blocks (but synchronize's), begin/rescue, other classes' code, arrays
// and hashes (for now), &., floats that aren't whole, a field the class writes with values of two types.
import {type Extraction} from './extract.ts'
import {Refusal} from './extract-read.ts'
import {type Harness, type SModule, type StepOptions, type StepRead, entryNames, extractStep, node} from './extract-step.ts'

export type RbOptions = StepOptions & {
  // The directory the file's requires resolve from (its library's lib/); by default the file's directory.
  root?: string,
  // The ruby to run; by default ruby.
  ruby?: string,
  // initialize's keywords that are clock objects (their current_time or now read as the request's time).
  clocks?: string[],
}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
const here = (f: string) => new URL(`./rb/${f}`, import.meta.url).pathname

// The file as the reader lowers it (the class named).
export function readRuby(file: string, names: string[], opts: {root?: string, ruby?: string, clocks?: string[]} = {}): SModule {
  const cp = node<CP>('node:child_process'), path = node<{resolve: (...p: string[]) => string, dirname: (p: string) => string}>('node:path')
  const abs = path.resolve(file), root = path.resolve(opts.root ?? path.dirname(abs))
  let out: string
  try { out = cp.execFileSync(opts.ruby ?? 'ruby', [here('reader.rb'), JSON.stringify({root, file: abs, names, clocks: opts.clocks ?? []})], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(file, `the Ruby reader didn't run (${String((e as {stderr?: string}).stderr ?? (e as Error).message).split('\n').filter(Boolean).slice(-2).join(' | ')}): ruby 3.3 or later (with Prism) is needed to extract Ruby`) }
  return JSON.parse(out) as SModule
}
export function extractRuby(file: string, opts: RbOptions): Extraction & {read?: StepRead} {
  let mod: SModule
  try {
    if (opts.answers && Object.keys(opts.answers).length) throw new Refusal(file, 'answers: not in the Ruby front end yet (a call of other code is refused where it is)')
    if (opts.stores && Object.keys(opts.stores).length) throw new Refusal(file, 'stores: not in the Ruby front end yet')
    mod = readRuby(file, entryNames(opts), opts)
    mod.stubs = false
  } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const harness = (): Harness => ({cmd: opts.ruby ?? 'ruby', args: [here('harness.rb')], hello: {root: mod.root, path: mod.path, clocks: opts.clocks ?? [], loads: (mod as SModule & {loads?: string[]}).loads ?? []}})
  return extractStep(mod, harness, opts)
}
