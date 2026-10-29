// The extractor's Python front end (`gdp-wired/extract-py`): a class or functions of a module read through Python's
// own parser (core/py/reader.py, run with the python3 on the PATH or the one given), executed by the shared step
// executor (core/extract-step.ts), printed, built and checked as every front end's rule is (core/extract.ts's
// fromModel), the check running the module as it ships through core/py/harness.py. Python is needed only here, at
// extraction; the rule printed needs nothing but gdp-wired.
//
//   const x = extractPython('litellm/proxy/auth/auth_checks.py', {root: 'litellm-repo', entry: ['team_max_budget_check'],
//     answers: {get_current_spend: 'float'}, skip: ['asyncio.create_task', 'CallInfo'], failures: 'kept'})
//   if (!x.ok) console.log(x.refusals)
//
// The subset: a class (its constructor's arguments the rule's params, a dataclass's fields without defaults too) and
// the methods given, or module functions, each a request; ints (Python's, unbounded: the rule's numbers stop at ±2^53,
// past which a step is refused), floats at whole values (as JavaScript's numbers are read: a float literal that isn't
// whole is refused, and so is a true division but in math.floor, math.ceil or int of x / k), bools, strs (set and
// compared), Literal strings as choices, X | None (a None one holds 0, beside a flag), the module's dataclasses and
// classes as records (nested, by reference), dict[int | str, scalar or record] as maps (d[k], get, pop, in, del, and a
// write of one key a step), an object the caller gives as a record of inputs (its fields read, their types from its
// class's annotations in the repository's modules), if, early returns, ternaries, and/or with Python's values,
// truthiness, raise and assert (the step's failure: its refusal, or with failures: 'kept' its result), calls of the
// module's functions and methods (inlined), properties, `with` a lock (the step atomic), async methods whose awaits
// are the module's own coroutines or answered calls (each request one step: nothing else runs while it does, as no
// await suspends), time.time() as the request's time, math.isfinite (true at whole values), min, max, abs, int, float,
// bool. What a caller states (answers, skip, stores) is printed in the notes and enforced by the check.
//
// Refused, each where it is with why: loops and comprehensions, try/except, lambdas and closures, global and nonlocal,
// lists, strings beyond set and compared (an f-string is kept only as a store's key or where nothing reads it), a
// dict's truthiness, other modules' code not answered or skipped, a write to an object the caller gave, a field the
// constructor doesn't set, one object in two places of the state, two keys of one map written in one step, a write
// before a failure (unless onError: 'discard').
import {type Extraction} from './extract.ts'
import {Refusal} from './extract-read.ts'
import {type Harness, type SModule, type StepOptions, type StepRead, extractStep, node} from './extract-step.ts'

export type PyOptions = StepOptions & {
  // The repository's root (its modules importable from it); by default the file's directory.
  root?: string,
  // The Python to run (the one with the code's dependencies installed); by default python3.
  python?: string,
}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}
const here = (f: string) => new URL(`./py/${f}`, import.meta.url).pathname

// The module as the reader lowers it (the names given and the module's functions).
export function readPython(file: string, names: string[], opts: {root?: string, python?: string} = {}): SModule {
  const cp = node<CP>('node:child_process'), path = node<{resolve: (...p: string[]) => string, dirname: (p: string) => string}>('node:path')
  const abs = path.resolve(file), root = path.resolve(opts.root ?? path.dirname(abs))
  let out: string
  try { out = cp.execFileSync(opts.python ?? 'python3', ['-I', here('reader.py'), JSON.stringify({root, file: abs, names})], {encoding: 'utf8', maxBuffer: 1 << 29, stdio: ['ignore', 'pipe', 'pipe']}) }
  catch (e) { throw new Refusal(file, `the Python reader didn't run (${String((e as {stderr?: string}).stderr ?? (e as Error).message).split('\n').filter(Boolean).slice(-2).join(' | ')}): python3 is needed to extract Python`) }
  return JSON.parse(out) as SModule
}
export function extractPython(file: string, opts: PyOptions): Extraction & {read?: StepRead} {
  let mod: SModule
  try { mod = readPython(file, Array.isArray(opts.entry) ? opts.entry : [opts.entry], opts) } catch (e) {
    if (e instanceof Refusal) return {ok: false, refusals: [{where: e.where, what: e.what}], notes: []}
    throw e
  }
  const harness = (): Harness => ({cmd: opts.python ?? 'python3', args: [here('harness.py')], env: {PYTHONDONTWRITEBYTECODE: '1'}, hello: {root: mod.root, path: mod.path, module: mod.module}})
  return extractStep(mod, harness, opts)
}
