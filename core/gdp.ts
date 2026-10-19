// gdp-ts's proofs, minted by proven rules. gdp-ts (Ghosts of Departed Proofs for TypeScript) makes every call site
// present a proof that a check ran on exactly these values, and trusts the module that performs the check; gdp-wired
// proves the check. A guard is a function's condition whose laws are proven; a gate is a rule's flag whose laws hold
// along every run. Each is made from the trusted module's prover, proves its laws when it is made (and refuses to be
// made otherwise), and mints a proof only where the proven condition holds, computed from the same terms the laws are
// about. The trusted module keeps its prover private, as gdp-ts's lint asks, and exports the function that mints.
//
//   // proofs/can-read.ts
//   const CanRead = defineProof('CanRead')
//   export interface CanRead<U, D> extends Proof<'CanRead', [U, D]> {}
//   const mint = guard(CanRead, access, 'permit', {laws: accessLaws})
//   export const canRead = async <U, D>(user: Named<U, UserId>, doc: Named<D, DocId>): Promise<CanRead<U, D> | null> =>
//     mint(await db.accessFacts(user.value, doc.value), user, doc)
//
// Nothing here is trusted: the kernel checks the proofs, and both runtimes are held to the reference evaluator. What
// stays the trusted module's job is what gdp-ts already asks of it: that the facts it reads are about the names it
// mints for. A request outside what the laws were proven for (an `assume` that fails, a history read out of order) mints
// nothing and leaves a gate's state as it was; a value that isn't of its kind is refused with the RangeError both
// runtimes refuse it with. Either way no proof is minted: the proof fails closed.
import type {Named, NamesOf, Proof, Prover} from '@gdp-ts/core'
import {type Decision, type Fun, type Rule, type StepLaw, type Verdict, Unproven, funOf, proveDecision, proveSteps} from './dsl.ts'
import {type Law, type State, evalC, interpret} from './machine.ts'
import {allowed, requestEnv} from './watch.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyNamed = Named<any, any>
// Mints a proof of kind K about the named values it is given, or returns null: `args` are the values the condition reads.
export type Mint<K extends string, A> = <S extends AnyNamed[]>(args: A, ...about: S) => Proof<K, NamesOf<S>> | null

export {Unproven}
const proven = (what: string, v: Verdict): void => { if (!(v.proven && v.checked)) throw new Unproven(what, v) }

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyFun = Fun<any, any, any>
// The fields of a function's result that are conditions (booleans when it runs).
type Conditions<O> = {[k in keyof O]: O[k] extends boolean ? k : never}[keyof O] & string
type ArgsOf<F extends AnyFun> = Parameters<F['run']>[0]
type ParamsOf<F extends AnyFun> = NonNullable<Parameters<F['run']>[1]>

// A proof wherever `fn`'s result `field` holds. Every law in `laws` must have been stated about `fn` (fn.law or
// fn.relate) and is proven now; the arguments it is later called with must meet the function's kinds and `assume`.
//   const access = fun('document access').inputs({...}).returns(env => ({permit: permit(env)}))
//   const mint = guard(CanRead, access, 'permit', {laws: [access.law('...', ...)]})
export function guard<K extends string, F extends AnyFun>(prover: Prover<K>, fn: F, field: Conditions<ReturnType<F['run']>>, opts: {laws: Decision[], params?: ParamsOf<F>}): Mint<K, ArgsOf<F>> {
  if (opts.laws.length === 0) throw new Error(`${fn.name}: a guard needs a law to prove`)
  for (const d of opts.laws) {
    if (funOf(d) !== fn) throw new Error(`${fn.name}: "${d.name}" was not stated about this function (state it with ${fn.name}.law)`)
    proven(`${fn.name}: "${d.name}"`, proveDecision(d))
  }
  const r = fn.rule, m = r.machine, params = (opts.params ?? {}) as ParamsOf<F>, ps = r.encodeParams(params as never)
  if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) throw new Error(`${fn.name}: the params ${JSON.stringify(params)} don't meet its precondition`)
  return (args, ...about) => {
    const input = r.encodeInput(args as never)
    if (m.assume && !evalC(m.assume, {...ps, ...input} as Record<string, number>, {scalars: {}, maps: {}}, m)) return null
    return (fn.run(args as never, params) as Record<string, unknown>)[field] === true ? prover.prove(...about) : null
  }
}

// eslint-disable-next-line @typescript-eslint/no-explicit-any
type AnyRule = Rule<any, any, any, any, any, any, any, any>
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type FlagOf<R> = R extends Rule<any, any, any, any, infer F, any, any, any> ? keyof F & string : never
type InputOf<R extends AnyRule> = Parameters<R['encodeInput']>[0]
type RuleParams<R extends AnyRule> = Parameters<R['encodeParams']>[0]

// A running rule that mints a proof for each request whose step takes `flag`.
export type Gate<K extends string, I> = {
  // Takes the request's step (every allowed request is a step, granted or not, as the laws were proven about), and
  // mints a proof about `about` if the flag held in it.
  request: Mint<K, I>
  // The state now, as the compiled rule keeps it (maps and the log are updated in place by the next request); save it
  // and pass it back as `state` to resume.
  readonly state: State
  // The state's scalars as runtime values.
  values(): Record<string, unknown>
}

// A proof for each request whose step takes `flag`, the rule's laws (and step laws) proven now. One gate holds one
// run's state: keep one per state it guards (per process, or loaded and saved around each request in a transaction).
//   const tokens = rule('one-time tokens').inputs({...}).maps({...}).flags(env => ({redeem: ...})).step(...)
//   const redeem = gate(Redeemed, tokens, 'redeem', {laws: tokenLaws})
//   redeem.request({op: 'redeem', token: 7}, user, token) // a Redeemed proof the first time, null after
export function gate<K extends string, R extends AnyRule>(prover: Prover<K>, r: R, flag: FlagOf<R>, opts: {laws: Law[], stepLaws?: StepLaw[], params?: RuleParams<R>, state?: State}): Gate<K, InputOf<R>> {
  const m = r.machine
  if (!(flag in (m.step.flags ?? {}))) throw new Error(`${m.name}: no flag ${flag}`)
  if (opts.laws.length + (opts.stepLaws?.length ?? 0) === 0) throw new Error(`${m.name}: a gate needs a law to prove`)
  proven(m.name, proveSteps(r, opts.laws, opts.stepLaws ?? []))
  const params = (opts.params ?? {}) as RuleParams<R>, ps = r.encodeParams(params as never)
  if (m.pre && !evalC(m.pre, ps, {scalars: {}, maps: {}}, m)) throw new Error(`${m.name}: the params ${JSON.stringify(params)} don't meet its precondition`)
  const run = interpret(m), compiled = r.compiled()
  let st: State = opts.state ?? compiled.init(ps)
  return {
    request: (args, ...about) => {
      const input = r.encodeInput(args as never)
      if (!allowed(m, run, ps, st, input)) return null
      const granted = requestEnv(m, run, ps, st, input)[`?${flag}`] === 1
      st = compiled.step(ps, st, input)
      return granted ? prover.prove(...about) : null
    },
    get state() { return st },
    values: () => r.decode(st),
  }
}
