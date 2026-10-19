# With gdp-ts: proven checks, proofs at every call site

[gdp-ts](https://github.com/rauchg/gdp-ts) and gdp-wired cover two halves of one guarantee:

| | Guarantees | Trusts |
|---|---|---|
| gdp-ts | Every call site presents a proof that the check ran on exactly these values (the type checker, plus its lint) | The trusted module's check |
| gdp-wired | The check is right: its laws hold for every input, or along every run (the kernel, then Lean) | Nothing beyond the kernel |

`gdp-wired/gdp` joins them: the trusted module keeps its gdp-ts prover private and hands it to gdp-wired, which proves
the check's laws when the module loads and mints a proof only where the proven condition holds. Install both:

```sh
npm install gdp-wired @gdp-ts/core
```

## A check without state: `guard`

Write the check as a `fun` whose result has a condition, state its laws with `fn.law`, and make the guard from the
prover, the function, the condition's name and the laws:

```ts
// proofs/can-read.ts
import {defineProof, type Named, type Proof} from '@gdp-ts/core'
import {bool, fun, maybe, no, oneOf, upTo} from 'gdp-wired'
import {guard} from 'gdp-wired/gdp'

const access = fun('document access')
  .inputs({role: oneOf('guest', 'staff', 'admin'), clearance: maybe(upTo(3)), level: upTo(3)})
  .returns(env => ({permit: permit(env)}))
const laws = [
  access.law('without a clearance, only public documents', (env, out) => [env.clearance.isNone, out.permit], (_, env) => env.level.eq(0)),
]

const CanRead = defineProof('CanRead') // never exported
export interface CanRead<U, D> extends Proof<'CanRead', [U, D]> {}
const mint = guard(CanRead, access, 'permit', {laws})

export async function canRead<U, D>(user: Named<U, UserId>, doc: Named<D, DocId>): Promise<CanRead<U, D> | null> {
  const facts = await db.accessFacts(user.value, doc.value) // {role, clearance, level}: about these two names
  return mint(facts, user, doc)
}
```

- The laws are proven when `guard` runs; a law that fails throws `Unproven` (with `.verdict`, the counterexample in
  `verdict.witness`), so a wrong check never becomes a trusted module.
- Only laws stated about this function are accepted (`access.law`, `access.relate`): a law about a variant is refused.
- `params` fixes the function's params: `guard(P, fn, 'ok', {laws, params: {cap: 5}})`.
- A condition inside a record of the result is named by its path: `guard(P, decide, 'verdict.ok', {laws})`.

## A check with state: `gate`

When the check depends on what happened before (a token used once, a lockout, a quota, an hourly limit), write the rule
with a flag for "this request is let through", and make a gate on the flag:

```ts
const tokens = rule('one-time tokens')
  .inputs({op: oneOf('issue', 'redeem'), token: nat})
  .maps({Issued: 0, Used: 0})
  .flags(({op, token, Issued, Used}) => ({redeem: op.is('redeem').and(Issued.at(token).eq(1), Used.at(token).eq(0))}))
  .step(({op, token, redeem, Issued, Used}) => ({Issued: Issued.bump(token, op.is('issue')), Used: Used.bump(token, redeem)}))
const laws = [tokens.law('used at most as often as issued', ({Used, Issued}) => forall(t => Used.at(t).atMost(Issued.at(t))))]

const Redeemed = defineProof('Redeemed')
export interface Redeemed<T> extends Proof<'Redeemed', [T]> {}
const redeemed = gate(Redeemed, tokens, 'redeem', {laws}) // proveSteps(tokens, laws, stepLaws) when made
export const redeem = <T>(token: Named<T, number>): Redeemed<T> | null => redeemed.request({op: 'redeem', token: token.value}, token)
```

- Every allowed request takes the rule's step, granted or not (the laws are about every step), and a proof is minted
  when that step took the flag. The compiled rule runs it: maps and the log are updated in place.
- A gate holds one run's state. Keep one per state it guards; to persist, save `gate.state` and pass it back as
  `state` (load, request, save, inside one transaction when several processes share it).
- Step laws go in `stepLaws`: "a sign-in happens only while unlocked" is a step law on the flag.

## Failing closed

- A request outside what the laws were proven for (an `assume` that fails, a history read out of order) mints nothing,
  and a gate's state is left as it was.
- A value that isn't of its kind (past `upTo(k)`, a choice not declared) throws the `RangeError` both runtimes throw.
- No proof leaves either function any other way: the prover is called only where the condition holds.

## What stays the trusted module's job

The same as in gdp-ts: the facts passed to `mint` must be about the names it mints for. gdp-wired proves what the check
decides from its facts; it can't see where the facts came from. Keep the module small, read the facts there, and let
gdp-ts's lint keep `defineProof` inside `proofs/`.

## Tests

Keep the broken check next to the proven one and assert it is refused:

```ts
expect(() => guard(defineProof('CanRead'), adminBypass, 'permit', {laws: lawsOf(adminBypass)})).toThrow(Unproven)
```

`examples/gdp.ts` in the repo runs gdp-ts's own example (who may change password protection) with a guard, and a
sign-in lockout with a gate.
