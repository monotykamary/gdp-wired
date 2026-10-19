// Type-level checks for the gdp-ts adapter (gdp.ts): every line marked @ts-expect-error must fail to type-check, and
// `tsc -p .` fails if one of them doesn't. Never run: type-checked only.
import {type Named, type Proof, defineProof, name} from '@gdp-ts/core'
import {bool, fun, lit, nat, oneOf, rule, upTo} from './dsl.ts'
import {gate, guard} from './gdp.ts'

interface CanRead<U, D> extends Proof<'CanRead', [U, D]> {}
declare function readDocument<U, D>(doc: Named<D, number>, proof: CanRead<U, D>): void

export function typeChecks() {
  const access = fun('access').inputs({level: upTo(3), cleared: bool}).returns(({level, cleared}) => ({permit: cleared.or(level.eq(0)), shown: level}))
  const laws = [access.law('above public, cleared', (env, out) => [out.permit, env.level.gt(0)], (_, env) => env.cleared)]
  const mint = guard(defineProof('CanRead'), access, 'permit', {laws})
  // @ts-expect-error shown is a number, not a condition
  guard(defineProof('CanRead'), access, 'shown', {laws})
  // @ts-expect-error not a field of the result
  guard(defineProof('CanRead'), access, 'allow', {laws})

  name(1, 2, (user, doc) => {
    const proof = mint({level: 1, cleared: true}, user, doc)
    if (!proof) return
    readDocument(doc, proof)
    // @ts-expect-error a proof about (user, doc) is not a proof about this other document
    readDocument(user, proof)
    name(3, other => {
      // @ts-expect-error nor about a document named elsewhere
      readDocument(other, proof)
    })
  })
  // @ts-expect-error the arguments are the function's inputs
  mint({lvl: 1, cleared: true})

  const tokens = rule('tokens').inputs({op: oneOf('issue', 'redeem'), token: nat}).maps({Used: 0})
    .flags(({op, token, Used}) => ({redeem: op.is('redeem').and(Used.at(token).eq(0))}))
    .step(({token, redeem, Used}) => ({Used: Used.bump(token, redeem)}))
  // @ts-expect-error redeemed is not a flag of the rule
  gate(defineProof('Redeemed'), tokens, 'redeemed', {laws: []})
  const g = gate(defineProof('Redeemed'), tokens, 'redeem', {laws: []})
  // @ts-expect-error the request is the rule's inputs
  g.request({op: 'redeem', tkn: 1})
  const nested = fun('nested').inputs({c: bool}).returns(({c}) => ({v: {ok: c, n: lit(1)}}))
  guard(defineProof('Ok'), nested, 'v.ok', {laws})
  // @ts-expect-error v.n is a number, not a condition
  guard(defineProof('Ok'), nested, 'v.n', {laws})
}
