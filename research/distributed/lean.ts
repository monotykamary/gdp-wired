// The keyed liveness proofs exported to Lean (lean-kernel/emit.ts's toLean): each the rule with its key a param
// (keyed), the laws the proof used, and the liveness at the rank found; Lean checks every step law of it and states
// Live.lean's theorem for every run, at every value of the key.
//   bun research/distributed/lean.ts > Keyed.lean   (then lean Keyed.lean, with lean-kernel's library on LEAN_PATH)
import {type KeyedLiveness, type Rule, keyed, proveLeadsTo} from '../../core/dsl.ts'
import {type LeanItem, toLean} from '../../lean-kernel/emit.ts'
import {terminates, transactions} from './sip.ts'
import {outbox, published} from './time.ts'

// eslint-disable-next-line @typescript-eslint/no-explicit-any
const item = (id: string, r: Rule<any, any, any, any, any, any, any, any>, l: KeyedLiveness): LeanItem => {
  const v = proveLeadsTo(r, [], l, {ms: 30_000})
  if (!(v.proven && v.checked && v.rank)) throw new Error(`${id}: not proven (${v.why ?? v.goal ?? ''})`)
  const k = keyed(r, l)
  console.error(`${id}: proven, rank ${v.found?.rank}; laws ${(v.found?.laws ?? []).map(f => f.text).join('; ') || 'none'}`)
  return {id, machine: k.machine, laws: [...k.kindLaws(), ...(v.found?.laws ?? []).map(f => f.law)], liveness: [{...l, rank: v.rank}]}
}
const nict = transactions('NICT'), nist = transactions('NIST'), ob = outbox()
console.log(toLean([
  item('nict', nict, terminates('NICT', nict, false)),
  item('nist', nist, terminates('NIST', nist, true)),
  item('outbox', ob, published(ob)),
], {title: 'liveness over every key: SIP transactions terminate, outbox rows are published'}))
