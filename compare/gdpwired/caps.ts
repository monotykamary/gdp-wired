// Rule 2, per-key caps, in gdp-wired's typed builders: a request (acct, day, ok) is granted iff ok and its account
// has no grant yet and its day has fewer than d. The counts are maps from key to count; the laws hold at every key.
import {bool, forall, nat, proveRule, rule} from '../../core/dsl.ts'
import {compileJs} from '../../core/machine.ts'

// --- rule
export const caps = rule('caps')
  .params({d: nat})
  .inputs({acct: nat, day: nat, ok: bool})
  .maps({Acct: 0, Day: 0})
  .flags(({ok, acct, day, d, Acct, Day}) => ({granted: ok.and(Acct.at(acct).lt(1), Day.at(day).lt(d))}))
  .step(({acct, day, granted, Acct, Day}) => ({Acct: Acct.bump(acct, granted), Day: Day.bump(day, granted)}))

// --- laws
export const capLaws = [
  caps.law('grants per acct <= 1', ({Acct}) => forall(k => Acct.at(k).atMost(1))),
  caps.law('grants per day <= d', ({Day, d}) => forall(k => Day.at(k).atMost(d))),
]

// --- proofs
export const verdict = () => proveRule(caps, capLaws)

// --- run
if (import.meta.main) {
  const t0 = performance.now(), v = verdict(), ms = (performance.now() - t0).toFixed(1)
  const js = caps.compiled(), params = caps.encodeParams({d: 2})
  let st = js.init(params)
  for (const [acct, day, ok] of [[1, 5, true], [1, 5, true], [2, 5, true], [3, 5, true], [4, 6, false]] as const) st = js.step(params, st, caps.encodeInput({acct, day, ok}))
  console.log(`caps: proven=${v.proven} checked=${v.checked} prove_ms=${ms} js_bytes=${compileJs(caps.machine).length} run day5=${st.maps.Day!.get(5)} acct1=${st.maps.Acct!.get(1)}`)
  process.exit(v.proven && v.checked ? 0 : 1)
}
