// Rule 3, the sliding-window limit, in gdp-wired's typed builders (core/models.ts windowLimit): a request (forced, t) is
// admitted iff not forced and seen + 1 <= c, where seen counts the logged requests with t < r.t + w; forced requests
// always go through; both are logged. `ours` counts the admitted, unforced records in the window ending at now (a
// param, so the law holds at every now). The relation is the one fact the kernel proves record by record.
import {bool, count, nat, proveRule, relation, rule} from '../../core/dsl.ts'
import {compileJs} from '../../core/machine.ts'

// --- rule
export const window = rule('window limit')
  .params({w: nat, c: nat, now: nat})
  .inputs({forced: bool, t: nat})
  .log('forced', 't')
  .queries({seen: (r, {t, w}) => count(t.lt(r.t.plus(w)))})
  .flags(({forced, seen, c}) => ({admitted: forced.not().and(seen.plus(1).atMost(c))}))
  .keep(({forced, admitted}) => forced.or(admitted))

// --- laws
export const observed = window.sums({ours: (r, {now, w}) => count(r.forced.not().and(r.t.atMost(now), now.lt(r.t.plus(w))))})
export const ceiling = observed.law('admitted in the window ending at now <= c', ({ours, c}) => ours.atMost(c))

// --- proofs
export const proved = observed.relations(({t, now, ours, seen}) => [relation(ours.atMost(seen), t.atMost(now))])
export const verdict = () => proveRule(proved, [ceiling])

// --- run
if (import.meta.main) {
  const t0 = performance.now(), v = verdict(), ms = (performance.now() - t0).toFixed(1)
  const js = proved.compiled(), params = proved.encodeParams({w: 10, c: 2, now: 12})
  let st = js.init(params)
  for (const [forced, t] of [[false, 1], [false, 3], [false, 4], [true, 5], [false, 12]] as const) st = js.step(params, st, proved.encodeInput({forced, t}))
  console.log(`window: proven=${v.proven} checked=${v.checked} prove_ms=${ms} js_bytes=${compileJs(proved.machine).length} run logged=${st.history!.length}`)
  process.exit(v.proven && v.checked ? 0 : 1)
}
