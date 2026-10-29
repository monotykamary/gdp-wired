// rate limit/nghttp2/nghttp2_ratelim: extracted from nghttp2 1.70.0 (nghttp2/nghttp2), lib/nghttp2_ratelim.c: nghttp2_ratelim_init, nghttp2_ratelim_drain (nghttp2_ratelim_update refused: UINT64_MAX is past the rule's numbers, and it divides by a variable). MIT, (c) nghttp2 contributors.
// Extracted by gdp-wired/extract from nghttp2_ratelim.c (nghttp2_ratelim, a class).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, int, Int, nat, oneOf, rule, when} from '../../../../core/dsl.ts'

export const nghttp2_ratelimRule = rule("nghttp2_ratelim")
  .inputs({method: oneOf('nghttp2_ratelim_init', 'nghttp2_ratelim_drain'), nghttp2_ratelim_init_burst: nat, nghttp2_ratelim_init_rate: nat, nghttp2_ratelim_drain_n: nat})
  .state({burst: 0, rate: 0, val: int.from(0), tstamp: 0, nghttp2_ratelim_drain_result: int.from(0)})
  .assume(({method, nghttp2_ratelim_init_burst, nghttp2_ratelim_init_rate, nghttp2_ratelim_drain_n, val}) => all(method.is('nghttp2_ratelim_init').implies(nghttp2_ratelim_init_burst.atLeast(0)), method.is('nghttp2_ratelim_init').implies(nghttp2_ratelim_init_rate.atLeast(0)), method.is('nghttp2_ratelim_drain').implies(nghttp2_ratelim_drain_n.atLeast(0)), method.is('nghttp2_ratelim_drain').implies(Int.of(nghttp2_ratelim_drain_n).atMost(val))))
  .step(({method, nghttp2_ratelim_init_burst, burst, nghttp2_ratelim_init_rate, rate, val, nghttp2_ratelim_drain_n, tstamp}) => {
    const t1 = method.is('nghttp2_ratelim_init')
    return {burst: when(t1, nghttp2_ratelim_init_burst, burst), rate: when(t1, nghttp2_ratelim_init_rate, rate), val: when(t1, nghttp2_ratelim_init_burst, val.minus(nghttp2_ratelim_drain_n)), tstamp: when(t1, 0, tstamp), nghttp2_ratelim_drain_result: 0}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const nghttp2_ratelimInvariants = [nghttp2_ratelimRule.law("burst within its type's range", ({burst}) => burst.atLeast(0)), nghttp2_ratelimRule.law("rate within its type's range", ({rate}) => rate.atLeast(0)), nghttp2_ratelimRule.law("val within its type's range", ({val}) => val.atLeast(0)), nghttp2_ratelimRule.law("tstamp within its type's range", ({tstamp}) => tstamp.atLeast(0)), nghttp2_ratelimRule.law("nghttp2_ratelim_drain_result within its type's range", ({nghttp2_ratelim_drain_result}) => nghttp2_ratelim_drain_result.atMost(2147483647).and(nghttp2_ratelim_drain_result.atLeast(-2147483648)))]
