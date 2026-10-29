// rate limit/gcra/GcraState: extracted from gcra 0.6.0 (crates.io; lytefast/gcra-rs), src/gcra.rs: GcraState::check_and_modify_at, revert_at (and the closures in them); src/rate_limit.rs: RateLimit::increment_interval. MIT, (c) Sam Shih.
// Extracted by gdp-wired/extract from gcra.rs (GcraState, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const gcraStateRule = rule("GcraState")
  .inputs({method: oneOf('check_and_modify_at', 'revert_at'), check_and_modify_at_arrived_at: int, check_and_modify_at_cost: nat, check_and_modify_at_rate_limit_emission_interval: nat, check_and_modify_at_rate_limit_period: nat, revert_at_arrived_at: int, revert_at_cost: nat, revert_at_rate_limit_emission_interval: nat})
  .state({tat: int.from(0), tat_none: bool.from(true), failed: bool.from(false)})
  .assume(({method, check_and_modify_at_cost, check_and_modify_at_rate_limit_emission_interval, check_and_modify_at_rate_limit_period, revert_at_cost, revert_at_rate_limit_emission_interval}) => all(method.is('check_and_modify_at').implies(all(check_and_modify_at_cost.atLeast(0), check_and_modify_at_cost.atMost(4294967295))), method.is('check_and_modify_at').implies(check_and_modify_at_rate_limit_emission_interval.atLeast(0)), method.is('check_and_modify_at').implies(check_and_modify_at_rate_limit_period.atLeast(0)), method.is('revert_at').implies(all(revert_at_cost.atLeast(0), revert_at_cost.atMost(4294967295))), method.is('revert_at').implies(revert_at_rate_limit_emission_interval.atLeast(0))))
  .step(({method, check_and_modify_at_rate_limit_emission_interval, check_and_modify_at_cost, tat_none, check_and_modify_at_rate_limit_period, tat, check_and_modify_at_arrived_at, revert_at_rate_limit_emission_interval, revert_at_cost, revert_at_arrived_at}) => {
    const t1 = method.is('check_and_modify_at')
    const t2 = check_and_modify_at_rate_limit_emission_interval.mul(check_and_modify_at_cost)
    const t3 = t2.lt(0)
    const t4 = t2.atLeast(0)
    const t5 = check_and_modify_at_rate_limit_period.lt(t2)
    const t6 = all(tat_none, t5)
    const t7 = tat_none.implies(t2.atMost(check_and_modify_at_rate_limit_period))
    const t8 = t2.atMost(check_and_modify_at_rate_limit_period)
    const t9 = all(tat_none, t8)
    const t10 = tat.lt(check_and_modify_at_arrived_at)
    const t11 = all(t10, t5)
    const t12 = all(check_and_modify_at_arrived_at.atMost(tat), t5)
    const t13 = all(t10, t8)
    const t14 = tat.plus(t2)
    const t15 = t14.minus(check_and_modify_at_rate_limit_period).atMost(check_and_modify_at_arrived_at)
    const t16 = any(t9, all(t10.implies(t8), check_and_modify_at_arrived_at.atMost(tat).implies(t8), any(t13, t15)))
    const t17 = all(t4, t7, t16)
    const t18 = when(t6, not(tat_none), any(t9, when(t11, not(tat_none), when(t12, not(tat_none), any(t13, t15, not(tat_none))))))
    const t19 = when(t17, t18, when(t3, not(tat_none), t18))
    const t20 = when(t6, tat, when(t9, check_and_modify_at_arrived_at.plus(t2), when(t11, tat, when(t12, tat, when(t13, tat.max(check_and_modify_at_arrived_at).plus(t2), when(t15, t14, tat))))))
    const t21 = revert_at_rate_limit_emission_interval.mul(revert_at_cost)
    const t22 = t21.lt(0)
    const t23 = when(t21.atLeast(0), all(not(tat_none), revert_at_arrived_at.atMost(tat)), not(tat_none))
    return {tat: when(t1, when(t19, when(t17, t20, when(t3, tat, t20)), 0), when(t23, when(t22, tat, when(tat_none, tat, tat.minus(t21))), 0)), tat_none: when(t1, not(t19), not(t23)), failed: any(all(t1, any(all(t1, t3), all(t1, t4, t7.implies(all(tat_none.implies(t5), not(all(t10.implies(t8), check_and_modify_at_arrived_at.atMost(tat).implies(t8), any(t13, t15)))))))), all(method.is('revert_at'), t22))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const gcraStateInvariants = [gcraStateRule.law("tat: a None one holds 0", ({tat, tat_none}) => any(tat_none.not(), tat.eq(0)))]
