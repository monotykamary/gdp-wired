// rate limit/gcra/GcraState: extracted from gcra 0.6.0 (crates.io; lytefast/gcra-rs), src/gcra.rs: GcraState::check_and_modify_at, revert_at (and the closures in them); src/rate_limit.rs: RateLimit::increment_interval. MIT, (c) Sam Shih.
// Extracted by gdp-wired/extract from gcra.rs (GcraState, a class and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const gcraStateRule = rule("GcraState")
  .inputs({method: oneOf('check_and_modify_at', 'revert_at'), check_and_modify_at_arrived_at: int, check_and_modify_at_cost: nat, check_and_modify_at_rate_limit_emission_interval: nat, check_and_modify_at_rate_limit_period: nat, revert_at_arrived_at: int, revert_at_cost: nat, revert_at_rate_limit_emission_interval: nat})
  .state({tat: int.from(0), tat_none: bool.from(true), failed: bool.from(false)})
  .assume(({method, check_and_modify_at_cost, check_and_modify_at_rate_limit_emission_interval, check_and_modify_at_rate_limit_period, revert_at_cost, revert_at_rate_limit_emission_interval}) => all(method.is('check_and_modify_at').implies(check_and_modify_at_cost.atMost(4294967295)), method.is('check_and_modify_at').implies(check_and_modify_at_cost.atLeast(0)), method.is('check_and_modify_at').implies(check_and_modify_at_rate_limit_emission_interval.atLeast(0)), method.is('check_and_modify_at').implies(check_and_modify_at_rate_limit_period.atLeast(0)), method.is('revert_at').implies(revert_at_cost.atMost(4294967295)), method.is('revert_at').implies(revert_at_cost.atLeast(0)), method.is('revert_at').implies(revert_at_rate_limit_emission_interval.atLeast(0))))
  .step(({method, tat_none, check_and_modify_at_rate_limit_period, check_and_modify_at_rate_limit_emission_interval, check_and_modify_at_cost, tat, check_and_modify_at_arrived_at, revert_at_arrived_at, revert_at_rate_limit_emission_interval, revert_at_cost}) => {
    const t1 = method.is('check_and_modify_at')
    const t2 = check_and_modify_at_rate_limit_emission_interval.mul(check_and_modify_at_cost)
    const t3 = check_and_modify_at_rate_limit_period.lt(t2)
    const t4 = all(tat_none, t3)
    const t5 = t2.atMost(check_and_modify_at_rate_limit_period)
    const t6 = all(tat_none, t5)
    const t7 = tat.lt(check_and_modify_at_arrived_at)
    const t8 = all(t7, t3)
    const t9 = all(check_and_modify_at_arrived_at.atMost(tat), t3)
    const t10 = all(t7, t5)
    const t11 = tat.plus(t2)
    const t12 = t11.minus(check_and_modify_at_rate_limit_period).atMost(check_and_modify_at_arrived_at)
    const t13 = when(t4, not(tat_none), any(t6, when(t8, not(tat_none), when(t9, not(tat_none), any(t10, t12, not(tat_none))))))
    const t14 = all(not(tat_none), revert_at_arrived_at.atMost(tat))
    return {tat: when(t1, when(t13, when(t4, tat, when(t6, check_and_modify_at_arrived_at.plus(t2), when(t8, tat, when(t9, tat, when(t10, tat.max(check_and_modify_at_arrived_at).plus(t2), when(t12, t11, tat)))))), 0), when(t14, when(tat_none, tat, tat.minus(revert_at_rate_limit_emission_interval.mul(revert_at_cost))), 0)), tat_none: when(t1, not(t13), not(tat_none).implies(tat.lt(revert_at_arrived_at))), failed: all(t1, tat_none.implies(t5).implies(all(tat_none.implies(t3), not(all(t7.implies(t5), check_and_modify_at_arrived_at.atMost(tat).implies(t5), any(t10, t12))))))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const gcraStateInvariants = [gcraStateRule.law("tat: a None one holds 0", ({tat, tat_none}) => any(tat_none.not(), tat.eq(0)))]
