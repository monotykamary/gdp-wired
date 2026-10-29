// rate limit/libtorrent/bandwidth_channel: extracted from libtorrent 2.1.2 (arvidn/libtorrent), src/bandwidth_limit.cpp and include/libtorrent/aux_/bandwidth_limit.hpp: libtorrent::aux::bandwidth_channel's throttle(int), update_quota, use_quota, return_quota, quota_left (libtorrent/assert.hpp stood in for: TORRENT_ASSERT as assert). BSD-3-Clause, (c) Arvid Norberg and contributors.
// Extracted by gdp-wired/extract from bandwidth_channel.cpp (bandwidth_channel, a class).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, int, Int, nat, not, oneOf, rule, when} from '../../../../core/dsl.ts'

export const bandwidth_channelRule = rule("bandwidth_channel")
  .inputs({method: oneOf('throttle', 'update_quota', 'use_quota', 'return_quota', 'quota_left'), throttle_limit: nat, update_quota_dt_milliseconds: nat, use_quota_amount: nat, return_quota_amount: nat})
  .state({distribute_quota: int.from(0), m_quota_left: int.from(0), m_limit: 0, quota_left_result: int.from(0)})
  .assume(({method, throttle_limit, update_quota_dt_milliseconds, m_limit, use_quota_amount, return_quota_amount, m_quota_left}) => all(method.is('throttle').implies(throttle_limit.atMost(2147483647)), method.is('throttle').implies(Int.of(throttle_limit).atLeast(-2147483648)), method.is('throttle').implies(throttle_limit.atLeast(0)), not(all(method.is('throttle'), throttle_limit.atLeast(0), throttle_limit.atLeast(2147483647))), method.is('update_quota').implies(update_quota_dt_milliseconds.atMost(2147483647)), method.is('update_quota').implies(Int.of(update_quota_dt_milliseconds).atLeast(-2147483648)), method.is('update_quota').implies(m_limit.atLeast(0)), not(all(method.is('update_quota'), m_limit.atLeast(0), m_limit.atLeast(2147483647))), method.is('use_quota').implies(use_quota_amount.atMost(2147483647)), method.is('use_quota').implies(Int.of(use_quota_amount).atLeast(-2147483648)), method.is('use_quota').implies(use_quota_amount.atLeast(0)), not(all(method.is('use_quota'), use_quota_amount.atLeast(0), m_limit.lt(0))), method.is('return_quota').implies(return_quota_amount.atMost(2147483647)), method.is('return_quota').implies(Int.of(return_quota_amount).atLeast(-2147483648)), method.is('return_quota').implies(return_quota_amount.atLeast(0)), not(all(method.is('return_quota'), return_quota_amount.atLeast(0), m_limit.eq(0).not(), m_quota_left.plus(return_quota_amount).lt(m_quota_left)))))
  .step(({method, distribute_quota, m_limit, m_quota_left, update_quota_dt_milliseconds, use_quota_amount, return_quota_amount, throttle_limit}) => {
    const t1 = method.is('throttle')
    const t2 = method.is('update_quota')
    const t3 = m_limit.eq(0)
    const t4 = m_limit.mul(update_quota_dt_milliseconds).plus(500)
    const t5 = m_quota_left.plus(when(t4.atLeast(0), t4.divBy(1000), Int.of(t4).negate().divBy(1000).negate()))
    const t6 = when(Int.of(2147483647).minus(m_quota_left).lt(when(t4.atLeast(0), t4.divBy(1000), Int.of(t4).negate().divBy(1000).negate())), 2147483647, when(Int.of(m_limit).lt(when(t5.atLeast(0), t5.divBy(3), t5.negate().divBy(3).negate())), m_limit.times(3), t5).min(2147483647))
    const t7 = method.is('use_quota')
    const t8 = method.is('return_quota')
    return {distribute_quota: when(t1, distribute_quota, when(t2, when(t3, distribute_quota, t6.clamped), distribute_quota)), m_quota_left: when(t1, m_quota_left, when(t2, when(t3, m_quota_left, t6), when(t7, when(t3, m_quota_left, m_quota_left.minus(use_quota_amount)), when(t8, when(t3, m_quota_left, m_quota_left.plus(return_quota_amount)), m_quota_left)))), m_limit: when(t1, throttle_limit, m_limit), quota_left_result: when(t1, 0, when(t2, 0, when(t7, 0, when(t8, 0, when(method.is('quota_left'), when(t3, 2147483647, m_quota_left.minus(m_quota_left.plus(2147483648).divBy(4294967296).times(4294967296)).clamped), 0)))))}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const bandwidth_channelInvariants = [bandwidth_channelRule.law("distribute_quota within its type's range", ({distribute_quota}) => distribute_quota.atMost(2147483647).and(distribute_quota.atLeast(-2147483648))), bandwidth_channelRule.law("m_limit within its type's range", ({m_limit}) => m_limit.atMost(2147483647).and(m_limit.atLeast(0))), bandwidth_channelRule.law("quota_left_result within its type's range", ({quota_left_result}) => quota_left_result.atMost(2147483647).and(quota_left_result.atLeast(-2147483648)))]
