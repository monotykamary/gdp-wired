// Clock-derived search allowances are policy, not public native work quotas.
import {clock,fullRate,withBudget,withDeadline} from '../kernel/prove.ts'
import {inProxySearch} from './search-policy.ts'

export function withSearchAllowance<T>(until:number,run:()=>T,onNativeRefusal?:(error:unknown)=>T):T {
 // No local ledger endpoint exists here. An authentic enclosing refusal must
 // bypass every catch written to consume a native local-quota expiration.
 if(inProxySearch())return withDeadline(until,run)
 try{return withBudget(Math.max(0,until-clock())*fullRate,run)}
 catch(error){if(!onNativeRefusal)throw error;return onNativeRefusal(error)}
}
