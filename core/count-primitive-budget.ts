// Historical subquery constants were tuned for the twelve-counter clock.
// Full accounting must reuse the already granted W/120 leaf allowance, not
// reinterpret 150/250/600 as full-work limits. Callers still clamp to the same
// absolute leaf/strategy/root end; this helper never grants another budget.
import {completeWorkProfile} from './work-profile.ts'
export function countPrimitiveUnits(legacyUnits:number,leafUnits?:number):number{
 return Math.max(0,completeWorkProfile.enabled?(leafUnits??legacyUnits):legacyUnits)
}
