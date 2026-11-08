import {supportBudget} from '../support-budget.ts'
/** One draw from the still-unspent goal allowance. Split children receive the
 * same absolute deadline; the second spends only what the first leaves. */
export const leafAllowance=(remaining:number,leavesLeft:number):number=>supportBudget(remaining,remaining/Math.max(1,leavesLeft),true)
