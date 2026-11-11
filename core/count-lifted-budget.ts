// W is the original enclosing CLOCK-unit allowance, not a remaining case share.
// Divide once: every local leaf uses W/120, every operation uses W/30, and
// both are clipped to the caller's absolute endpoint. Legacy search is exact.
import {completeWorkProfile} from './work-profile.ts'
import {type CountStrategyOptions,strategyLeafUnits} from './count-strategy.ts'
import {clock} from '../kernel/prove.ts'
import {countPrimitiveUnits} from './count-primitive-budget.ts'
export type LiftedWorkBudget=Readonly<{workAllowance:number,leafUnits:number,caseUnits:number,full:boolean}>
export function liftedWorkBudget(workAllowance:number,full=completeWorkProfile.enabled):LiftedWorkBudget{
 if(full&&(!Number.isFinite(workAllowance)||workAllowance<0))throw new RangeError('invalid lifted work allowance')
 return Object.freeze({workAllowance,leafUnits:full?strategyLeafUnits(workAllowance):500,caseUnits:full?workAllowance/30:2000,full})
}
export const liftedDeadline=(now:number,parent:number,units:number):number=>Math.min(parent,now+Math.max(0,units))
export function liftedLeafUntil(until:number,options:CountStrategyOptions,legacy=500):number{
 return liftedDeadline(clock(),until,countPrimitiveUnits(legacy,options.leafUnits))
}
export function liftedCaseUntil(until:number,budget:LiftedWorkBudget,frame=false):number{
 return liftedDeadline(clock(),until,countPrimitiveUnits(frame?500:2000,budget.caseUnits))
}
