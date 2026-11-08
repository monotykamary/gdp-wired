// Receipt classification only; actual trees are rechecked separately in a fresh process.
import {canon} from '../../kernel/kernel.ts'
export function passesT10B(r:any):boolean{
 const a=r.attempt,n=r.numeric
 return r.instanceInViolatedSet===true&&r.modelValid===true&&r.sourceProjectionMatches===true
  &&a?.outcome==='checked'&&a.coreSize>0&&a.coreSize<=8&&a.queryCountedUnits<=30
  &&!!a.saved?.lemma?.when?.some((l:Record<string,number>)=>canon(l)===canon(r.guardAtom))
  &&n?.numericChecked===true&&n.conditionalChecked===true&&r.numericCore>0&&r.numericCore<=6
  &&n.queryCountedUnits<=20&&r.countedUnits<=120
}
