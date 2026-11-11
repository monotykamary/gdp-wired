// Passive operation brackets for qualification. No budget, flag, proof or verdict is supplied by this observer.
export type CountOperationEvent=Readonly<{phase:'begin'|'end',owner:string,value:number,kind:string,returned?:boolean}>
let observe:((event:CountOperationEvent)=>void)|undefined
export function withCountOperationObservation<T>(next:(event:CountOperationEvent)=>void,run:()=>T):T{const prior=observe;observe=next;try{return run()}finally{observe=prior}}
export function observeCountOperation<T>(identity:Omit<CountOperationEvent,'phase'|'returned'>,run:()=>T):T{
 if(!observe)return run()
 const notify=observe;notify({...identity,phase:'begin'});let returned=false
 try{const result=run();returned=result!==undefined;return result}finally{notify({...identity,phase:'end',returned})}
}
