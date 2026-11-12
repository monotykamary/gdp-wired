// Optional observation only. No cache, solver, fuel or proof authority.
export type ReplayDiagnosticContext=Readonly<{passId?:number,closingAttempt?:number,member?:string,obligation?:string,route?:string,repairUsed?:boolean}>
export type ReplayDiagnosticEvent=Readonly<{kind:string,context?:ReplayDiagnosticContext,[key:string]:unknown}>
export const countReplayDiagnostic:{on?: (event:ReplayDiagnosticEvent)=>void,observerFailures:number}={observerFailures:0}
let current:ReplayDiagnosticContext={}
const passIds=new WeakMap<object,number>(),certificateIds=new WeakMap<object,number>();let nextPass=0,nextCertificate=0
export function replayCertificateId(certificate:object):number|undefined{
 if(!countReplayDiagnostic.on)return undefined
 let id=certificateIds.get(certificate);if(id===undefined){id=++nextCertificate;certificateIds.set(certificate,id)}return id
}
export function replayPassId(pass:object):number|undefined{
 if(!countReplayDiagnostic.on)return undefined
 let id=passIds.get(pass);if(id===undefined){id=++nextPass;passIds.set(pass,id)}return id
}
export function withReplayDiagnosticContext<T>(context:ReplayDiagnosticContext,run:()=>T):T{
 if(!countReplayDiagnostic.on)return run()
 const old=current;current={...old,...context};try{return run()}finally{current=old}
}
export function emitReplayDiagnostic(event:ReplayDiagnosticEvent):void{
 const observer=countReplayDiagnostic.on;if(!observer)return
 // Diagnostics cannot turn a proof refusal into success, renew any allowance,
 // or replace an original allocator exception with a serialization exception.
 try{observer({...event,context:{...current,...event.context}})}catch{countReplayDiagnostic.observerFailures++}
}
