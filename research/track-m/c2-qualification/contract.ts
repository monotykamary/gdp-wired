// T309 consumer contract only. No meter implementation, numeric fallback, or allocation authority.
export type ExactRaw=Readonly<{numerator:string,denominator:string}>
export type WorkAmount=Readonly<{num:bigint,den:bigint}>
export type Endpoint=Readonly<{id:number,kind:'root'|'scope'|'work-cap'|'deadline',end:ExactRaw}>
export type Snapshot=Readonly<{version:'strict-work-v1',rootEpoch:number,scopeEpoch:number,counterEpoch:number,actual:ExactRaw,reserved:ExactRaw,effectiveEnd:ExactRaw|null,activeEndpoints:readonly Endpoint[],weights:Readonly<Record<string,ExactRaw>>,counters:Readonly<Record<string,string>>,rootBaseline:Readonly<{actual:ExactRaw,counters:Readonly<Record<string,string>>}>|null}>
export type LeaseEvent=Snapshot&Readonly<{sequence:number,kind:'trace-start'|'trace-end'|'reserve'|'start'|'release'|'invalidate'|'refuse'|'scope-enter'|'scope-exit',sink?:string,site?:string,requested?:string,granted?:string,leaseId?:number}>
export interface MeterBinding{workLedger:{withBudget<T>(grant:WorkAmount,run:()=>T):T};workAdmissionSnapshot():Snapshot;withWorkAdmissionTrace<T>(observe:(event:LeaseEvent)=>void,run:()=>T):T}
export type Status='PASS'|'FAIL'|'UNKNOWN'|'NOT_RUN'
export type Verdict=Readonly<{status:Status,reason:string}>
export type LawIdentity=Readonly<{name:string,sha256:string}>
export type Manifest=Readonly<{version:'c2-production-gates-v1',candidate:{commit:string,tree:string,sourceClosureSha256:string},flags:Readonly<Record<string,string>>,protocolId:string,searchWorkRaw:string,wallMs:number,rootGrant:ExactRaw,workKeys:readonly string[],weightsSha256:string,originalMachineSha256:string,candidateRoster:readonly LawIdentity[],closedRoster:readonly LawIdentity[],exclusions:readonly Readonly<{law:LawIdentity,status:'excluded'|'unknown'|'refuted',reason:string}>[],halfLaw:LawIdentity,operations:readonly Readonly<{value:number,kind:string}>[],authorization:Readonly<{status:'NOT_RUN'|'GO',releaseSha256:string|null}>}>
export type OperationObservation=Readonly<{phase:'begin'|'end',owner:string,value:number,kind:string,returned?:boolean}>
export type CaseAttempt={identity:OperationObservation,start:Snapshot,end?:Snapshot,events:LeaseEvent[],returned?:boolean,slice?:Readonly<{kind:'case',key:string,allocation:ExactRaw,scopeId:number,rootEpoch:number}>}
export const missingMeter:MeterBinding={workLedger:{withBudget(){throw Error('NOT_RUN: T309 meter binding is absent')}},workAdmissionSnapshot(){throw Error('NOT_RUN: T309 meter binding is absent')},withWorkAdmissionTrace(){throw Error('NOT_RUN: T309 meter binding is absent')}}
