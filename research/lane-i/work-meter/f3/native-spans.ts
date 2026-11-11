// Diagnostic call boundaries, not raw work charges or native-instruction evidence.
// Slots 0/1 retain the existing running flag and raw heartbeat. Native span
// state occupies 4..8; odd sequence numbers are never valid observations.
const SEQ=4,ID=5,COUNT=6,DEPTH=7,OVERFLOW=8,MAX_CALLS=100_000_000
let shared:Int32Array|undefined
export const setNativeSpanBuffer=(value?:Int32Array)=>{if(value&&value.length<=OVERFLOW)throw Error('native span buffer needs nine slots');shared=value}
export type NativeSpan={valid:boolean,sequence:number,id:number,count:number,depth:number,overflow:boolean}
export function readNativeSpan(value:Int32Array):NativeSpan{
 const sequence=Atomics.load(value,SEQ),id=Atomics.load(value,ID),count=Atomics.load(value,COUNT),depth=Atomics.load(value,DEPTH),overflow=Atomics.load(value,OVERFLOW)!==0
 return {valid:!(sequence&1)&&sequence===Atomics.load(value,SEQ)&&!overflow,sequence,id,count,depth,overflow}
}
export const sameNativeSpan=(a:NativeSpan,b:NativeSpan)=>a.valid&&b.valid&&a.id>0&&a.id===b.id&&a.sequence===b.sequence&&a.count===b.count&&a.depth===b.depth
export function nativeSpan<T>(id:number,run:()=>T):T{
 const value=shared;if(!value||Atomics.load(value,OVERFLOW))return run()
 if(Atomics.load(value,COUNT)>=MAX_CALLS){Atomics.store(value,OVERFLOW,1);return run()}
 const previous=Atomics.load(value,ID),depth=Atomics.load(value,DEPTH)
 Atomics.add(value,SEQ,1);Atomics.add(value,COUNT,1);Atomics.store(value,ID,id);Atomics.store(value,DEPTH,depth+1);Atomics.add(value,SEQ,1)
 try{return run()}finally{Atomics.add(value,SEQ,1);Atomics.store(value,ID,previous);Atomics.store(value,DEPTH,depth);Atomics.add(value,SEQ,1)}
}
// Evaluate the receiver once, retrieve the method, then evaluate the arguments;
// all three precede the span. Native callbacks/GC remain inside the call span.
export function nativeMethod<T>(id:number,receiver:object,key:PropertyKey,args:()=>unknown[]):T{
 const method=Reflect.get(receiver,key),values=args()
 return nativeSpan(id,()=>Reflect.apply(method,receiver,values) as T)
}
