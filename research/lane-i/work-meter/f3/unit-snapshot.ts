import {meterKeys,type Raw} from '../calibration/contract.ts'
export {meterKeys}
// Single-writer, monotone raw counters, atomically published as exact integers.
// A global seqlock starves under continuous zero-priced writes. Independent
// atomic loads cannot decrease any component: equal nonnegative weighted scans
// establish no observed unit progress without requiring a simultaneous raw scan.
// Reset, invalid input or publication rollover permanently invalidates the run.
export const unitSnapshotBytes=16+meterKeys.length*8
export type UnitSnapshot={valid:boolean,sequence:number,raw:Raw,units:number,flags:number}
export function createUnitPublisher(buffer:SharedArrayBuffer,initial:Raw){
 if(buffer.byteLength!==unitSnapshotBytes)throw Error('unit snapshot buffer size')
 const control=new Int32Array(buffer,0,4),values=new BigUint64Array(buffer,16,meterKeys.length),last=meterKeys.map(()=>0)
 const publish=(key:typeof meterKeys[number],value:number)=>{
  const i=meterKeys.indexOf(key)
  if(i<0||!Number.isSafeInteger(value)||value<0||value<last[i]!){Atomics.store(control,2,1);return}
  if(Atomics.load(control,0)>=2_000_000_000)Atomics.store(control,2,1)
  last[i]=value;Atomics.store(values,i,BigInt(value));Atomics.add(control,0,1)
 }
 for(const key of meterKeys)publish(key,initial[key])
 return {publish,control}
}
export function readUnitSnapshot(buffer:SharedArrayBuffer,weights:readonly number[]):UnitSnapshot{
 if(buffer.byteLength!==unitSnapshotBytes||weights.length!==meterKeys.length||weights.some(w=>!Number.isFinite(w)||w<0))throw Error('explicit finite unit weights required')
 const control=new Int32Array(buffer,0,4),values=new BigUint64Array(buffer,16,meterKeys.length),copy=meterKeys.map((_,i)=>Number(Atomics.load(values,i)))
 const sequence=Atomics.load(control,0),flags=Atomics.load(control,2)
 let units=0;for(let i=0;i<weights.length;i++)units+=weights[i]!*copy[i]!
 return {valid:sequence>=0&&flags===0&&copy.every(Number.isSafeInteger)&&Number.isFinite(units),sequence,raw:Object.fromEntries(meterKeys.map((key,i)=>[key,copy[i]!])) as Raw,units,flags}
}
export function observeUnitProgress(previous:UnitSnapshot,next:UnitSnapshot){
 return {eligible:previous.valid&&next.valid,advanced:previous.valid&&next.valid&&next.units>previous.units,
  unchanged:previous.valid&&next.valid&&next.units===previous.units}
}
