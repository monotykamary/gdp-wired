import {createUnitPublisher,meterKeys,unitSnapshotBytes} from './unit-snapshot.ts'
import type {Raw} from '../calibration/contract.ts'
// Exact 20-key source binding. No monkey-patching of clocks or budget functions.
export function installUnitPublisher(core:Record<string,number>,costs:Record<string,number>,epr:Record<string,number>){
 const entries=meterKeys.map((key,index)=>{
  const object=key==='epr'?epr:index<12||key==='cdclNodes'?costs:core,property=key==='epr'?'n':key
  const descriptor=Object.getOwnPropertyDescriptor(object,property)
  if(!descriptor?.configurable||!descriptor.writable||typeof descriptor.value!=='number')throw Error('unobservable raw counter '+key)
  return{key,object,property,descriptor,value:descriptor.value as number}
 })
 const initial=Object.fromEntries(entries.map(e=>[e.key,e.value])) as Raw,buffer=new SharedArrayBuffer(unitSnapshotBytes),publisher=createUnitPublisher(buffer,initial)
 for(const entry of entries)Object.defineProperty(entry.object,entry.property,{configurable:entry.descriptor.configurable,enumerable:entry.descriptor.enumerable,get:()=>entry.value,set:(value:number)=>{entry.value=value;publisher.publish(entry.key,value)}})
 let restored=false
 return{buffer,restore:()=>{if(restored)return;restored=true;for(const entry of entries)Object.defineProperty(entry.object,entry.property,{...entry.descriptor,value:entry.value})}}
}
