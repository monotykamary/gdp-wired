// Global research stop, independent of the disabled internal deadlines.
import {costs} from '../../core/solver.ts'
import {fullRate,fullWork} from '../../kernel/prove.ts'
import {realNow,withoutDeadlines} from './without-deadlines.ts'
export class ResearchStop extends Error{constructor(public reason:'counted-cap'|'wall-cap'){super(reason)}}
export function boundedResearch<T>(units:number,wallMs:number,run:()=>T,progress:(r:{units:number,wallMs:number})=>void=()=>{}):T{
 if(!(units>0&&wallMs>0))throw new Error('positive research limits required')
 const object=costs as Record<string,number>,keys=Object.keys(object),descriptors=Object.getOwnPropertyDescriptors(object),values={...object},weights:Record<string,number>={}
 // Derive weights from the unchanged meter, before installing interceptors.
 const base=fullWork();for(const key of keys){const old=object[key]!;object[key]=old+1;weights[key]=fullWork()-base;object[key]=old}
 const start=realNow();let estimate=0,ticks=0,last=0,stop:ResearchStop|undefined
 const observe=()=>{const now=realNow(),spent=(fullWork()-base)/fullRate;if(now-last>=1000||spent>=units){last=now;progress({units:spent,wallMs:now-start})}if(spent>=units)stop??=new ResearchStop('counted-cap');if(now-start>=wallMs)stop??=new ResearchStop('wall-cap');if(stop)throw stop}
 try{
  for(const key of keys)Object.defineProperty(object,key,{configurable:true,enumerable:true,get:()=>values[key],set:(value:number)=>{estimate+=(value-values[key]!)*weights[key]!;values[key]=value;if(++ticks%256===0||estimate>=units*fullRate)observe()}})
  return withoutDeadlines(run)
 }finally{
  for(const key of keys)Object.defineProperty(object,key,{...descriptors[key]!,value:values[key]})
 }
}
