// Research-only synchronous override. No production module imports this file.
// Work still accumulates in fullWork(); never report clock() as measured work.
import {clock,counted} from '../../kernel/prove.ts'
export function withoutDeadlines<T>(run:()=>T):T{
 const prior=Object.getOwnPropertyDescriptor(performance,'now')
 Object.defineProperty(performance,'now',{configurable:true,value:()=>0})
 try{return counted(Infinity,()=>{if(clock()!==0)throw new Error('unlimited probe must start outside another counted scope');return run()},true)}
 finally{if(prior)Object.defineProperty(performance,'now',prior);else Reflect.deleteProperty(performance,'now')}
}
export const realNow=()=>Number(process.hrtime.bigint())/1e6
