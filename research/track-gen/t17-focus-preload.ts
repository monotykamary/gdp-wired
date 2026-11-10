// Observation only: the original harness owns all work and wall allowances.
import {resolve} from 'node:path'
const {cprof,countsDump}=await import(resolve('core/counts.ts'))
const error=console.error.bind(console),log=console.log.bind(console),prior=countsDump.on
countsDump.on=(event:object)=>{
 prior?.(event)
 if('phase'in event&&event.phase==='candidates'&&'laws'in event&&Array.isArray(event.laws))error('T17_PROFILE '+JSON.stringify({event:'candidate-names',names:event.laws.map((law:{name:string})=>law.name)}))
}
console.error=(...args:unknown[])=>{
 if(typeof args[0]==='string'&&args[0].startsWith('counts: candidates at '))error('T17_PROFILE '+JSON.stringify({event:'candidates',at:performance.now(),profile:{...cprof}}))
 error(...args)
}
console.log=(...args:unknown[])=>{
 if(typeof args[0]==='string'&&args[0].startsWith('{'))try{const row=JSON.parse(args[0]);if(row.id&&row.search)error('T17_PROFILE '+JSON.stringify({event:'result',at:performance.now(),searchMs:row.search.ms,profile:{...cprof}}))}catch{/* ordinary output */}
 log(...args)
}
