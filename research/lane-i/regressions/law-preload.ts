// Observe full names and genuine-model flags without emitting witness objects.
import {resolve as resolveLawPath} from 'node:path'
const {countsDump:lawDump}=await import(resolveLawPath('core/counts.ts'))
const priorLawObserver=lawDump.on
lawDump.on=(event:object)=>{
 priorLawObserver?.(event)
 if('phase'in event&&'law'in event&&typeof event.phase==='string'&&typeof event.law==='string'&&['finite-model','count-completion','rejected proposal'].includes(event.phase)){
  const row=event as {phase:string,law:string,pass?:number,completion?:{genuine?:boolean}}
  console.error('LANE_I_LAW '+JSON.stringify({phase:row.phase,law:row.law,pass:row.pass,genuine:row.completion?.genuine,at:performance.now()}))
 }
}
