// Section23 production relative screen. Only source-replayed ledger evidence
// can reject; tiny-Houdini's survivors and finite exhaustion are not proofs.
import {type Law,type Machine,type State} from './machine.ts'
import {finiteTinyHoudini} from './finite-houdini.ts'
import {createRejectionStage,type RejectionStage} from './rejection-stage.ts'
import {checkBudget,clock,fullRate,fullWork} from '../kernel/prove.ts'
import {countGenerationPhase} from './count-generation-phase.ts'
export type RejectionPhase={kind:string,used:number,complete:boolean}
export function rejectionStage(source:Machine,m:Machine,caller:readonly Law[],candidates:readonly Law[],allowance:number,options:{stage?:RejectionStage,phases?:RejectionPhase[]}={}){
 const stage=options.stage??createRejectionStage(source,m,caller,candidates,allowance),phases=options.phases??[]
 const until=clock()+allowance,started=fullWork(),params=Object.fromEntries(source.params.map(name=>[name,2]))
 let complete=false,previous:{params:Record<string,number>,pre:State,request:unknown}|undefined
 const dropped=new Map<number,number>()
 try{const run=countGenerationPhase(until,()=>{
  finiteTinyHoudini(source,m,[...caller],stage.active().filter(law=>!caller.includes(law)),[params],{
   valueDomain:[0,1],wallMs:Math.max(0,allowance),
   onDrop:drop=>{
    dropped.set(drop.round,(dropped.get(drop.round)??0)+1)
    // Every rejection still comes from one full-family source replay. Merely
    // finding another law false in the same shared transition adds no replay.
    if(previous?.params===drop.params&&previous.pre===drop.pre&&previous.request===drop.request)return
    previous={params:drop.params,pre:drop.pre,request:drop.request}
    stage.relative(drop.params,drop.pre,drop.request)
   },
   onTiny:(round,stats)=>{complete=stats.completed&&!stats.timedOut&&(dropped.get(round)??0)===0},
   onFinish:result=>{if(result.timedOut)complete=false},
  })
  checkBudget('relative screen completion')
 });if(!run.complete)complete=false
 }finally{phases.push({kind:'relative-two-server',used:(fullWork()-started)/fullRate,complete})}
 return {...stage,phases,screenWork:{used:(fullWork()-started)/fullRate,limit:allowance}}
}
