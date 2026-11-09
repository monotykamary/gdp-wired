// Research-only comparison of original and independently reconstructed families.
import {readFileSync} from 'node:fs'
import {mldr} from '../protocols/ic3syn/mldr.ts'
import {type Law,type Machine,type State,type Request,interpret} from '../../core/machine.ts'
import {finiteEvaluator,finiteTinyHoudini} from '../../core/finite-houdini.ts'
import {withWall} from '../../kernel/prove.ts'
import {checkWall} from '../../core/wall.ts'
const mode=process.argv[2]??'original', capture=JSON.parse(readFileSync('tiny-data/0.json','utf8')), data=capture.beforeFinite
const source=mldr().machine,m=data.machine as Machine,caller=data.caller as Law[],params={size:3},run=interpret(source),evaluate=finiteEvaluator(m)
let candidates=data.candidates as Law[]
const extras:Law[]=[...m.facts??[],...(m.pre?[{name:'machine precondition',holds:m.pre}]:[])]
const historical:string[]=[]
if(mode==='survivors')withWall(performance.now()+5000,()=>{
  const rounds=[...new Set<number>(capture.finiteDrops.map((d:{round:number})=>d.round))].sort((a,b)=>a-b)
  for(const round of rounds){
    checkWall('historical round')
    const family=[...caller,...candidates,...extras],removed=new Set<string>()
    for(const d of capture.finiteDrops.filter((d:{round:number})=>d.round===round)){
      checkWall('historical replay')
      const pre:State={...d.pre,maps:Object.fromEntries(Object.entries(d.pre.maps as Record<string,[number,number][]>).map(([k,v])=>[k,new Map(v)]))}
      const request:Request=Object.fromEntries(Object.entries(d.request).map(([k,v])=>[k,Array.isArray(v)?new Map(v as [number,number][]):v])) as Request
      const law=candidates.find(l=>l.name===d.law.name)
      if(!law||!family.every(l=>evaluate(l,d.params,pre)===true)||evaluate(law,d.params,run.step(d.params,pre,request))!==false)throw Error('historical certification failed: '+String(d.law.name))
      removed.add(law.name);historical.push(law.name)
    }
    candidates=candidates.filter(l=>!removed.has(l.name))
  }
})
const initial=caller.length+candidates.length,drops:{stage:number,round:number,ms:number,law:string}[]=[],rounds:unknown[]=[],finishes:unknown[]=[]
const removed=new Set<Law>(),started=performance.now()
let timedOut=false
const postTargetPruning=process.env.T16_POST_TARGET==='1',postTargetIntervals=process.env.T16_POST_INTERVALS==='1'
try {
  withWall(started+1900,()=>{
    const stages=[{valueDomain:[0,1],rounds:2,wallMs:1000},{valueDomain:[0,1,2],rounds:1,wallMs:2000}]
    for(const [stage,options] of stages.entries()) {
      checkWall('hybrid stage')
      candidates=finiteTinyHoudini(source,m,caller,candidates,[params],{...options,postTargetPruning,postTargetIntervals,
        onDrop:drop=>{
          removed.add(drop.law)
          const row={stage,round:drop.round,ms:performance.now()-started,law:drop.law.name}
          drops.push(row)
          console.log('HYBRID_CTI',JSON.stringify({...row,pre:{scalars:drop.pre.scalars,maps:Object.fromEntries(Object.entries(drop.pre.maps).map(([k,v])=>[k,[...v]]))},request:Object.fromEntries(Object.entries(drop.request).map(([k,v])=>[k,v instanceof Map?[...v]:v]))}))
        },
        onTiny:(round,stats)=>rounds.push({stage,round,stats}),
        onFinish:finish=>finishes.push({stage,...finish})
      })
    }
  })
} catch(error) {
  if(!(error instanceof Error)||error.name!=='WallExpired')throw error
  checkWall('hybrid outer completion');timedOut=true
}
console.log('HYBRID_RESULT',JSON.stringify({mode,postTargetPruning,postTargetIntervals,initial,drops,rounds,finishes,timedOut,wall:performance.now()-started,removed:removed.size,survivors:initial-removed.size}))
