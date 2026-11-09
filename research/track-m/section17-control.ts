// Installed only into disposable copies. No change to the production modules.
import {appendFileSync} from 'node:fs'
import {type Machine,type Law} from '../../core/machine.ts'
import {countedObligations} from '../../kernel/kernel.ts'
import {clock,fullRate,fullWork,withWall} from '../../kernel/prove.ts'
import {t12} from './section15-control.ts'
import {goalSize,proportionalDraw} from './section17-budget.ts'
const mode=process.env.TRACK_M_POOL_MODE??'baseline',file=process.env.TRACK_M_POOL_LOG
let startWall=0,startUnits=0,duration=0,serial=0,current:{law:string,size:number,totalSize:number,unitEnd:number,wallEnd:number}|undefined
let sizes=new WeakMap<Law[],Map<Law,number>>()
const units=()=>fullWork()/fullRate
const emit=(event:string,data:any={})=>{if(file)appendFileSync(file,JSON.stringify({event,mode,wall:performance.now(),units:units(),...data})+'\n')}
export const poolControl={
 get enabled(){return mode!=='baseline'},
 protocol<T>(ms:number,run:()=>T):T{
  startWall=performance.now();startUnits=units();duration=ms;serial=0;current=undefined;sizes=new WeakMap()
  Object.assign(t12,{cap:mode==='combo',classes:mode==='combo',modelFirst:mode==='combo'})
  emit('protocol-start',{duration,startWall,startUnits})
  try{return this.enabled?withWall(startWall+duration,run):run()}finally{emit('protocol-end',{wallMs:performance.now()-startWall,usedUnits:units()-startUnits})}
 },
 countedEnd(end:number){return this.enabled?Math.min(end,startUnits+duration):end},
 available(end:number){return Math.max(0,Math.min(end-clock(),startUnits+duration-units(),startWall+duration-performance.now()))},
 generated(m:Machine,laws:Law[]){emit('generated',{laws,counts:m.counts})},
 lease(m:Machine,context:Law[],law:Law,pending:Law[],end:number){
  let memo=sizes.get(context);if(!memo){memo=new Map();sizes.set(context,memo)}
  const weight=(l:Law)=>{let n=memo!.get(l);if(n===undefined){n=Math.max(1,goalSize(countedObligations(m,context,{[l.name]:{}},context.indexOf(l)).map(p=>p.goal.hyps)));memo!.set(l,n)}return n}
  const unique=[...new Set(pending)],size=weight(law),totalSize=unique.reduce((n,l)=>n+weight(l),0),remaining=this.available(end),grant=proportionalDraw(remaining,size,totalSize)
  current={law:law.name,size,totalSize,unitEnd:clock()+grant,wallEnd:performance.now()+grant}
  emit('law-draw',{law:law.name,size,totalSize,remaining,grant,unitEnd:current.unitEnd,wallEnd:current.wallEnd,pending:unique.map(l=>l.name)})
  return {allotted:grant,stop:current.unitEnd,wall:current.wallEnd}
 },
 fallbackEnd(end:number,now=clock()){
  if(!this.enabled)return end
  const remaining=this.available(Math.min(end,current?.unitEnd??end)),draw=proportionalDraw(remaining,current?.size??1,current?.totalSize??1)
  emit('fallback-draw',{law:current?.law,remaining,draw,callerEnd:end})
  return Math.min(end,now+draw)
 },
 attemptStart(law:Law,context:Law[],pass:number,allotted:number){const token={id:++serial,wall:performance.now(),units:units()};emit('attempt-start',{...token,law:law.name,pass,allotted,context:context.map(l=>l.name)});return token},
 attemptEnd(token:{id:number,wall:number,units:number},law:Law,pass:number,result:any){emit('attempt-end',{id:token.id,law:law.name,pass,outcome:result&&'proof'in result?'proof':'unknown',stuck:result?.stuck,wallMs:performance.now()-token.wall,usedUnits:units()-token.units})},
 accepted(laws:Law[]){emit('checked-family',{laws:laws.map(l=>l.name)})},
}
