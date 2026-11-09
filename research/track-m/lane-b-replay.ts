// Standalone, checked root-query experiment. No production budget or rule changes.
import {readFileSync} from 'node:fs'
import {check,type Goal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withDeadline,withWall,widen,atPoint,usedHyps} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
const [file,mode='default']=process.argv.slice(2),d=JSON.parse(readFileSync(file!,'utf8')),goal:Goal=d.goal,budget=2700
if(!['default','core','no-units'].includes(mode))throw Error('unknown replay mode')
const start=performance.now(),before=fullWork();let checked=false,used:number|undefined,verdict='unknown',error:string|undefined
try{counted(fullRate,()=>withWall(start+4800,()=>withDeadline(clock()+budget,()=>{
 const until=clock()+budget,path=new Map(),ask=()=>grow(goal,path,{nodes:0,until,...(mode==='no-units'?{units:false}:{})})
 let out:ReturnType<typeof grow>
 if(mode==='core'){
  const q=modelSequence()(goal,Math.min(until,clock()+200))
  if('tree'in q)out=q
  else if(q.why===REFUTED&&q.core?.length){const source={...goal,hyps:q.core.map(i=>goal.hyps[i]!)},r=grow(source,path,{nodes:0,until}),tree='tree'in r?widen(source,goal,r.tree):undefined;out=tree?{tree,nodes:0}:r}
  else out=ask()
 }else out=ask()
 verdict='tree'in out?'tree':out.stuck
 if('tree'in out){checked=check(goal,out.tree);used=usedHyps(goal,out.tree).size;if(!checked)throw Error('replay tree rejected')}
})),true)}catch(e){error=String(e)}
console.log(JSON.stringify({id:d.id,sources:d.sources,mode,budget,wallAllowance:4800,hyps:goal.hyps.length,verdict,checked,used,units:(fullWork()-before)/fullRate,wallMs:performance.now()-start,error,atPoint:atPoint.on}))
if(verdict==='tree'&&!checked)process.exitCode=1
