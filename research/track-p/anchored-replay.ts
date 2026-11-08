// Research: anchor relevance at the actual negated POST, not the final count axiom.
import {readFileSync} from 'node:fs'
import {type Machine,type Law,type C} from '../../core/machine.ts'
import {relevantGoals} from '../../core/relevance.ts'
import {type Goal,type CountCert,checkMC,countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,grow,widen,withWall,withDeadline} from '../../kernel/prove.ts'
const dir=process.argv[2]!,mode=process.argv[3]!,data=JSON.parse(readFileSync(dir+'/production.json','utf8')) as {machine:Machine,laws:Law[]},pack=JSON.parse(readFileSync(dir+'/c11-wide.json','utf8')),m=data.machine,all=data.laws
const header=JSON.parse(readFileSync(dir+'/core-header.json','utf8')) as {coreNames:string[]}
const unique=(cs:C[])=>[...new Map(cs.map(c=>[JSON.stringify(c),c])).values()]
for(const item of pack){
 const laws=item.label==='core'?all.filter(l=>header.coreNames.includes(l.name)):all,target=laws.find(l=>l.name.includes('a < c, b ≠ d'))!,raw=countedObligations(m,laws,{[target.name]:item.instances},laws.indexOf(target)).at(-1)!,request=item.certificateRequest as CountCert,gg=mcGoal(raw.goal.hyps,raw.decls,request)!
 const neg=raw.goal.hyps.at(-1)!,negKey=JSON.stringify(neg),at=gg.hyps.findIndex(c=>JSON.stringify(c)===negKey),others=gg.hyps.filter((_,i)=>i!==at),aux=gg.hyps.slice(raw.goal.hyps.length),anchor:Goal={...gg,hyps:[...others,neg]},hint:C={op:'and',xs:[neg,...aux]},rankHint:Goal={...gg,hyps:[...others,hint]}
 const slices=mode==='full'?[gg]:mode==='wrong'?relevantGoals(gg):mode==='anchored'?relevantGoals(anchor):relevantGoals(rankHint).map(g=>({...g,hyps:unique([...g.hyps.slice(0,-1),...aux,neg])}))
 for(const [i,part]of slices.entries()){
  const begin=performance.now(),out=withWall(begin+2500,()=>counted(fullRate,()=>withDeadline(clock()+1500,()=>grow(part,new Map(),{nodes:0,until:clock()+1500})),true)),tree='tree'in out?widen(part,gg,out.tree):undefined,checked=!!tree&&checkMC(raw.goal.hyps,raw.decls,{...request,tree})
  console.log(JSON.stringify({context:item.label,mode,part:i,hyps:part.hyps.length,whole:gg.hyps.length,captured:item.hyps,negIndex:at,aux:aux.length,checked,status:'tree'in out?'tree':out.stuck,ms:performance.now()-begin}))
 }
}
