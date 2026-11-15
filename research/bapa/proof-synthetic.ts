// Deterministic synthetic data for controls. No grow/prover/search is called.
import {n,atMost,less,plus,times,x,type Machine,type Law} from '../../core/machine.ts'
import {type Tree,type Goal,type Path,type CountCert,type MonoCut,type LinCut,obligations,countedObligations,leafConstraints,mcGoal,framePath,canon} from '../../kernel/kernel.ts'
import type {FamilyBundle} from './proof-capture.ts'
const contradiction=(g:Goal,path:Path):Tree=>{
 const rows=leafConstraints(g,path),index=rows.findIndex(r=>Object.keys(r.lin).every(k=>k==='1')&&(r.lin['1']??0)>0)
 if(index<0)throw Error('synthetic constant contradiction absent')
 return {leaf:[{kind:'input',index}]}
}
export function syntheticPlain(){
 const machine:Machine={name:'synthetic',params:[],inputs:[],state:{s:n(0)},step:{state:{s:x('s')}}},laws:Law[]=[{name:'true law',holds:atMost(n(0),n(0))}]
 const proof={instances:{},trees:Object.fromEntries(obligations(machine,laws).map(g=>[g.name,contradiction(g,new Map())]))}
 return {machine,laws,proof}
}
export function syntheticCounted(withFrame:boolean,auxiliary:'none'|'mono'|'lin'|'both'='none'):Pick<FamilyBundle,'original'|'final'> {
 const p=syntheticPlain(),machine:Machine={...p.machine,counts:{empty:{j:'j',key:'n',below:n(0),body:n(0)}}}
 const laws=auxiliary==='none'?p.laws:[...p.laws,{...p.laws[0]!,name:'other true law'}],certs:Record<string,CountCert>={}
 for(const {goal,decls}of countedObligations(machine,laws)){
  const map=decls[0]!.map,frames=withFrame?[{when:[],post:'c1',pre:'c0'}]:[]
  // Empty-domain equal-zero counts make these tiny positive format/bridge
  // controls, not evidence about a real protocol's useful per-key inequality.
  const below=less(x('n'),n(0)),zero=n(0),weightedZero=plus(times(1,zero),zero)
  const monos:MonoCut[]=auxiliary==='mono'||auxiliary==='both'?[{when:[],post:'c1',pre:'c0',tree:contradiction({name:'per-key cut',hyps:[below,less(zero,zero)]},new Map())}]:[]
  const lins:LinCut[]=auxiliary==='lin'||auxiliary==='both'?[{when:[],pos:[[1,'c1']],neg:[[1,'c0']],tree:contradiction({name:'linear cut',hyps:[below,less(weightedZero,weightedZero)]},new Map())}]:[]
  const needsReads=withFrame||auxiliary!=='none'
  const partial={reads:needsReads?([['c0',map,n(0)],['c1',map,n(0)]] as CountCert['reads']):[],insts:[],frames,monos,lins}
  const g=mcGoal(goal.hyps,decls,partial);if(!g)throw Error('synthetic counted goal absent')
  const split={s:1},key=canon(split)
  const tree:Tree={split,yes:contradiction(g,framePath(frames,[],new Map([[key,{lin:split,holds:true}]]),monos,lins)),no:contradiction(g,framePath(frames,[],new Map([[key,{lin:split,holds:false}]]),monos,lins))}
  certs[goal.name]={...partial,tree}
 }
 return {original:{machine,laws},final:{phase:'closed-family',checked:true,machine,laws,proof:{instances:{},certs}}}
}
