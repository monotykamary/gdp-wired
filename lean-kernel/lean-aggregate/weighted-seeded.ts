import {type C,type E,n,same,x} from '../../core/machine.ts'
import {type Goal,type Instances,type Path,type Tree,checkLaws,obligations,sumParts} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {countGuardTree} from '../../core/count-guard-tree.ts'
import type {WeightedCandidate} from './weighted.ts'

// Propose ∀-instances only at the address the weighted summary actually
// subtracts and the preservation goal's own row. Every branch tree is an
// ordinary proof of the original goal (no changed hypothesis list).
export function proveWeightedSeeded(c:WeightedCandidate,ms:number,observe:(x:object)=>void){
  const {machine,laws,links}=c
  const p=laws.find(l=>l.forall)
  if(!p?.forall)return {proven:false,checked:false,failed:{why:'no pointwise helper'}}
  const probe=x(`${p.forall}#`)
  const point=links.point
  const touched:E[]=[point,...(point.op==='if'?[point.then,point.else]:[])]
  const sum=Object.keys(machine.sums??{})[0]!
  const q=`?${sumParts(sum).flag}`
  const closed=Object.entries(machine.step.flags??{}).flatMap(([name,c])=>c.op==='all'?[name]:[])
  const instances:Record<string,Instances>=Object.fromEntries(laws.map(l=>[l.name,{...Object.fromEntries(closed.map(f=>['?'+f,[n(0)]])),[p.name]:l===p?[...touched,probe]:[point],[q]:l===p?[probe]:[] }]))
  const until=clock()+ms, trees:Record<string,Tree>={}
  const goals=obligations(machine,laws,instances)
  // Try agreement first so a large pointwise relation cannot starve it.
  const i=laws.findIndex(({holds:c})=>(c.op==='='||c.op==='<=')&&[c.a,c.b].some(e=>e.op==='var'&&e.name===sum))
  if(i>=0)goals.unshift(...goals.splice(2*i,2))
  for(const goal of goals){
    if(clock()>=until)return {proven:false,checked:false,failed:{goal:goal.name,why:'budget'}}
    const addressConditions:C[]=goal.name.endsWith('@step')?(point.op==='if'?[point.c]:[]):[]
    if(goal.name===`${p.name} @step`)addressConditions.push(same(probe,point))
    if(goal.name.endsWith('@step')) for(const f of links.events.filter(f=>closed.includes(f))) addressConditions.push({op:'<=',a:x('?'+f),b:n(0)})
    const one=(g:Goal,path:Path,ms:number)=>{
      const found=grow(g,path,{nodes:0,until:Math.min(until,clock()+ms)})
      return 'tree'in found ? found.tree : undefined
    }
    const quick=one(goal,new Map(),goal.name.endsWith('@start')?1000:closed.length?1200:3500)
    const split=countGuardTree(until,{yesFirst:true})
    const branch=(at:number,path:Path):Tree|undefined => {
      if(at===addressConditions.length){
        const proof=one(goal,path,Math.min(closed.length?6000:8000,until-clock()))
        if(!proof&&closed.length)observe({goal:goal.name,phase:'leaf',path:[...path.values()].slice(-12)})
        return proof
      }
      if(closed.length && at>0){ const dead=one(goal,path,70); if(dead)return dead }
      const next=(p:Path)=>branch(at+1,p)
      return split.condition(addressConditions[at]!,path,next,next)
    }
    const tree=quick ?? branch(0,new Map())
    observe({goal:goal.name,checkedHere:!!tree,remaining:Math.round(until-clock())})
    if(!tree)return {proven:false,checked:false,failed:{goal:goal.name,why:'write-key instances and guard splitting did not close'}}
    trees[goal.name]=tree
  }
  const proof={instances,trees}, checked=checkLaws(machine,laws,proof)
  return {proven:checked,checked,proof,failed:checked?undefined:{why:'whole-family kernel refused'}}
}
