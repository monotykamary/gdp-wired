// Untrusted R1 proposer: split the Boolean indicator atoms, not the action's
// expanded control flow. The ordinary linOk checker accepts or rejects the cut.
import {type C,type E,less,n,plus,times,x} from './machine.ts'
import {type Count,type Goal,type LinCut,type Path,type Tree,linOk} from '../kernel/kernel.ts'
import {fullRate,fullWork,late,rowsAt} from '../kernel/prove.ts'
import {solve} from './solver.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {traceNow} from './trace-clock.ts'
export function proveBooleanPartitionCut(counts:Count[],when:C[],terms:[number,string][],until:number,observe?:(event:Record<string,unknown>)=>void):{cut:LinCut}|undefined{
 const start=fullWork(),wall=observe?traceNow():0,used=terms.map(([,id])=>counts.find(count=>count.v===id))
 if(used.some(count=>!count))return
 const first=used[0]!;if(!first||used.some(count=>count!.key!==first.key||JSON.stringify(count!.below)!==JSON.stringify(first.below)))return
 const pos=terms.filter(([k])=>k>0),neg=terms.filter(([k])=>k<0).map(([k,id])=>[-k,id] as [number,string])
 const term=(side:[number,string][]):E=>side.reduce<E>((sum,[k,id])=>plus(sum,times(k,counts.find(count=>count.v===id)!.body)),n(0))
 const goal:Goal={name:'Boolean partition definition',hyps:[...when,less(x(first.key),first.below),less(term(neg),term(pos))]},atoms=new Map<string,C>()
 const visit=(c:C):void=>{if(c.op==='not')visit(c.x);else if(c.op==='and'||c.op==='or')c.xs.forEach(visit);else atoms.set(JSON.stringify(c),c)}
 for(const count of used){const body=count!.body;if(body.op!=='if'||body.then.op!=='const'||body.then.value!==1||body.else.op!=='const'||body.else.value!==0)return;visit(body.c)}
 if(atoms.size>8)return
 let leaves=0;const split=countGuardTree(until),list=[...atoms.values()]
 const build=(at:number,path:Path):Tree|undefined=>{
  if(late(until))return
  if(at<list.length)return split.condition(list[at]!,path,p=>build(at+1,p),p=>build(at+1,p))
  leaves++;const result=solve(rowsAt(goal,path),500)
  return result.kind==='refuted'?{leaf:result.steps}:undefined
 }
 const tree=build(0,new Map()),cut=tree?{when,pos,neg,tree}:undefined,checked=!!cut&&linOk(counts,cut)
 observe?.({stage:'boolean-partition-cut',checked,atoms:atoms.size,leaves,units:(fullWork()-start)/fullRate,wallMs:traceNow()-wall,...(!checked?{refusedCut:{kind:'linear',when,terms,counts:used}}:{})})
 return checked&&!late(until)?{cut:cut!}:undefined
}
