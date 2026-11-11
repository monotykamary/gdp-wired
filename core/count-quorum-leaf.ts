// The three-fact/four-split quorum leaf shared by row strategies. This is the
// arithmetic construction from count-leader.ts, with endpoint roles supplied.
// Facts must already be checked on the caller's path; no count axiom is added.
import {traceNow} from './trace-clock.ts'
import {type C,type E} from './machine.ts'
import {type Goal,type Path,type Tree,check,linear} from '../kernel/kernel.ts'
import {sub,solve} from './solver.ts'
import {clock,fullRate,fullWork,rowsAt,withDeadline} from '../kernel/prove.ts'
import {countGuardTree} from './count-guard-tree.ts'
import {rebasePath} from './count-rebase-path.ts'
export function proveQuorumCountLeaf(full:Goal,minimal:Goal,path:Path,pair:C,counts:{first:string,second:string},halves:readonly[E,E],until:number,observe?:(event:Record<string,unknown>)=>void,options:{deferCheck?:boolean}={}):Tree|undefined{
 if(pair.op!=='or'||pair.xs[0]?.op!=='not'||clock()>=until)return
 const clipped:E[]=[]
 const visit=(value:unknown):void=>{if(!value||typeof value!=='object')return;if(!Array.isArray(value)&&(value as E).op==='sub'&&!clipped.some(term=>JSON.stringify(term)===JSON.stringify(value)))clipped.push(value as E);for(const child of Array.isArray(value)?value:Object.values(value))visit(child)}
 visit(pair)
 if(clipped.length!==2)return
 const h=halves.map(half=>linear(half,path)),tails=clipped.map(term=>term.op==='sub'?{left:linear(term.a,path),right:linear(term.b,path)}:undefined)
 if(h.some(value=>!value)||tails.some(value=>!value?.left||!value.right))return
 const cuts=[sub({[counts.first]:1},h[0]!),sub({[counts.second]:1},h[1]!),...tails.map(tail=>sub(tail!.right!,tail!.left!))],split=countGuardTree(until)
 const close=(root:Path):Tree|undefined=>{
  const start=fullWork(),startWall=observe?traceNow():0,end=Math.min(until,clock()+500),rows=rowsAt(minimal,root),result=withDeadline(end,()=>solve(rows,2000)),tree:Tree|undefined=result.kind==='refuted'?{leaf:result.steps}:undefined,checked=!!tree&&(options.deferCheck||check(minimal,tree,root))&&clock()<end
  observe?.({stage:'quorum-linear-leaf',checked:!options.deferCheck&&checked,proposed:checked,units:(fullWork()-start)/fullRate,wallMs:traceNow()-startWall,rows:rows.length,outcome:result.kind,...(!checked?{query:minimal,path:[...root],result}:{})})
  return checked?tree:undefined
 }
 const choose=(at:number,root:Path):Tree|undefined=>at===cuts.length?close(root):split.rows([cuts[at]!],root,at<2?close:next=>choose(at+1,next),next=>choose(at+1,next))
 const disabled=pair.xs.slice(2),enter=(at:number,root:Path):Tree|undefined=>at===disabled.length?choose(0,root):split.condition(disabled[at]!,root,close,next=>enter(at+1,next))
 const tree=split.condition(pair.xs[0].x,path,root=>enter(0,root),close)
 if(!tree||clock()>=until)return
 const lifted=rebasePath(minimal,tree,path,path,until,full)
 return lifted&&(options.deferCheck||check(full,lifted,path))?lifted:undefined
}
