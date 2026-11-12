// Capture-local output reuse, not a checker or a new global cache. The legacy
// reference pass has already materialized these exact proposer rows. Preserve
// the subsequent native builder's work/order, but do not retain another full
// quadratic pair table. Kernel checking still calls its unchanged builder.
import {type Constraint,type Lin} from './solver.ts'
import {type Goal,type Path,canon,canonFlip,cellParts,facts,isCell,termRows} from '../kernel/kernel.ts'
import {observeTableCells} from './meter.ts'
import {admittedLinearCopy as rowCopy,admittedLinearAdd as rowAdd,admittedLinearScale as rowScale,admittedLinearSub as rowSub,admittedLinearVariable as rowVariable,visitLinearCells,fundedSub as sub,fundedScale as scale} from './linear-admission.ts'
import {workFilter,workMap,workSetArray} from './work-collections.ts'

// Keep the native sameKey/decide operations (including funded sub/scale and
// short-circuiting), not the differently metered proposer implementation.
function decide(lin:Lin,path:Path):boolean|undefined{
 observeTableCells()
 let constant=true
 for(const key in lin){observeTableCells(key.length+1);if(!Number.isSafeInteger(lin[key]))return undefined;if(key!=='1')constant=false}
 if(constant)return(lin['1']??0)<=0
 const direct=path.get(canon(lin))?.holds
 if(direct!==undefined)return direct
 const flipped=path.get(canonFlip(lin))?.holds
 return flipped===undefined?undefined:!flipped
}
function sameKey(p:ReturnType<typeof cellParts>,q:ReturnType<typeof cellParts>,path:Path):boolean{
 const zero=(a:Lin,b:Lin)=>{const d=sub(a,b);return decide(d,path)===true&&decide(scale(d,-1),path)===true}
 if(p.key&&q.key)return zero(p.key,q.key)
 return!!p.keys&&!!q.keys&&p.keys.length===q.keys.length&&p.keys.every((a,i)=>zero(a,q.keys![i]!))
}

// The work-only counterpart of kernel leafRows(..., h => facts(h,path)). Only
// atom/fact rows must coexist to discover names. Generated pair/term/nat rows
// still perform every original funded coefficient operation at its original
// position; their output is discarded immediately instead of being appended.
// This intentionally saves storage, NOT quadratic arithmetic/counting work.
export function reuseNativeScopeRows(goal:Goal,path:Path,rows:Constraint[]):Constraint[]{
 const initial:Constraint[]=[];let atom=0,count=0
 for(const a of path.values()){
  const lin=a.holds?rowCopy(a.lin,'leafRows:atom-copy'):rowAdd(rowVariable('1',1,'leafRows:atom-one'),rowScale(a.lin,-1,'leafRows:atom-negate'),'leafRows:atom-flip')
  initial.push({lin,label:'',src:{atom:atom++}});count++
 }
 for(const[i,h]of goal.hyps.entries())for(const lin of facts(h,path)){initial.push({lin:rowCopy(lin,'leafRows:fact'),label:'',src:{fact:i}});count++}
 const names=new Set<string>()
 for(const row of initial)visitLinearCells(row.lin,key=>{if(key!=='1')names.add(key)},'leafRows:names')
 const cells=workMap(workFilter(workSetArray(names,'leafRows:names-copy'),isCell,'leafRows:cell-filter'),name=>({name,...cellParts(name)}),'leafRows:cell-parts')
 for(let i=0;i<cells.length;i++)for(let j=i+1;j<cells.length;j++){
  const p=cells[i]!,q=cells[j]!
  observeTableCells()
  if(p.map!==q.map)continue
  if(!sameKey(p,q,path))continue
  const pRow=rowVariable(p.name,1,'leafRows:pair-p'),qRow=rowVariable(q.name,1,'leafRows:pair-q')
  rowSub(pRow,qRow,'leafRows:pair-left');rowSub(qRow,pRow,'leafRows:pair-right');count+=2
 }
 const seen=new Set<string>(),todo=workFilter(workSetArray(names,'leafRows:todo-copy'),n=>n.startsWith('⟦'),'leafRows:todo-filter')
 while(todo.length){
  const name=todo.pop()!
  if(seen.has(name))continue
  seen.add(name)
  for(const lin of termRows(name,path)){
   rowCopy(lin,'leafRows:term');count++
   visitLinearCells(lin,key=>{if(key!=='1'){names.add(key);if(key.startsWith('⟦')&&!seen.has(key))todo.push(key)}},'leafRows:term-names')
  }
 }
 for(const name of names){rowVariable(name,-1,'leafRows:natural');count++}
 // Never use a partial/mismatched proposal to infer suppliers. This comparison
 // is intrinsic metadata, not a traversal or a certificate-acceptance shortcut.
 if(count!==rows.length)throw new Error('capture native/proposer row-count mismatch')
 return rows
}
