// Untrusted, cancellable row proposal. The checker always rebuilds its own rows
// with kernel/leafConstraints; these rows are never proof authority.
import {type C} from './machine.ts'
import {type Constraint,type Lin} from './solver.ts'
import {observeTableCells} from './meter.ts'
import {admittedLinearCopy as rowCopy,admittedLinearSub as rowSub,admittedLinearScale as rowScale,admittedLinearAdd as rowAdd,admittedLinearVariable as rowVariable,visitLinearCells} from './linear-admission.ts'
import {checkWorkEndpoint} from './wall.ts'
import {withTableAdmission} from './table-admission.ts'
import {workFlatMap,workFilter,workMap,workSetArray} from './work-collections.ts'
import {type Goal,type Path,type Seen,canon,canonFlip,cellParts,facts,isCell,reusing,termRows,truth} from '../kernel/kernel.ts'
const seenFacts=new WeakMap<Goal,Map<C,Seen<Lin[]>>>()
function proposedFacts(c:C,path:Path,positive=true):Lin[]{
 checkWorkEndpoint('row hypothesis')
 if(c.op==='not')return proposedFacts(c.x,path,!positive)
 if(c.op==='and'||c.op==='or'){
  if((c.op==='and')===positive)return workFlatMap(c.xs,y=>proposedFacts(y,path,positive),'proposedFacts:conjunction')
  const open=workFilter(c.xs,y=>{checkWorkEndpoint('row disjunction');return truth(y,path)!==!positive},'proposedFacts:disjunction')
  return open.length===0?[rowVariable('1',1,'proposedFacts:false')]:open.length===1?proposedFacts(open[0]!,path,positive):[]
 }
 return facts(c,path,positive)
}
// Same integer-path comparison as the reference row builder, outside its
// private memo state. This only proposes rows; their use is checked later.
function decided(lin:Lin,path:Path):boolean|undefined{
 checkWorkEndpoint('row key comparison')
 observeTableCells();let constant=true
 for(const key in lin){checkWorkEndpoint('row key coefficient');observeTableCells(key.length+1);if(!Number.isSafeInteger(lin[key]))return undefined;if(key!=='1')constant=false}
 if(constant)return(lin['1']??0)<=0
 const direct=path.get(canon(lin))?.holds
 if(direct!==undefined)return direct
 const flipped=path.get(canonFlip(lin))?.holds
 return flipped===undefined?undefined:!flipped
}
function sameKey(p:ReturnType<typeof cellParts>,q:ReturnType<typeof cellParts>,path:Path):boolean{
 const zero=(a:Lin,b:Lin)=>{const d=rowSub(a,b,'row-key:subtract');return decided(d,path)===true&&decided(rowScale(d,-1,'row-key:flip'),path)===true}
 if(p.key&&q.key)return zero(p.key,q.key)
 return!!p.keys&&!!q.keys&&p.keys.length===q.keys.length&&p.keys.every((a,i)=>zero(a,q.keys![i]!))
}
export function budgetedLeafRows(goal:Goal,path:Path):Constraint[]{
 return withTableAdmission(()=>budgetedLeafRowsIn(goal,path))
}
function budgetedLeafRowsIn(goal:Goal,path:Path):Constraint[]{
 let byHyp=seenFacts.get(goal);if(!byHyp)seenFacts.set(goal,(byHyp=new Map()))
 const rows:Constraint[]=[]
 // Own the coefficient plan and start each output before materializing it.
 // Failed discovery/emission stays charged; no completed-row post-observer.
 const put=(row:Constraint)=>{checkWorkEndpoint('row append');rows.push({...row,lin:rowCopy(row.lin,'proposedRows:copy')});checkWorkEndpoint('row appended')}
 let atom=0;for(const a of path.values())put({lin:a.holds?a.lin:rowAdd(rowVariable('1',1,'proposedRows:one'),rowScale(a.lin,-1,'proposedRows:negate'),'proposedRows:flip'),label:'',src:{atom:atom++}})
 for(const[i,h]of goal.hyps.entries()){
  checkWorkEndpoint('row hypothesis entry');let seen=byHyp.get(h);if(!seen)byHyp.set(h,(seen={}))
  for(const lin of reusing(seen,path,p=>proposedFacts(h,p)))put({lin,label:'',src:{fact:i}})
 }
 const names=new Set<string>();for(const row of rows)visitLinearCells(row.lin,key=>{if(key!=='1')names.add(key)},'proposedRows:names')
 const cells=workMap(workFilter(workSetArray(names,'proposedRows:names-copy'),isCell,'proposedRows:cell-filter'),name=>{checkWorkEndpoint('row cell');return{name,...cellParts(name)}},'proposedRows:cell-parts')
 for(let i=0;i<cells.length;i++)for(let j=i+1;j<cells.length;j++){
  const p=cells[i]!,q=cells[j]!
  checkWorkEndpoint('row cell pair');observeTableCells()
  if(p.map!==q.map||!sameKey(p,q,path))continue
  const pr=rowVariable(p.name,1,'proposedRows:pair-p'),qr=rowVariable(q.name,1,'proposedRows:pair-q')
  put({lin:rowSub(pr,qr,'proposedRows:pair-left'),label:'',src:{pair:[p.name,q.name]}});put({lin:rowSub(qr,pr,'proposedRows:pair-right'),label:'',src:{pair:[p.name,q.name]}})
 }
 const seen=new Set<string>(),todo=workFilter(workSetArray(names,'proposedRows:todo-copy'),n=>n.startsWith('⟦'),'proposedRows:todo-filter')
 while(todo.length){
  checkWorkEndpoint('row term');const name=todo.pop()!;if(seen.has(name))continue;seen.add(name)
  for(const lin of termRows(name,path)){put({lin,label:'',src:{term:name}});visitLinearCells(lin,key=>{if(key!=='1'){names.add(key);if(key.startsWith('⟦')&&!seen.has(key))todo.push(key)}},'proposedRows:term-names')}
 }
 for(const name of names)put({lin:rowVariable(name,-1,'proposedRows:natural'),label:'',src:{nat:name}})
 checkWorkEndpoint('row completion');return rows
}
