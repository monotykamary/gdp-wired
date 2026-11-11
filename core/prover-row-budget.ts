// Untrusted, cancellable row proposal. The checker always rebuilds its own rows
// with kernel/leafConstraints; these rows are never proof authority.
import {type C} from './machine.ts'
import {type Constraint,type Lin,k,scale,sub,v} from './solver.ts'
import {observeConstraintRows,observeTableCells} from './meter.ts'
import {checkWorkEndpoint} from './wall.ts'
import {type Goal,type Path,type Seen,atomOf,canon,canonFlip,cellParts,facts,isCell,reusing,termRows,truth} from '../kernel/kernel.ts'
const seenFacts=new WeakMap<Goal,Map<C,Seen<Lin[]>>>()
function proposedFacts(c:C,path:Path,positive=true):Lin[]{
 checkWorkEndpoint('row hypothesis')
 if(c.op==='not')return proposedFacts(c.x,path,!positive)
 if(c.op==='and'||c.op==='or'){
  if((c.op==='and')===positive)return c.xs.flatMap(y=>proposedFacts(y,path,positive))
  const open=c.xs.filter(y=>{checkWorkEndpoint('row disjunction');return truth(y,path)!==!positive})
  return open.length===0?[k(1)]:open.length===1?proposedFacts(open[0]!,path,positive):[]
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
 const zero=(a:Lin,b:Lin)=>{const d=sub(a,b);return decided(d,path)===true&&decided(scale(d,-1),path)===true}
 if(p.key&&q.key)return zero(p.key,q.key)
 return!!p.keys&&!!q.keys&&p.keys.length===q.keys.length&&p.keys.every((a,i)=>zero(a,q.keys![i]!))
}
export function budgetedLeafRows(goal:Goal,path:Path):Constraint[]{
 let byHyp=seenFacts.get(goal);if(!byHyp)seenFacts.set(goal,(byHyp=new Map()))
 const rows:Constraint[]=[]
 // Charge each completed row now: cancellation must not discard a batch's
 // pending observations, and a failed proposal never refunds completed work.
 const put=(row:Constraint)=>{checkWorkEndpoint('row append');rows.push(row);observeConstraintRows([row]);checkWorkEndpoint('row appended')}
 let atom=0;for(const a of path.values())put({...atomOf(a.lin,a.holds),src:{atom:atom++}})
 for(const[i,h]of goal.hyps.entries()){
  checkWorkEndpoint('row hypothesis entry');let seen=byHyp.get(h);if(!seen)byHyp.set(h,(seen={}))
  for(const lin of reusing(seen,path,p=>proposedFacts(h,p)))put({lin,label:'',src:{fact:i}})
 }
 const names=new Set(rows.flatMap(r=>Object.keys(r.lin).filter(key=>key!=='1')))
 const cells=[...names].filter(isCell).map(name=>{checkWorkEndpoint('row cell');return{name,...cellParts(name)}})
 for(const[i,p]of cells.entries())for(const q of cells.slice(i+1)){
  checkWorkEndpoint('row cell pair');observeTableCells()
  if(p.map!==q.map||!sameKey(p,q,path))continue
  put({lin:sub(v(p.name),v(q.name)),label:'',src:{pair:[p.name,q.name]}});put({lin:sub(v(q.name),v(p.name)),label:'',src:{pair:[p.name,q.name]}})
 }
 const seen=new Set<string>(),todo=[...names].filter(n=>n.startsWith('⟦'))
 while(todo.length){
  checkWorkEndpoint('row term');const name=todo.pop()!;if(seen.has(name))continue;seen.add(name)
  for(const lin of termRows(name,path)){put({lin,label:'',src:{term:name}});for(const key of Object.keys(lin))if(key!=='1'){names.add(key);if(key.startsWith('⟦')&&!seen.has(key))todo.push(key)}}
 }
 for(const name of names)put({lin:{[name]:-1},label:'',src:{nat:name}})
 checkWorkEndpoint('row completion');return rows
}
