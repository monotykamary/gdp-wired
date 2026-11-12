// Frozen source48 reference collector, TEST ONLY. Do not import in production.
// Untrusted scope metadata, never a checker or a transport-success receipt.
// Preserve every legacy reference and retain root hypotheses supplying names
// to used native pair, term and naturality rows, including term-closure chains.
import {type CountCert,type Goal,type Path,type Tree,canon,framePath,leafConstraints} from '../../kernel/kernel.ts'
import {countedCertificateHyps} from '../../core/count-cert-transport.ts'
import {visitLinearCells} from '../../core/linear-admission.ts'
import {startWork} from '../../core/work-admission.ts'
import {checkWall} from '../../core/wall.ts'

const tick=(site:string):void=>{checkWall('counted scope row premises');startWork('ticks',1,site)}
function branch(path:Path,split:Extract<Tree,{split:unknown}>['split'],holds:boolean):Path{
 const out:Path=new Map()
 for(const [key,value]of path){tick('pair-scope:path-copy');out.set(key,value)}
 tick('pair-scope:path-branch');out.set(canon(split),{lin:split,holds});return out
}

export function referenceCountedScopeHyps(goal:Goal,cert:CountCert):Set<number>|undefined{
 tick('pair-scope:entry')
 const legacy=countedCertificateHyps(goal,cert)
 if(!legacy)return undefined
 const found=new Set<number>()
 for(const index of legacy){tick('pair-scope:legacy-reference');found.add(index)}
 const active=new WeakSet<object>()
 const leaf=(tree:Extract<Tree,{leaf:unknown}>,path:Path):boolean=>{
  // Reconstruct the actual native prefix; all cut kinds affect row indices.
  const actual=framePath(cert.frames??[],cert.lemmas??[],path,cert.monos??[],cert.lins??[])
  const rows=leafConstraints(goal,actual)
  const roots=new Map<string,Set<number>>(),parents=new Map<string,Set<string>>()
  // name -> introducing term. Walking these edges backwards lazily computes
  // the same union of root owners as forward propagation to a fixed point.
  for(let i=0;i<rows.length;i++){
   tick('row-scope:source-row');const row=rows[i]!,src=row.src
   if(!src)return false
   if('atom'in src||'fact'in src){
    if('fact'in src&&(!Number.isSafeInteger(src.fact)||src.fact<0||src.fact>=goal.hyps.length))return false
    visitLinearCells(row.lin,name=>{
     tick('row-scope:root-name');if(name==='1')return
     // Presence includes stored zero entries, exactly like native names.
     let owners=roots.get(name);if(!owners)roots.set(name,(owners=new Set()))
     if('fact'in src)owners.add(src.fact) // Path/cut atoms invent no fact owner.
    },'row-scope:root-cells')
   }else if('term'in src){
    visitLinearCells(row.lin,name=>{
     tick('row-scope:introduced-name');if(name==='1')return
     let origins=parents.get(name);if(!origins)parents.set(name,(origins=new Set()))
     origins.add(src.term)
    },'row-scope:term-cells')
   }else if(!('pair'in src||'nat'in src))return false
  }
  const todo:number[]=[],seen=new Set<number>(),names:string[]=[],seenNames=new Set<string>()
  const n=rows.length,squares=tree.squares?.length??0,products=tree.products??[]
  for(let i=0;i<tree.leaf.length;i++){tick('pair-scope:input-step');const step=tree.leaf[i]!;if(step.kind==='input')todo.push(step.index)}
  // The transporter reindexes all explicit products, even unread ones.
  for(let i=0;i<products.length;i++){tick('pair-scope:product-operands');const pair=products[i]!;todo.push(pair[0],pair[1])}
  while(todo.length){
   tick('pair-scope:referenced-row');const index=todo.pop()!
   if(!Number.isSafeInteger(index)||index<0||index>=n+squares+products.length)return false
   if(seen.has(index))continue;seen.add(index)
   if(index<n){
    const src=rows[index]!.src!
    if('fact'in src)found.add(src.fact)
    else if('pair'in src){
     for(const cell of src.pair){
      tick('pair-scope:pair-cell');if(!roots.has(cell))return false
      names.push(cell)
     }
    }else if('term'in src)names.push(src.term)
    else if('nat'in src)names.push(src.nat)
    else if(!('atom'in src))return false
   }else if(index>=n+squares){
    const pair=products[index-n-squares]!
    if(!pair||!Number.isSafeInteger(pair[0])||!Number.isSafeInteger(pair[1])||pair[0]<0||pair[1]<0||pair[0]>=index||pair[1]>=index)return false
    todo.push(pair[0],pair[1])
   }
   // A square is supplied by the certificate itself, not by hypothesis names.
   // Products inherit their operands, including nested products and squares.
  }
  while(names.length){
   tick('row-scope:dependency-name');const name=names.pop()!
   if(seenNames.has(name))continue;seenNames.add(name)
   if(!roots.has(name)&&!parents.has(name))return false
   for(const owner of roots.get(name)??[]){tick('row-scope:root-owner');found.add(owner)}
   // Follow the generating term even when its name cancelled out of the used
   // row. src.term, not a scan of only that row's coefficients, supplies it.
   for(const origin of parents.get(name)??[]){tick('row-scope:term-origin');names.push(origin)}
  }
  return true
 }
 const visit=(tree:Tree,path:Path):boolean=>{
  tick('pair-scope:tree');if(!tree||typeof tree!=='object'||active.has(tree))return false
  active.add(tree)
  try{return 'leaf'in tree?leaf(tree,path):visit(tree.yes,branch(path,tree.split,true))&&visit(tree.no,branch(path,tree.split,false))}
  finally{active.delete(tree)}
 }
 return visit(cert.tree,new Map())?found:undefined
}
