// Untrusted scope metadata, never a checker or a proof of successful transport.
// Preserve every legacy reference, then add the hypotheses which make a used
// equal-key pair row available in the native leaf's pre-closure name set.
import {type CountCert,type Goal,type Path,type Tree,canon,framePath,isCell,leafConstraints} from '../kernel/kernel.ts'
import {countedCertificateHyps} from './count-cert-transport.ts'
import {visitLinearCells} from './linear-admission.ts'
import {startWork} from './work-admission.ts'
import {checkWall} from './wall.ts'

const tick=(site:string):void=>{checkWall('counted scope pair premises');startWork('ticks',1,site)}
function branch(path:Path,split:Extract<Tree,{split:unknown}>['split'],holds:boolean):Path{
 const out:Path=new Map()
 for(const [key,value]of path){tick('pair-scope:path-copy');out.set(key,value)}
 tick('pair-scope:path-branch');out.set(canon(split),{lin:split,holds});return out
}

export function countedScopeHyps(goal:Goal,cert:CountCert):Set<number>|undefined{
 tick('pair-scope:entry')
 const legacy=countedCertificateHyps(goal,cert)
 if(!legacy)return undefined
 const found=new Set<number>()
 for(const index of legacy){tick('pair-scope:legacy-reference');found.add(index)}
 const active=new WeakSet<object>()
 const leaf=(tree:Extract<Tree,{leaf:unknown}>,path:Path):boolean=>{
  // Use the actual native prefix, not the legacy fact-only path. In particular
  // frame/mono/linear rows precede lemma rows and affect every input-row index.
  const actual=framePath(cert.frames??[],cert.lemmas??[],path,cert.monos??[],cert.lins??[])
  const rows=leafConstraints(goal,actual),present=new Set<string>(),suppliers=new Map<string,Set<number>>()
  for(let i=0;i<rows.length;i++){
   tick('pair-scope:source-row');const row=rows[i]!,src=row.src
   if(!src||!('atom'in src||'fact'in src))continue
   if('fact'in src&&(!Number.isSafeInteger(src.fact)||src.fact<0||src.fact>=goal.hyps.length))return false
   visitLinearCells(row.lin,name=>{
    tick('pair-scope:source-cell');if(!isCell(name))return
    // Include stored zero coefficients: the native name collector does too.
    present.add(name)
    if('fact'in src){let owners=suppliers.get(name);if(!owners)suppliers.set(name,(owners=new Set()));owners.add(src.fact)}
   },'pair-scope:source-cells')
  }
  const todo:number[]=[],seen=new Set<number>(),n=rows.length,squares=tree.squares?.length??0,products=tree.products??[]
  for(let i=0;i<tree.leaf.length;i++){tick('pair-scope:input-step');const step=tree.leaf[i]!;if(step.kind==='input')todo.push(step.index)}
  // The exact transporter also reindexes all retained product operands, even
  // products not cited by the final arithmetic. Keep their pair support too.
  for(let i=0;i<products.length;i++){tick('pair-scope:product-operands');const pair=products[i]!;todo.push(pair[0],pair[1])}
  while(todo.length){
   tick('pair-scope:referenced-row');const index=todo.pop()!
   if(!Number.isSafeInteger(index)||index<0||index>=n+squares+products.length)return false
   if(seen.has(index))continue;seen.add(index)
   if(index<n){
    const src=rows[index]!.src
    if(src&&'fact'in src)found.add(src.fact)
    if(src&&'pair'in src)for(const cell of src.pair){
     tick('pair-scope:pair-cell');if(!present.has(cell))return false
     // A path atom alone can supply a cell. Otherwise retain every fact-row
     // owner, not an arbitrary first match or only a nonzero coefficient.
     for(const owner of suppliers.get(cell)??[]){tick('pair-scope:cell-owner');found.add(owner)}
    }
   }else if(index>=n+squares){
    const pair=products[index-n-squares]!
    // Normal products only refer backwards. Refuse malformed/cyclic metadata
    // instead of guessing a smaller scope; never turn this into acceptance.
    if(!pair||!Number.isSafeInteger(pair[0])||!Number.isSafeInteger(pair[1])||pair[0]<0||pair[1]<0||pair[0]>=index||pair[1]>=index)return false
    todo.push(pair[0],pair[1])
   }
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
