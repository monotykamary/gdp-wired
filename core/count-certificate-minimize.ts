// Untrusted certificate size reduction. No proof verdict is cached or minted:
// the caller must check the result on its original INIT/STEP obligations.
import {type C, type Law} from './machine.ts'
import {type CountCert, type CountDecl, type FrameCut, type Goal, type Instances, type Path, type Tree, assumed, canon, frameOk, framePath, frameRows, linRows, mcGoal} from '../kernel/kernel.ts'
import {late, rowsAt} from '../kernel/prove.ts'
import {type Constraint, type Step} from './solver.ts'
import {countsForReads} from './count-facts.ts'

export function countCertificateSize(cert: CountCert) {
  let leaves=0, splits=0, steps=0
  const pending=[{tree:cert.tree,exit:false}],active=new Set<Tree>()
  while(pending.length){const {tree,exit}=pending.pop()!;if(exit){active.delete(tree);continue}if(active.has(tree))throw Error('cyclic certificate tree');if('leaf'in tree){leaves++;steps+=tree.leaf.length}else{active.add(tree);splits++;pending.push({tree,exit:true},{tree:tree.no,exit:false},{tree:tree.yes,exit:false})}}
  return {leaves,splits,steps,frames:cert.frames?.length??0,lins:cert.lins?.length??0,monos:cert.monos?.length??0,instances:cert.insts.length}
}

// Remove only exact duplicate instantiated formulas. Plain laws and unknown
// flag instances stay; the caller rebuilds its original goal and reindexes.
export function dedupeCountInstances(family: Law[], facts: Law[], original: Instances) {
  const laws=[...family,...facts],seen=new Set(laws.filter(l=>!l.forall).flatMap(l=>assumed([l],{})).map(h=>JSON.stringify(h)))
  const instances: Instances={},removed: string[]=[]
  for(const [name,terms]of Object.entries(original)){
    const law=laws.find(l=>l.name===name),arity=law?.forall?1+(law.keys?.length??0):0
    if(!law||!arity||terms.length%arity){instances[name]=terms;continue}
    const kept:typeof terms=[]
    for(let i=0;i<terms.length;i+=arity){
      const tuple=terms.slice(i,i+arity),keys=assumed([law],{[name]:tuple}).map(h=>JSON.stringify(h))
      if(keys.length&&keys.every(key=>seen.has(key)))removed.push(name)
      else{kept.push(...tuple);keys.forEach(key=>seen.add(key))}
    }
    if(kept.length)instances[name]=kept
  }
  return {instances,removed}
}

export type CountMinimizeOptions={lift?:boolean,merge?:boolean,maxVisits?:number}
export function minimizeCountCertificate(hyps:C[],decls:CountDecl[],original:CountCert,until:number,options:CountMinimizeOptions={}) {
  const before=countCertificateSize(original),stats={before,after:before,liftAttempts:0,liftedSplits:0,frameMerges:0,unusedFrames:0,unusedLins:0,duplicateLins:0,fastRejected:0,visits:0,rowsBuilt:0,aborted:false,missing:[] as {split:string,rows:string[]}[]}
  if(late(until)){stats.aborted=true;return {cert:original,stats}}
  const goal=mcGoal(hyps,decls,original),counts=countsForReads(decls,original.reads)
  if(!goal||!counts)return {cert:original,stats}
  const live=()=>{const ok=!late(until)&&stats.visits++<(options.maxVisits??200000);if(!ok)stats.aborted=true;return ok}
  const rowGetter=(g:Goal,c:CountCert)=>{
    const cache=new Map<string,Constraint[]>()
    return (path:Path)=>{
      const key=JSON.stringify([...path]);let rows=cache.get(key)
      if(!rows){rows=rowsAt(g,framePath(c.frames??[],c.lemmas??[],path,c.monos??[],c.lins??[]));stats.rowsBuilt++;if(cache.size>=4096)cache.delete(cache.keys().next().value!);cache.set(key,rows)}
      return rows
    }
  }
  const rowIndices=new WeakMap<Constraint[],Map<string,number>>()
  const transport=(tree:Tree,from:Path,to:Path,oldRows:(p:Path)=>Constraint[],newRows:(p:Path)=>Constraint[],missing:string[],depth=0):Tree|undefined=>{
    if(!live()||depth>512)return undefined
    if('split'in tree){
      const id=canon(tree.split)
      if(to.has(id))return undefined
      const next=(path:Path,holds:boolean)=>new Map(path).set(id,{lin:tree.split,holds})
      const yes=transport(tree.yes,next(from,true),next(to,true),oldRows,newRows,missing,depth+1)
      const no=yes&&transport(tree.no,next(from,false),next(to,false),oldRows,newRows,missing,depth+1)
      return yes&&no?{split:tree.split,yes,no}:undefined
    }
    const a=oldRows(from),b=newRows(to)
    let indices=rowIndices.get(b)
    if(!indices){indices=new Map();b.forEach((r,i)=>{const key=canon(r.lin);if(!indices!.has(key))indices!.set(key,i)});rowIndices.set(b,indices)}
    const squares=tree.squares?.length??0,products=tree.products??[]
    const index=(i:number,limit=a.length+squares+products.length):number|undefined=>{
      if(!Number.isSafeInteger(i)||i<0||i>=limit)return undefined
      if(i>=a.length)return i-a.length+b.length
      const key=canon(a[i]!.lin),j=indices.get(key)
      if(j===undefined&&missing.length<8)missing.push(key)
      return j
    }
    const leaf:Step[]=[]
    for(const step of tree.leaf){if(step.kind!=='input')leaf.push(step);else{const i=index(step.index);if(i===undefined)return undefined;leaf.push({...step,index:i})}}
    const pairs:[number,number][]=[]
    for(let n=0;n<products.length;n++){const [a0,b0]=products[n]!,i=index(a0,a.length+squares+n),j=index(b0,a.length+squares+n);if(i===undefined||j===undefined)return undefined;pairs.push([i,j])}
    return {leaf,...(tree.products?{products:pairs}:{}),...(tree.squares?{squares:tree.squares}:{})}
  }
  let cert=original
  const oldRows=rowGetter(goal,original)
  if(options.merge!==false){
    const used=new Set<string>()
    const collect=(tree:Tree,path:Path,depth=0):void=>{
      if(!live()||depth>512){stats.aborted=true;return}
      if('split'in tree){const id=canon(tree.split);collect(tree.yes,new Map(path).set(id,{lin:tree.split,holds:true}),depth+1);collect(tree.no,new Map(path).set(id,{lin:tree.split,holds:false}),depth+1);return}
      const rows=oldRows(path),indices=[...tree.leaf.flatMap(s=>s.kind==='input'?[s.index]:[]),...(tree.products??[]).flat()]
      for(const i of indices)if(rows[i])used.add(canon(rows[i]!.lin))
    }
    if((original.frames?.length??0)||(original.lins?.length??0))collect(original.tree,new Map())
    const groups=new Map<string,FrameCut[]>()
    const neededFrames=(original.frames??[]).filter(f=>frameRows(f).some(row=>used.has(canon(row))))
    stats.unusedFrames=(original.frames?.length??0)-neededFrames.length
    for(const frame of neededFrames){const key=JSON.stringify([frame.post,frame.pre]),group=groups.get(key)??[];groups.set(key,group);group.push(frame)}
    const frames:FrameCut[]=[]
    for(const group of groups.values()){
      const kept:FrameCut[]=[]
      for(const frame of group){
        let merged=false
        for(let i=0;i<kept.length;i++){
          const prior=kept[i]!,keys=new Set(frame.when.map(canon)),candidate={post:frame.post,pre:frame.pre,when:prior.when.filter(w=>keys.has(canon(w)))}
          if(frameOk(counts,candidate)){kept[i]=candidate;stats.frameMerges++;merged=true;break}
        }
        if(!merged)kept.push(frame)
      }
      frames.push(...kept)
    }
    const side=(terms:[number,string][])=>{const sum=new Map<string,number>();for(const [k,name]of terms)sum.set(name,(sum.get(name)??0)+k);return [...sum].filter(([,k])=>k!==0).sort(([a],[b])=>a.localeCompare(b))}
    const seen=new Set<string>(),lins=(original.lins??[]).filter(cut=>{if(!linRows(cut).some(row=>used.has(canon(row)))){stats.unusedLins++;return false}const key=JSON.stringify([cut.when.map(c=>JSON.stringify(c)).sort(),side(cut.pos),side(cut.neg)]);if(seen.has(key)){stats.duplicateLins++;return false}seen.add(key);return true})
    const candidate={...original,frames,lins}
    if(stats.frameMerges||stats.duplicateLins||stats.unusedFrames||stats.unusedLins){const tree=transport(original.tree,new Map(),new Map(),oldRows,rowGetter(goal,candidate),[]);if(tree)cert={...candidate,tree};else{stats.frameMerges=0;stats.duplicateLins=0;stats.unusedFrames=0;stats.unusedLins=0}}
  }
  if(options.lift!==false){
    const rows=rowGetter(goal,cert),metadata=new WeakMap<Tree,{leaves:number,used:Set<string>}>()
    const mark=(tree:Tree,path:Path):{leaves:number,used:Set<string>}=>{
      const known=metadata.get(tree);if(known)return known
      let meta:{leaves:number,used:Set<string>}
      if('leaf'in tree){
        const keys=[...framePath(cert.frames??[],cert.lemmas??[],path,cert.monos??[],cert.lins??[]).keys()],used=new Set<string>()
        for(const i of [...tree.leaf.flatMap(s=>s.kind==='input'?[s.index]:[]),...(tree.products??[]).flat()])if(i<keys.length&&path.has(keys[i]!))used.add(keys[i]!)
        meta={leaves:1,used}
      }else{const key=canon(tree.split),yes=mark(tree.yes,new Map(path).set(key,{lin:tree.split,holds:true})),no=mark(tree.no,new Map(path).set(key,{lin:tree.split,holds:false}));meta={leaves:yes.leaves+no.leaves,used:new Set([...yes.used,...no.used])}}
      metadata.set(tree,meta);return meta
    }
    const visit=(tree:Tree,path:Path,depth=0):Tree=>{
      if(!live()||depth>512){stats.aborted=true;return tree}
      if('leaf'in tree){const leaf={...tree};mark(leaf,path);return leaf}
      const key=canon(tree.split),yesPath=new Map(path).set(key,{lin:tree.split,holds:true}),noPath=new Map(path).set(key,{lin:tree.split,holds:false})
      const yes=visit(tree.yes,yesPath,depth+1),no=visit(tree.no,noPath,depth+1),children:[Tree,Path][]=[[yes,yesPath],[no,noPath]]
      if(!metadata.has(yes)||!metadata.has(no))return {split:tree.split,yes,no}
      children.sort(([a],[b])=>metadata.get(a)!.leaves-metadata.get(b)!.leaves)
      for(const [child,from]of children){
        stats.liftAttempts++
        // Like the ordinary prover's lift, conservatively leave a subtree
        // that directly uses the discarded path decision intact.
        if(metadata.get(child)!.used.has(key)){stats.fastRejected++;continue}
        const missing:string[]=[],lifted=transport(child,from,path,rows,rows,missing)
        if(lifted){stats.liftedSplits++;mark(lifted,path);return lifted}
        if(stats.missing.length<10&&missing.length)stats.missing.push({split:key,rows:missing})
      }
      const result={split:tree.split,yes,no};mark(result,path);return result
    }
    cert={...cert,tree:visit(cert.tree,new Map())}
  }
  stats.after=countCertificateSize(cert)
  return {cert,stats}
}
