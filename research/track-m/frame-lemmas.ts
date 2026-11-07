// Factor valid count-frame inequalities out of a large counted obligation.
// Every cut is an ordinary checked Tree split; no frame is trusted as a fact.
import {type C,type E,walkOnce,x} from '../../core/machine.ts'
import {type CountCert,type Goal,type Path,type Tree,canon,check,substC} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {modelSequence} from '../../kernel/model-sequence.ts'
import {REFUTED} from '../../kernel/cdcl.ts'
import {liftCountProxies} from './lift-count-proxies.ts'
import {piecesAt,walkLive} from './live-dependencies.ts'
import {booleanCore} from './boolean-core.ts'
type Proposal=Pick<CountCert,'reads'|'insts'>
export function frameLemmas(g:Goal,cert:Proposal,until:number,trace:object[],root:Path=new Map(),options:{stopAfterFailed?:number,boolean?:boolean}={}):Tree|undefined {
 let failed=0
 const seq=modelSequence(root),base=g.hyps.slice(0,g.hyps.length-cert.insts.length),ctx:C[]=[],path:Path=new Map(root),lemmas:{split:Record<string,number>,no:Tree}[]=[]
 const reads=new Map(cert.reads.map(r=>[r[0],r])),maps=new Set(cert.reads.map(r=>r[1])),wits=new Set(cert.insts.map(i=>i.wit))
 const weaken=(c:C,wit:string):C|undefined=>{
  if(c.op==='and'){const xs=c.xs.flatMap(x=>{const y=weaken(x,wit);return y?[y]:[]});return xs.length?{op:'and',xs}:undefined}
  let count=false,other=false,own=false
  walkLive(c,root,(o:any)=>{if(o.op==='get'&&maps.has(o.map))count=true;if(o.op==='var'&&wits.has(o.name)){if(o.name===wit)own=true;else other=true}})
  return count||other&&!own?undefined:c
 }
 const solve=(goal:Goal,limit:number,finish=false):Tree|undefined=>{
  if(finish){
   const pieces=(c:C)=>piecesAt(c,root)
   const maps=Object.fromEntries([...new Set(cert.reads.map(r=>r[1]))].map(map=>[map,(key:E):E=>{const r=cert.reads.find(r=>r[1]===map&&JSON.stringify(r[2])===JSON.stringify(key));return r?x(r[0]):{op:'get',map,key}}]))
   const flags:Record<string,C>={};walkOnce(goal.hyps,(o:any)=>{if(o.op==='flag')flags[o.name]={op:'flag',name:o.name}})
   const hyps=goal.hyps.map(c=>substC(c,{vars:{},maps,flags})).flatMap(c=>pieces(c)).filter(c=>{let skip=false;walkLive(c,root,(o:any)=>{if(o.op==='get'||o.op==='var'&&wits.has(o.name))skip=true});return !skip})
   const numeric={...goal,hyps},start=clock(),q=seq(numeric,Math.min(until,clock()+150))
   trace.push({stage:'frame-arithmetic',hyps:hyps.length,ms:Math.round(clock()-start),outcome:'tree'in q?'tree':q.stuck,core:q.core?.length})
   let proof='tree'in q?q.tree:undefined
   if(!proof&&!('tree'in q)&&q.why===REFUTED&&q.core?.length){const reduced={...numeric,hyps:q.core.map(i=>hyps[i]!)},out=grow(reduced,root,{nodes:0,until:Math.min(until,clock()+150),units:false});if('tree'in out)proof=widen(reduced,numeric,out.tree,{},root,root)}
   if(proof){const lifted=liftCountProxies(numeric,goal,proof,cert.reads,root,root,event=>trace.push({stage:'proxy-lift',...event}));trace.push({stage:'frame-arithmetic-lift',ms:Math.round(clock()-start),proved:!!lifted});if(lifted)return lifted}
  }
  const q=seq(goal,Math.min(until,clock()+limit))
  if('tree'in q)return q.tree
  if(q.why!==REFUTED||!q.core?.length)return undefined
  const reduced={...goal,hyps:q.core.map(i=>goal.hyps[i]!)}
  if(options.boolean&&q.core.length<=8){const tree=booleanCore(reduced,root,wits,Math.min(until,clock()+100),trace);if(tree)return widen(reduced,goal,tree,{},root,root)}
  const out=grow(reduced,root,{nodes:0,until:Math.min(until,clock()+200),units:false})
  return 'tree'in out?widen(reduced,goal,out.tree,{},root,root):undefined
 }
 for(const [i,instance] of cert.insts.entries()){
  if(clock()>=until)break
  if(instance.unit!==0||instance.terms.length!==2)continue
  const [a,b]=instance.terms.map(t=>reads.get(t[1]))
  if(!a||!b||a[1].replace(/#$/,'')!==b[1].replace(/#$/,'')||a[1].endsWith('#')===b[1].endsWith('#')||JSON.stringify(a[2])!==JSON.stringify(b[2]))continue
  const h=g.hyps[base.length+i]
  if(h?.op!=='or'||h.xs[0]?.op!=='<=')continue
  const good=h.xs[0],split=Object.fromEntries(instance.terms.map(([n,v])=>[v,n])),noPath=new Map(path).set(canon(split),{lin:split,holds:false})
  const relevant=base.flatMap(c=>piecesAt(c,root)).flatMap(c=>{const kept=weaken(c,instance.wit);return kept?[kept]:[]})
  const part={...g,hyps:[...relevant,...ctx,h,{op:'not' as const,x:good}]},start=clock(),tree=solve(part,150)
  const no=tree&&widen(part,g,tree,{},root,noPath)
  trace.push({stage:'frame-lemma',index:i,ms:Math.round(clock()-start),proved:!!no})
  if(!no){if(++failed>=(options.stopAfterFailed??Infinity)&&!lemmas.length)return undefined;continue}
  lemmas.push({split,no});ctx.push(good);path.set(canon(split),{lin:split,holds:true})
 }
 if(!lemmas.length||clock()>=until)return undefined
 const part={...g,hyps:[...g.hyps,...ctx]},start=clock(),found=solve(part,Math.max(150,until-clock()-200),true)
 let tree=found&&widen(part,g,found,{},root,path)
 trace.push({stage:'frame-conclusion',facts:lemmas.length,ms:Math.round(clock()-start),proved:!!tree})
 if(!tree)return undefined
 for(const lemma of [...lemmas].reverse())tree={split:lemma.split,yes:tree,no:lemma.no}
 return check(g,tree,root)?tree:undefined
}
