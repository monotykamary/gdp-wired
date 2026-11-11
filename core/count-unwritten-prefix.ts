// Untrusted shared prefix for unwritten row counts. Every reusable result is
// checked after alpha-renaming; no frame is inferred merely from a row label.
import {type C,type E,n,not,same,walkOnce,x} from './machine.ts'
import {countCertificateRenamer} from './count-cert-rename.ts'
import {countsForReads} from './count-facts.ts'
import {type Count,type CountDecl,type LinCut,type MapRead,linOk,substE} from '../kernel/kernel.ts'
import {clock} from '../kernel/prove.ts'
import {guardLinearFact} from './count-guard-facts.ts'
import {replayLinearSkeleton} from './count-replay-skeleton.ts'
// A hint, never an equality assumption: alpha-renaming can change which
// orientation a stored derivation supports. Admit the reverse only by linOk.
export function checkedReversePrefix(counts:Count[],cut:LinCut):LinCut|undefined{
 const candidate={...cut,pos:cut.neg,neg:cut.pos}
 return linOk(counts,candidate)?candidate:undefined
}
// Unlike swapping a proof, this rebuilds every leaf for the opposite claim.
// It may only return a cut that linOk accepts under the original conditions.
export function replayReversePrefix(counts:Count[],cut:LinCut,until:number):LinCut|undefined{
 if(clock()>=until)return
 const pos=cut.neg,neg=cut.pos,first=counts.find(c=>c.v===(pos[0]??neg[0])?.[1])
 if(!first||[...pos,...neg].some(([,id])=>!counts.some(c=>c.v===id)))return
 const term=(side:[number,string][]):E=>side.reduceRight<E>((rest,[k,id])=>({op:'add',a:{op:'mul',k,a:counts.find(c=>c.v===id)!.body},b:rest}),n(0))
 const goal={name:'replayed opposite prefix',hyps:[...cut.when,{op:'<' as const,a:x(first.key),b:first.below},{op:'<' as const,a:term(neg),b:term(pos)}]}
 const tree=replayLinearSkeleton(goal,cut.tree,new Map(),until)
 const candidate=tree&&{...cut,pos,neg,tree}
 return candidate&&clock()<until&&linOk(counts,candidate)?candidate:undefined
}
export class UnwrittenCountPrefix {
 private cache=new Map<string,LinCut>()
 readonly stats={proofs:0,hits:0,refusals:0}
 constructor(private decls:CountDecl[],private reads:MapRead[],private guards:C[],private written:E,private rowBound:E,private search:'grow'|'cdcl'='grow',private options:{deferCheck?:boolean}={}){}
 prove(post:string,pre:string,rows:E[],sign:1|-1,until:number):LinCut|undefined{
  const p=this.reads.find(r=>r[0]===post),q=this.reads.find(r=>r[0]===pre)
  if(!p||!q||p[1]!==q[1]+'#'||JSON.stringify(p[2])!==JSON.stringify(q[2]))return
  const names=[...new Set(rows.flatMap(r=>r.op==='var'?[r.name]:[]))]
  if(names.length!==rows.length)return
  const fixed=new Set<string>();for(const c of [...this.guards,this.written,this.rowBound])walkOnce(c,(v:any)=>{if(v.op==='var')fixed.add(v.name)})
  if(names.some(n=>fixed.has(n)))return
  const scope=JSON.stringify([this.decls,this.reads,this.guards,this.written,this.rowBound]);let prefix='unwritten$'
  while(scope.includes(prefix))prefix='$'+prefix
  const vars=Object.fromEntries(names.map((name,i)=>[name,x(prefix+'r'+i)])),sub={vars,maps:{},flags:{}}
  const key=substE(p[2],sub),genericRows=names.map(n=>vars[n]!),when=[...this.guards,...genericRows.flatMap(row=>[{op:'<' as const,a:row,b:this.rowBound},not(same(row,this.written))])]
  const generic:MapRead[]=[[prefix+'post',p[1],key],[prefix+'pre',q[1],key]],terms:[number,string][]=[[sign,generic[0]![0]],[-sign,generic[1]![0]]]
  const cacheKey=JSON.stringify([generic,when,terms]);let cut=this.cache.get(cacheKey)
  if(cut)this.stats.hits++
  else{
   this.stats.proofs++
   const fact=guardLinearFact(this.decls,generic,{name:'unwritten count prefix',kind:'ordinary-unwritten-count',when,terms},Math.min(until,clock()+60),undefined,this.search,this.options)
   if(!fact){this.stats.refusals++;return}
   cut=fact.cut;this.cache.set(cacheKey,cut)
  }
  const renames=new Map<string,string>(names.map((name,i)=>[prefix+'r'+i,name]));renames.set(generic[0]![0],post);renames.set(generic[1]![0],pre)
  if(clock()>=until)return
  const renamed=countCertificateRenamer(renames,until).certificate({reads:generic,insts:[],picks:[],lins:[cut],tree:{leaf:[]}}).lins![0]!
  const counts=countsForReads(this.decls,this.reads)
  if(!counts||!this.options.deferCheck&&!linOk(counts,renamed)){this.stats.refusals++;return}
  return renamed
 }
}
