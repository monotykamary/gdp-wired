// An explicit conditional pointwise lemma, not a safety or invariant proof.
import {readFileSync,writeFileSync} from 'node:fs'
import {brotliDecompressSync,brotliCompressSync,constants} from 'node:zlib'
import {createHash} from 'node:crypto'
import {type E,type C,get,not,x,walkOnce} from '../../core/machine.ts'
import {countLawSeeds} from '../../core/count-focused.ts'
import {candidateWork,grammarPool} from '../../core/count-support.ts'
import {memberInclusions} from '../../core/count-recovery/member-inclusions.ts'
import {countedObligations,mcGoal,checkMC,substC} from '../../kernel/kernel.ts'
import {clock,counted,fullRate,fullWork,grow,withWall} from '../../kernel/prove.ts'
const [input,carried,targetMap,control='guarded',msText='1000']=process.argv.slice(2)
if(!input||!carried||!targetMap||!['guarded','unguarded','tight','guarded-domain','unguarded-domain','tight-domain'].includes(control))throw Error('input, carried map, target map, guarded|unguarded|tight, ms required')
const [file,entry]=input.split('#'),text=entry?JSON.parse(brotliDecompressSync(readFileSync(file!)).toString())[entry]:readFileSync(file!,'utf8'),d=JSON.parse(text),ms=Number(msText),start=performance.now(),work=fullWork()
const result=withWall(start+Math.max(1000,ms*4),()=>counted(fullRate,()=>{
 const until=clock()+ms,m=d.machine,laws=d.laws,law=laws.find((l:any)=>l.name===d.law),index=laws.indexOf(law),own:E[]=[...(law?.forall?[x(law.forall+'#')]:[]),...(law?.keys??[]).map(x)],keyed=new Set<string>()
 walkOnce([m.step,m.assume],(o:any)=>{if(o.op==='get')walkOnce(o.key,(v:any)=>{if(v.op==='var'&&m.inputs.includes(v.name))keyed.add(v.name)})})
 const terms=[...own,...m.inputs.filter((n:string)=>keyed.has(n)).map(x)].slice(0,4),at=countLawSeeds(m,laws,d.instances,terms,terms),p=countedObligations(m,laws,{[law.name]:at},index).find(p=>p.goal.name===d.rawGoal.name)
 if(!p)throw Error('missing STEP packet')
 const pool=grammarPool(p.goal,p.decls,1000,candidateWork(),true,m),spec=memberInclusions(m,p.decls,pool.full.reads).find(s=>s.carried===carried&&pool.full.reads.some(r=>r[0]===s.negative&&r[1]===targetMap))
 if(!spec)throw Error('missing proposed pointwise inclusion')
 const pos=pool.full.reads.find(r=>r[0]===spec.positive)!,neg=pool.full.reads.find(r=>r[0]===spec.negative)!,inst=pool.full.insts.find(q=>q.unit===0&&JSON.stringify(q.below)===JSON.stringify(spec.below)&&q.terms.length===2&&q.terms.some(([a,v])=>a===1&&v===spec.positive)&&q.terms.some(([a,v])=>a===-1&&v===spec.negative))
 if(!inst)throw Error('missing ordinary witness instance')
 const wit=x(inst.wit),flagNames:string[]=[],flags:C[]=[]
 for(const [name,q]of Object.entries(m.step.flags??{}) as [string,C][]){
  if(q.op!=='all'||q.keys?.length)continue
  let uses=false;walkOnce(q.c,(v:any)=>{if(v.op==='get'&&v.map===carried)uses=true})
  if(uses){flagNames.push(name);flags.push(substC(q.c,{vars:{[q.key]:wit},maps:{},flags:{}}))}
 }
 if(!flags.length)throw Error('missing explicit conditional member flags')
 // Removing +1 strengthens the conditional claim. This is an explicit
 // research proof attempt, not a trusted normalization in the selector.
 const baseControl=control.replace('-domain',''),scalarContext:C[]=[]
 const collectScalar=(c:C,negative=false):void=>{
  if(c.op==='not'){collectScalar(c.x,!negative);return}
  if(c.op===(!negative?'and':'or')){for(const q of c.xs)collectScalar(q,negative);return}
  if(!['=','<','<='].includes(c.op))return
  let scalar=true;walkOnce(c,(v:any)=>{if(['get','flag','all'].includes(v.op))scalar=false})
  if(scalar)scalarContext.push(negative?not(c):c)
 }
 if(control.endsWith('-domain'))for(const h of p.goal.hyps)collectScalar(h)
 const guards=baseControl==='unguarded'?[]:spec.guards.map(c=>{
  if(baseControl!=='tight'||c.op!=='<'||c.a.op!=='add')return c
  const a=c.a,term=a.a.op==='const'&&a.a.value===1?a.b:a.b.op==='const'&&a.b.value===1?a.a:undefined
  return term?{...c,a:term}:c
 }),claim:C={op:'<=',a:get(pos[1],pos[2]),b:get(neg[1],neg[2])},hyps=[...scalarContext,...guards,...flags,not(claim)],cert={reads:[pos,neg],insts:[inst]},goal=mcGoal(hyps,p.decls,cert)
 if(!goal)throw Error('kernel rejected pointwise packet')
 const out=grow(goal,new Map(),{nodes:0,until}),proven='tree'in out,checked=proven&&checkMC(hyps,p.decls,{...cert,tree:out.tree})
 const bundle=proven&&checked&&process.env.MLDR_POINTWISE_OUT?{kind:'conditional-pointwise',inputSha256:createHash('sha256').update(text).digest('hex'),control,carried,targetMap,hyps,decls:p.decls.filter(d=>cert.reads.some(r=>r[1]===d.map)),cert:{...cert,tree:out.tree}}:undefined
 if(bundle&&!checkMC(bundle.hyps,bundle.decls,bundle.cert))throw Error('projected certificate failed independent kernel check')
 return {bundle,scope:'conditional pointwise lemma; NOT a safety proof',control,carried,targetMap,flagNames,scalarContext,guards,proposedGuards:spec.guards,pos,neg,proven,checked,...(!proven?{stuck:out.stuck,why:out.why,witness:out.witness}:{})}
},true))
const {bundle,...receipt}=result
let artifact:undefined|{encoding:string,sha256:string,data:string}
if(bundle){const bytes=brotliCompressSync(Buffer.from(JSON.stringify(bundle)),{params:{[constants.BROTLI_PARAM_QUALITY]:4}});writeFileSync(process.env.MLDR_POINTWISE_OUT!,bytes);artifact={encoding:'br',sha256:createHash('sha256').update(bytes).digest('hex'),data:bytes.toString('base64')}}
console.log(JSON.stringify({...receipt,ms,inputSha256:createHash('sha256').update(text).digest('hex'),countedMs:(fullWork()-work)/fullRate,wallMs:performance.now()-start,...(artifact?{artifact}:{})}))
