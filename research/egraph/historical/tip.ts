// Exact historical prod/lemma_09, never a synthetic tail obligation.
import {readFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
import {gzipSync} from 'node:zlib'
import {parseTip, parseSx} from '../../../compare/tip/tip.ts'
import {translate} from '../../../compare/tip/translate.ts'
import {proveData, programOf, encY, showY} from '../../../core/data.ts'
import {type C, type E, n, not} from '../../../core/machine.ts'
import {substC, type Tree} from '../../../kernel/kernel.ts'
import {type Cyclic, refuseCyclic} from '../../../kernel/cyclic.ts'
import {withWall, fullWork} from '../../../kernel/prove.ts'
import {EGraph, Meter} from '../match.ts'
import {certify, type Spec} from '../certify.ts'
const hash=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
const file='research/egraph/historical/inputs/gdp-wired-laneRL/research/frontier2/tasks/tip/prod/lemma_09.smt2'
const bytes=readFileSync(file), sourceBefore=hash(bytes)
const ownFiles=['core/data.ts','core/cyclic.ts','core/solver.ts','kernel/kernel.ts','kernel/cyclic.ts','kernel/prove.ts','compare/tip/tip.ts','compare/tip/translate.ts','research/egraph/match.ts','research/egraph/certify.ts']
const sourceHashes=()=>Object.fromEntries(ownFiles.map(p=>[p,hash(readFileSync(p))]))
const sourcePins=sourceHashes()
console.log('SOURCE',JSON.stringify(sourcePins))
const formulas=(JSON.parse(readFileSync('compare/tip/lemmas-sample30.json','utf8')) as Record<string,string[]>)['prod/lemma_09.smt2']!
const tr=translate(parseTip(bytes.toString()),'prod/lemma_09.smt2',formulas.flatMap(s=>parseSx(s)),{sorts:'abstract'})
const concl=encY(programOf([tr.law,...tr.lemmas],[],false),tr.law.holds,new Map())
console.log('INPUT',JSON.stringify({id:'prod/lemma_09.smt2',sha256:sourceBefore,formula:showY(tr.law.holds),concl,changes:tr.changes,notes:tr.notes,lemmas:formulas,lemmaSha256:hash(JSON.stringify(formulas)),options:{sorts:'abstract',lemmas:false,transfer:false,ms:10000},runtime:Bun.version}))
if(tr.changes.length) throw Error('statement changed')
const baseline=withWall(performance.now()+60000,()=>proveData(tr.law,{ms:57000}))
console.log('PRODUCTION_BASELINE',JSON.stringify({proven:baseline.proven,checked:baseline.checked,goal:baseline.goal,stuck:baseline.stuck,lemmas:baseline.lemmas,ms:baseline.ms,scope:'unchanged main9753 datatype engine; not historical dirty depth2 overlay'}))
const combined:Cyclic={facts:[],nodes:[]}, roots:number[]=[]
for(const law of tr.lemmas){
  const work=fullWork(), v=withWall(performance.now()+20000,()=>proveData(law,{lemmas:false,transfer:false,ms:10000}))
  console.log('LEMMA',JSON.stringify({law:showY(law.holds),proven:v.proven,checked:v.checked,goal:v.goal,stuck:v.stuck,proofUnits:fullWork()-work}))
  if(!v.proof?.proven||v.node===undefined) throw Error('historical lemma not proved')
  const p=v.proof.proof, why=refuseCyclic(p);if(why)throw Error(why)
  const indices=p.facts.map(f=>{const key=JSON.stringify(f);let j=combined.facts.findIndex(g=>JSON.stringify(g)===key);if(j<0){j=combined.facts.length;combined.facts.push(f)}return j})
  const offset=combined.nodes.length
  combined.nodes.push(...p.nodes.map(node=>({...structuredClone(node),insts:node.insts.map(i=>({...i,fact:indices[i.fact]!})),uses:node.uses.map(u=>({...structuredClone(u),node:u.node+offset}))})))
  roots.push(offset+v.node)
}
const combinedWhy=refuseCyclic(combined);if(combinedWhy)throw Error(`combined prefix: ${combinedWhy}`)
const meter=new Meter(500000,performance.now()+2000),graph=new EGraph(meter)
graph.seed([not(concl)])
const assoc=combined.nodes[roots[0]!]!,snoc=combined.nodes[roots[1]!]!
if(assoc.concl.op!=='='||snoc.concl.op!=='=')throw Error('expected historical equational lemma roots')
const assocBindings=graph.match([assoc.concl.b],tr.lemmas[0]!.vars.map(v=>v.name),1)
const hints:[E,E][]=[]
for(const vars of assocBindings){const c=substC(assoc.concl,{vars,maps:{},flags:{}});if(c.op!=='=')throw Error('equation');hints.push([c.a,c.b]);graph.seed([c])}
const snocBindings=graph.match([snoc.concl.a],tr.lemmas[1]!.vars.map(v=>v.name),8)
const uses=[...assocBindings.map(subst=>({node:roots[0]!,subst,guard:{op:'<=',a:n(0),b:n(0)} as C})),...snocBindings.map(subst=>({node:roots[1]!,subst,guard:{op:'<=',a:n(0),b:n(0)} as C}))]
const levels=roots.map(i=>combined.nodes[i]!.rank[0]!)
if(levels.some(l=>l.op!=='const'))throw Error('nonconstant lemma level')
const rank=[n(1+Math.max(...levels.map(l=>(l as Extract<E,{op:'const'}>).value))),...assoc.rank.slice(1).map(()=>n(0))]
const client:Spec={name:'historical prod/lemma_09.smt2',hyps:[],concl,rank,insts:[],uses}
const splitCount=(t:Tree):number=>'split'in t?1+splitCount(t.yes)+splitCount(t.no):0
console.log('MATCH',JSON.stringify({assocBindings,snocBindings,matchingUnits:meter.used,explicitSplitHints:hints,automaticExplanationExtraction:false}))
for(const mode of ['disabled','enabled-no-hints','enabled','ablated-assoc','ablated-snoc'] as const){
  const chosen=mode==='disabled'?[]:mode==='ablated-assoc'?uses.filter(u=>u.node!==roots[0]):mode==='ablated-snoc'?uses.filter(u=>u.node!==roots[1]):uses
  const specs:Spec[]=[...combined.nodes,{...client,uses:chosen}]
  const result=certify(combined.facts,specs,meter.used,2000000,combined.nodes,mode==='enabled-no-hints'?[]:hints)
  const proof=result.proof, root=proof?.nodes.at(-1)
  const controls:Record<string,string|undefined>={}
  if(result.checked&&proof&&root){
    for(const [name,lemma] of [['remove-assoc',roots[0]!],['remove-snoc',roots[1]!]] as const){const p=structuredClone(proof);p.nodes.at(-1)!.uses=p.nodes.at(-1)!.uses.filter(u=>u.node!==lemma);controls[name]=refuseCyclic(p)}
    const bad=structuredClone(proof);bad.nodes[roots[1]!]!.main={leaf:[]};controls['corrupt-lemma']=refuseCyclic(bad)
    const badRank=structuredClone(proof);badRank.nodes.at(-1)!.rank=snoc.rank;controls['nondecreasing-rank']=refuseCyclic(badRank)
  }
  if(result.checked && (Object.values(controls).some(v=>v===undefined) || JSON.stringify(root?.concl)!==JSON.stringify(concl)))throw Error('unsafe accepted comparison or wrong root')
  const serialized=proof&&JSON.stringify(proof)
  console.log('RESULT',JSON.stringify({mode,checked:result.checked,reason:result.reason,proofUnits:result.proofUnits,hintUnits:result.hintUnits,matchedSnoc:snocBindings.length,checkedRootSnocUses:result.checked?root?.uses.filter(u=>u.node===roots[1]).length:0,proofSha256:serialized&&hash(serialized),splitNodes:root&&splitCount(root.main),controls}))
  if(serialized)console.log('ARTIFACT',JSON.stringify({name:`tip-${mode}.json`,sha256:hash(serialized),gzipBase64:gzipSync(serialized).toString('base64')}))
}
const sourceAfter=sourceHashes()
console.log('POSTFLIGHT',JSON.stringify({inputUnchanged:hash(readFileSync(file))===sourceBefore,sourceUnchanged:JSON.stringify(sourcePins)===JSON.stringify(sourceAfter),hashes:sourceAfter}))
if(hash(readFileSync(file))!==sourceBefore||JSON.stringify(sourcePins)!==JSON.stringify(sourceAfter))throw Error('input or source mutated')
