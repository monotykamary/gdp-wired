// Certificate-only preservation audit. No prover, translator or production search imports.
import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {Machine,Law} from '../../../core/machine.ts'
import {countedObligations,checkMC,type Instances,type CountCert} from '../../../kernel/kernel.ts'
import {refuseCyclic,type Cyclic} from '../../../kernel/cyclic.ts'
const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
const sourcePaths=['kernel/kernel.ts','kernel/cyclic.ts','core/check.ts','core/solver.ts'],source=Object.fromEntries(sourcePaths.map(p=>[p,sha(readFileSync(p))]))
if(source['kernel/kernel.ts']!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel pin')
const mode=process.argv[2],id=process.argv[3]!
if(mode==='positive'){
  const dir='research/egraph/historical/inputs/m2/positives'
  const manifest=JSON.parse(readFileSync(dir+'/manifest.json','utf8')) as {artifacts:{id:string,file:string,rawSha256:string,gzipSha256:string,expected:{focus:string,inputSha256:string,proofSha256:string,replay:{name:string,goalSha256:string}[]}}[]}
  const a=manifest.artifacts.find(a=>a.id===id);if(!a)throw Error('unknown positive')
  const compressed=readFileSync(dir+'/'+a.file),bytes=gunzipSync(compressed)
  if(sha(compressed)!==a.gzipSha256||sha(bytes)!==a.rawSha256)throw Error('attempt pin')
  const e=JSON.parse(bytes.toString()) as {m:Machine,laws:Law[],law:Law,proof:{instances:Instances,certs:Record<string,CountCert>}}
  if(e.laws.length!==6||e.laws[0]!.name!==a.expected.focus||e.law.name!==a.expected.focus||sha(JSON.stringify([e.m,e.laws]))!==a.expected.inputSha256||sha(JSON.stringify(e.proof))!==a.expected.proofSha256)throw Error('historical focus/source/proof mismatch')
  const goals=countedObligations(e.m,e.laws,{[e.law.name]:e.proof.instances},0),text=JSON.stringify([e.m,e.laws])
  if(goals.length!==2)throw Error('missing start/step')
  const replay=goals.map(({goal,decls})=>{
    const cert=e.proof.certs[goal.name],expected=a.expected.replay.find(g=>g.name===goal.name),goalSha256=sha(JSON.stringify({goal,decls}))
    if(!cert||expected?.goalSha256!==goalSha256)throw Error('goal pin')
    const fresh=cert.insts.every(i=>!text.includes(JSON.stringify(i.wit))),checked=fresh&&checkMC(goal.hyps,decls,cert)
    if(!checked)throw Error('positive certificate rejected')
    return {name:goal.name,goalSha256,checked,fresh}
  })
  const canonical=JSON.parse(gunzipSync(readFileSync('research/egraph/historical/inputs/m2/one-value-decided.json.gz')).toString()) as {m:Machine,laws:Law[]}
  const laws=(ls:Law[])=>JSON.stringify([...ls].sort((a,b)=>a.name.localeCompare(b.name)))
  console.log('PRESERVED_POSITIVE',JSON.stringify({id,focus:e.law.name,source,attemptSha256:a.rawSha256,proofSha256:a.expected.proofSha256,replay,machineMatchesSafety:JSON.stringify(e.m)===JSON.stringify(canonical.m),lawSetMatchesSafety:laws(e.laws)===laws(canonical.laws),noProverInvoked:true}))
  if(sha(readFileSync(dir+'/'+a.file))!==a.gzipSha256)throw Error('attempt changed')
}else if(mode==='tip'){
  const expected:Record<string,string>={'tip-enabled-no-hints.json':'d6f0f654e62f7b9c19d17f0d1ab60dacf2b07063b72c64482ba84d7c2b367398','tip-enabled.json':'492b6821cea7dde59fd9837858a36789955358021aefac50b38cc73cc9d92773'}
  const path='research/egraph/historical/proofs/'+id,bytes=readFileSync(path)
  if(!expected[id]||sha(bytes)!==expected[id])throw Error('TIP proof pin')
  const statement='research/egraph/historical/inputs/gdp-wired-laneRL/research/frontier2/tasks/tip/prod/lemma_09.smt2'
  if(sha(readFileSync(statement))!=='225ccffbf1a98c7334f6be2d86e13efe07ce707e1fcaa8b3b5dd6b4869654888')throw Error('TIP statement pin')
  const proof=JSON.parse(bytes.toString()) as Cyclic,root=proof.nodes.at(-1)!
  if(proof.nodes.length!==9||root.uses.length!==2||root.hyps.length!==0||refuseCyclic(proof)!==undefined)throw Error('TIP full graph rejected')
  const controls:Record<string,string|undefined>={}
  for(const [i,use]of root.uses.entries()){
    const p=structuredClone(proof);p.nodes.at(-1)!.uses=p.nodes.at(-1)!.uses.filter(u=>u.node!==use.node)
    controls[`remove-root-use-${i}`]=refuseCyclic(p)
  }
  const snoc=root.uses[1]!.node,bad=structuredClone(proof);bad.nodes[snoc]!.main={leaf:[]};controls['corrupt-snoc']=refuseCyclic(bad)
  const rank=structuredClone(proof);rank.nodes.at(-1)!.rank=rank.nodes[snoc]!.rank;controls['nondecreasing-rank']=refuseCyclic(rank)
  if(Object.values(controls).some(x=>x===undefined))throw Error('TIP negative control accepted')
  console.log('PRESERVED_TIP',JSON.stringify({id,source,proofSha256:sha(bytes),nodes:proof.nodes.length,rootUses:root.uses.length,rootConclSha256:sha(JSON.stringify(root.concl)),checked:true,controls,noProverInvoked:true}))
  if(sha(readFileSync(path))!==expected[id])throw Error('TIP proof changed')
}else throw Error('unknown preservation mode')
for(const p of sourcePaths)if(sha(readFileSync(p))!==source[p])throw Error('source changed')
