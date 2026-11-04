// Certificate-only retention of v14 conditional branches; never used by proof search.
import {readFileSync} from 'node:fs'
import {gunzipSync,gzipSync} from 'node:zlib'
import {check,countedObligations,mcGoal,type Path,type Tree} from '../../../kernel/kernel.ts'
import type {E} from '../../../core/machine.ts'
import {safetyContext,sha} from './safety-context.ts'
const c=safetyContext(),candidateBytes=readFileSync('research/egraph/historical/recovery/safety-focus-v6.json')
if(sha(candidateBytes)!=='4d7c5adf0d85dd3f32e42ad23b0e1ded8db9b928f44e044e4fd0ae4286891a14')throw Error('candidate pin')
const proposal=JSON.parse(candidateBytes.toString()) as {keys:string[],candidates:{binding:Record<string,E>}[]}
const instances={...c.metadata.instances,[c.input.law.name]:[...c.metadata.instances[c.input.law.name]!,...proposal.candidates.flatMap(p=>proposal.keys.map(k=>p.binding[k]!))]}
const base=countedObligations(c.input.m,c.input.laws,{[c.input.law.name]:instances},c.input.laws.findIndex(l=>l.name===c.input.law.name)).find(x=>x.goal.name.endsWith('@step'))!
const goal=mcGoal(base.goal.hyps,base.decls,c.metadata)!;goal.name=c.original.name
const receipt=JSON.parse(readFileSync('research/egraph/historical/recovery/safety-v14-branches.json','utf8')) as {source:Record<string,string>,artifacts:{kind:string,path:string,sha256:string,gzipBase64:string}[]}
if(sha(readFileSync('kernel/kernel.ts'))!==receipt.source['kernel/kernel.ts'])throw Error('kernel drift')
for(const artifact of receipt.artifacts){
  if(artifact.kind!=='conditional-branch')throw Error('unexpected artifact')
  const bytes=gunzipSync(Buffer.from(artifact.gzipBase64,'base64'));if(sha(bytes)!==artifact.sha256)throw Error('branch pin')
  const branch=JSON.parse(bytes.toString()) as {goalSha256:string,contextSha256:string,path:[string,Path extends Map<string,infer V>?V:never][],tree:Tree}
  if(branch.goalSha256!==c.goalSha256||branch.contextSha256!==sha(JSON.stringify(goal)))throw Error('exact branch goal mismatch')
  if(!check(goal,branch.tree,new Map(branch.path)))throw Error('conditional branch rejected')
  const packet=JSON.stringify({kind:'conditional-branch-only',origin:'20261104-125543-c8mztn',source:receipt.source,inputSha256:sha(readFileSync('research/egraph/historical/inputs/m2/one-value-decided.json.gz')),metadataSha256:sha(readFileSync('research/egraph/historical/recovery/safety-v11.json')),candidateSha256:sha(candidateBytes),sourceGoalSha256:c.goalSha256,goal,instances,counts:c.metadata,path:branch.path,tree:branch.tree,completeSafetyProof:false,reusedBySearch:false})
  console.log('CONDITIONAL_BUNDLE',JSON.stringify({path:artifact.path,sha256:sha(packet),gzipBase64:gzipSync(packet).toString('base64')}))
}
