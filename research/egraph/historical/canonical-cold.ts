// Independent canonical conjunction checker. No transport helper or prover imports.
import {readFileSync} from 'node:fs'
import type {E} from '../../../core/machine.ts'
import {checkCountedLaws,countedObligations,type Instances,type CountCert} from '../../../kernel/kernel.ts'
import {frozenStart,sha} from './start-context.ts'
const c=frozenStart('safety'),bytes=readFileSync(process.argv[2]!),p=JSON.parse(bytes.toString()) as {canonicalInputSha256:string,canonicalMachineSha256:string,canonicalLawsSha256:string,canonicalGoalOrder:string[],instances:Record<string,Instances>,certs:Record<string,CountCert>,records:{name:string,canonicalObligationSha256:string,transformedCertificateSha256:string}[]}
const machine=sha(JSON.stringify(c.input.m)),laws=sha(JSON.stringify(c.input.laws))
if(p.canonicalInputSha256!==c.inputSha256||p.canonicalMachineSha256!==machine||p.canonicalLawsSha256!==laws)throw Error('canonical source pin')
const goals=countedObligations(c.input.m,c.input.laws,p.instances),expected=c.input.laws.flatMap(l=>[l.name+' @start',l.name+' @step'])
if(goals.length!==12||new Set(goals.map(g=>g.goal.name)).size!==12||JSON.stringify(goals.map(g=>g.goal.name))!==JSON.stringify(expected)||JSON.stringify(p.canonicalGoalOrder)!==JSON.stringify(expected)||JSON.stringify(Object.keys(p.certs).sort())!==JSON.stringify([...expected].sort())||JSON.stringify(Object.keys(p.instances).sort())!==JSON.stringify(c.input.laws.map(l=>l.name).sort()))throw Error('incomplete/default conjunction mismatch')
if(p.records.length!==12)throw Error('missing transport record')
for(const g of goals){const r=p.records.find(r=>r.name===g.goal.name);if(r?.canonicalObligationSha256!==sha(JSON.stringify(g))||r.transformedCertificateSha256!==sha(JSON.stringify(p.certs[g.goal.name])))throw Error('transport record mismatch')}
const checked=checkCountedLaws(c.input.m,c.input.laws,p)
const missing={...p,certs:{...p.certs}};delete missing.certs['one value decided @start']
const omissionRejected=!checkCountedLaws(c.input.m,c.input.laws,missing)
const raw=readFileSync('research/egraph/historical/recovery/safety-v11.json'),proposals=readFileSync('research/egraph/historical/recovery/safety-focus-v6.json')
if(sha(raw)!=='ada88e46d2c4139ad33cdb9cd68273ec3765b35874213357273a934d0d9dc727'||sha(proposals)!=='4d7c5adf0d85dd3f32e42ad23b0e1ded8db9b928f44e044e4fd0ae4286891a14')throw Error('negative-control input pin')
const meta=(JSON.parse(raw.toString()) as {metadata:Omit<CountCert,'tree'>&{instances:Instances}}).metadata,q=JSON.parse(proposals.toString()) as {keys:string[],candidates:{binding:Record<string,E>}[]}
const focus={...meta.instances,'one value decided':[...meta.instances['one value decided']!,...q.candidates.flatMap(x=>q.keys.map(k=>x.binding[k]!))]}
const reduced={instances:{...p.instances,'one value decided':focus},certs:{...p.certs,'one value decided @step':{reads:meta.reads,insts:meta.insts,picks:meta.picks,tree:p.certs['one value decided @step']!.tree}}}
const packageRemovalRejected=!checkCountedLaws(c.input.m,c.input.laws,reduced)
if(sha(JSON.stringify(c.input.m))!==machine||sha(JSON.stringify(c.input.laws))!==laws)throw Error('canonical source mutation')
console.log('CANONICAL_COLD',JSON.stringify({checked,omissionRejected,packageRemovalRejected,obligations:goals.length,canonicalMachineSha256:machine,canonicalLawsSha256:laws,proofSha256:sha(bytes),noProverInvoked:true,nativeAdmission:false}))
if(!checked||!omissionRejected||!packageRemovalRejected)process.exitCode=1
