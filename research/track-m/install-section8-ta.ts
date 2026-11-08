// Research-only capture hooks. Never run in a persistent or non-Linux checkout.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const closure='core/count-recovery/derivability-closure.ts';let source=readFileSync(closure,'utf8')
const marker='  const extended=lemmaPath(available.map(s=>s.lemma),scope)'
if(source.split(marker).length!==2)throw new Error('missing unique finish capture anchor')
source=source.replace(marker,"  __ta.capture({m,ds,g,cert,scope,numeric,available,saved,q,source})\n"+marker)
writeFileSync(closure,"import {ta as __ta} from '../../research/track-m/section8-ta-observer.ts'\n"+source)
const probe='research/track-m/active-source-probe.ts';source=readFileSync(probe,'utf8')
const replace=(a:string,b:string)=>{if(source.split(a).length!==2)throw new Error('missing probe anchor '+a);source=source.replace(a,b)}
replace('let goal=makeGoal();const memo=sourceProofMemo(m,law.name)',"const __taFull={...packet.cert,insts:packet.cert.insts.slice()}\nlet goal=makeGoal();const memo=sourceProofMemo(m,law.name)")
replace(' const events:any[]=[],suggestions:object[]='," __ta.begin(law.name,selection,__taFull)\n const events:any[]=[],suggestions:object[]=")
replace(' const detailResult=detail?.capture()'," __ta.finish()\n const detailResult=detail?.capture()")
writeFileSync(probe,"import {ta as __ta} from './section8-ta-observer.ts'\n"+source)
console.log(JSON.stringify({installed:'section8-ta-capture',files:[closure,probe]}))
