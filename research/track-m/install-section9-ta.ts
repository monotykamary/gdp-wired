// Measurement-only live hooks; the production worktree is never modified.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const file='core/count-recovery/derivability-closure.ts';let s=readFileSync(file,'utf8')
const marker='  const extended=lemmaPath(available.map(s=>s.lemma),scope)'
if(s.split(marker).length!==2)throw new Error('missing unique live capture anchor')
const capture="  __s9.capture({m,ds,g,cert,scope,numeric,available,saved,q,source,scopesFor,numericFor:(p,extra)=>{const a=active([...saved,...extra],p);return {name:g.name,hyps:[...abstracted.flatMap(c=>piecesAt(c,p)).filter(c=>pure(c,p)),...countBindingsAt(cert.reads,p),...a.map(s=>s.good).filter(c=>pure(c,p))]}}})\n"
s=s.replace(marker,capture+marker)
writeFileSync(file,"import {s9 as __s9} from '../../research/track-m/section9-guard-observer.ts'\n"+s)
const probe='research/track-m/active-source-probe.ts';s=readFileSync(probe,'utf8')
const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('probe anchor '+a);s=s.replace(a,b)}
replace('let goal=makeGoal();const memo=sourceProofMemo(m,law.name)',"const __s9Full={...packet.cert,insts:packet.cert.insts.slice()}\nlet goal=makeGoal();const memo=sourceProofMemo(m,law.name)")
replace(' const events:any[]=[],suggestions:object[]='," __s9.begin(law.name,selection,__s9Full)\n const events:any[]=[],suggestions:object[]=")
replace(' const detailResult=detail?.capture()'," __s9.finish()\n const detailResult=detail?.capture()")
writeFileSync(probe,"import {s9 as __s9} from './section9-guard-observer.ts'\n"+s)
console.log(JSON.stringify({installed:'section9-live-observer',files:[file,probe],productionStrategyChanged:false}))
