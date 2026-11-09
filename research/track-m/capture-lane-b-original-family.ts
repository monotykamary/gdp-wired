// Preload of the unchanged original run.ts entrypoint, not a surrogate generator.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {countsDump} from '../../core/counts.ts'
const dir=process.env.ORIGINAL_FAMILY_OUT,frozenFile=process.env.FROZEN_FAMILY
if(!dir||!frozenFile)throw Error('ORIGINAL_FAMILY_OUT and FROZEN_FAMILY required')
const frozenBytes=readFileSync(frozenFile),frozen=JSON.parse(frozenBytes.toString()),hash=(x:string|Buffer)=>createHash('sha256').update(x).digest('hex'),started=performance.now()
mkdirSync(dir,{recursive:true})
countsDump.on=e=>{
 const v=e as any;if(v.phase!=='original-family')return
 const laws:any[]=v.laws,candidateLaws:any[]=v.candidateLaws,indices=(xs:any[])=>xs.map(l=>laws.indexOf(l)).filter(i=>i>=0),targets:Record<string,number>={},missingTargets:string[]=[],targetComparisons:Record<string,unknown>={}
 for(const tag of ['p1','rows','star']){
  const expected=frozen.laws[frozen.targets[tag]],hits=laws.flatMap((l,i)=>l.name===expected.name?[i]:[])
  if(hits.length>1)throw Error('ambiguous original target '+tag)
  if(!hits.length){missingTargets.push(tag);continue}
  targets[tag]=hits[0]!;targetComparisons[tag]={name:expected.name,sameBody:JSON.stringify(laws[hits[0]!])===JSON.stringify(expected)}
 }
 const names=new Set(laws.map(l=>l.name)),frozenNames=new Set<string>(frozen.laws.map((l:any)=>l.name)),candidateNames=new Set(candidateLaws.map(l=>l.name)),comparison={frozenSha256:hash(frozenBytes),frozenSize:frozen.laws.length,candidateSize:candidateLaws.length,admissionSize:laws.length,missingFromAdmission:frozen.laws.filter((l:any)=>!names.has(l.name)).map((l:any)=>l.name),missingFromCandidates:frozen.laws.filter((l:any)=>!candidateNames.has(l.name)).map((l:any)=>l.name),addedInAdmission:laws.filter(l=>!frozenNames.has(l.name)).map(l=>l.name),machineSame:JSON.stringify(v.machine)===JSON.stringify(frozen.m),targetComparisons}
 const payload={conditional:true,source:'original run.ts post-finite admission context',originalHarness:true,generatorOnly:true,suppliedLaws:[],missingTargets,m:v.machine,laws,caller:indices(v.caller),support:indices(v.support),targets,generationWallMs:performance.now()-started,originalComparison:comparison}
 if(payload.caller.length!==v.caller.length)throw Error('original admission lost a caller')
 const text=JSON.stringify(payload);writeFileSync(join(dir,'family.json'),text);writeFileSync(join(dir,'family-comparison.json'),JSON.stringify({...comparison,familySha256:hash(text),missingTargets},null,2)+'\n');writeFileSync(join(dir,'owned-targets.txt'),Object.keys(targets).join('\n')+'\n')
 console.log(JSON.stringify({phase:'original-family-captured',...comparison,missingTargets,familySha256:hash(text)}))
 throw Error('LANE_B_ORIGINAL_FAMILY_CAPTURED')
}
