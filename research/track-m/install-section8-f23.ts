// T-F2/F3 only; preserve the final kernel check and all source-query budgets.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const file='core/count-recovery/conditional-proof.ts';let s=readFileSync(file,'utf8')
const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('nonunique F23 marker: '+a);s=s.replace(a,b)}
replace("if ('leaf' in t) return check(goal, t, lemmaPath(context.lemmas, p)) && alive(until)","if ('leaf' in t) return slicedCheck(goal, t, lemmaPath(context.lemmas, p)) && alive(until)")
replace('if (!local || !check(local, lemma.tree, proofPath(lemma.when, lemma.cut))) return false','if (!local || !memoIndependent(goal, lemma,()=>check(local, lemma.tree, proofPath(lemma.when, lemma.cut)))) return false')
replace('const out: LemmaCut[] = [], target = new Map<string, number>()\n  for (const [i, hyp] of to.hyps.entries()) {\n    if (!alive(until)) return undefined\n    const key = JSON.stringify(hyp)\n    if (!target.has(key)) target.set(key, i)\n  }','const out: LemmaCut[] = [], target = targetIndex(to)')
const functionStart=Math.max(s.indexOf('function retarget('),s.indexOf('function __s7Original_retarget('))
if(functionStart<0)throw new Error('missing retarget declaration')
const start=s.indexOf('  for (const lemma of lemmas) {',functionStart),end=s.indexOf('\n  return alive(until) ? out : undefined',start)
if(start<0||end<0)throw new Error('missing retarget loop')
const body=s.slice(start,end)
if(!body.endsWith('\n  }'))throw new Error('unexpected retarget loop')
const inner=body.slice(body.indexOf('{')+1,-4).replace('out.push({when, cut: lemma.cut, tree, slice})','return {when, cut: lemma.cut, tree, slice}')
s=s.slice(0,start)+`  for (const lemma of lemmas) {\n    if (!alive(until)) return undefined\n    const next=memoRetarget(from,to,lemma,scope,onlyMissing,()=>{${inner}\n    })\n    if(!next||!alive(until))return undefined\n    out.push(next)\n  }`+s.slice(end)
s="import {slicedCheck,memoIndependent,memoRetarget,targetIndex} from '../../research/track-m/section8-f23.ts'\n"+s
writeFileSync(file,s)
const runner='research/track-m/run-phase-census.ts';writeFileSync(runner,readFileSync(runner,'utf8')+"\nconsole.log(JSON.stringify({test:'T-F23-stats',...(await import('./section8-f23.ts')).f23Stats}))\n")
console.log(JSON.stringify({installed:'T-F2/F3',kernelChanged:false,harnessFinalCheckChanged:false}))
