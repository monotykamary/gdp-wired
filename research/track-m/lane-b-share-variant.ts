// Section 15.1 remains research-only here; Lane A owns its production implementation.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('disposable copy required')
const mode=process.argv[2];if(!['before','after'].includes(mode!))throw Error('before|after required')
if(mode==='after'){
 const p='core/counts.ts';let s=readFileSync(p,'utf8')
 const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw Error('share anchor changed');s=s.replace(a,b)}
 replace("import {supportBudget} from './support-budget.ts'","import {supportBudget} from './support-budget.ts'\nimport {supportShare} from '../research/track-m/section15-share.ts'")
 replace('      const failed = new Set<string>(), proofs = new Map<string, Proof>(), share = (until - clock()) / Math.max(1, set.filter(l => !kept.has(l.name) && !carried.has(l.name)).length)','      const failed = new Set<string>(), proofs = new Map<string, Proof>()\n      let untried = set.filter(l => !kept.has(l.name) && !carried.has(l.name)).length')
 replace('        const was = carried.get(law.name)','        const was = carried.get(law.name), share = supportShare(until - clock(), untried)\n        if (!was) untried--')
 writeFileSync(p,s)
}
