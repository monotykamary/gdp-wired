#!/usr/bin/env bun
/** Dry-run reviewed codemod: no generic ms->work replacement and no source writes. */
import {createHash} from 'node:crypto'
import {join} from 'node:path'
import {audit,parseInventory,type Entry} from './audit.ts'
export type Reviewed = {id:string,work:number,observedMaximumWork:number,batch:string,test:string,reason:string}
export function migrationPlan(entries:Entry[],reviewed:Reviewed[]){
 const byId=new Map(reviewed.map(row=>[row.id,row]))
 if(byId.size!==reviewed.length)throw Error('duplicate reviewed inventory IDs')
 for(const review of reviewed){
  if(!entries.some(entry=>entry.id===review.id))throw Error(`review refers to missing candidate ${review.id}`)
  if(!Number.isFinite(review.work)||!Number.isFinite(review.observedMaximumWork)||review.work<review.observedMaximumWork||review.observedMaximumWork<0||!review.batch)throw Error(`invalid counted baseline for ${review.id}`)
 }
 return entries.map(entry=>{
  const review=byId.get(entry.id)
  if(!review)return {id:entry.id,file:entry.file,classification:entry.classification,action:entry.classification==='watchdog-only'?'preserve-watchdog':'blocked',reason:entry.reason,originalGrants:entry.grants}
  if(review.test!==entry.file)throw Error(`review file mismatch for ${entry.id}`)
  const grant=entry.ast.properties.find(p=>p.path==='work'||p.path==='search.work')
  const actual=grant?Number(grant.expression.replaceAll('_','')):undefined
  const applied=entry.classification==='converted'&&actual===review.work
  return {id:entry.id,file:entry.file,line:entry.ast.line,classification:entry.classification,action:applied?'verified-applied':entry.ast.resolved?'reviewed-edit-plan':'blocked',reason:review.reason,originalGrants:entry.grants,
   replacement:{path:entry.callee==='proveRule'||entry.callee==='proveSteps'?'search.work':'work',units:review.work},
   evidence:{observedMaximumWork:review.observedMaximumWork,batch:review.batch},
   ...(applied?{}:{blocker:entry.ast.resolved?'Source change requires explicit option and wrapper review; this tool does not write source':entry.reason})}
 })
}
async function main(){
 const [inventory,root,output]=Bun.argv.slice(2)
 if(!inventory||!root||!output)throw Error('usage: bun codemod.ts INVENTORY.tsv SOURCE_ROOT PLAN.json (dry-run only)')
 const text=await Bun.file(inventory).text(),rows=parseInventory(text),entries=await audit(root,rows)
 const reviews=await Bun.file(join(import.meta.dir,'reviewed-migrations.json')).json() as {migrations:Reviewed[]}
 const files=[...new Set(entries.map(e=>e.file))],sourceHashes:Record<string,string>={}
 for(const file of files){const source=Bun.file(join(root,file));if(await source.exists())sourceHashes[file]=createHash('sha256').update(await source.bytes()).digest('hex')}
 const candidates=migrationPlan(entries,reviews.migrations)
 await Bun.write(output,JSON.stringify({schema:1,mode:'dry-run-only',inventorySha256:createHash('sha256').update(text).digest('hex'),sourceHashes,candidates},null,2)+'\n')
 console.log(JSON.stringify({candidates:candidates.length,reviewed:reviews.migrations.length,verified:candidates.filter(c=>c.action==='verified-applied').length,blocked:candidates.filter(c=>c.action==='blocked').length}))
}
if(import.meta.main)await main()
