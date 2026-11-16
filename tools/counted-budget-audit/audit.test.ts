import {expect,test} from 'bun:test'
import {mkdtempSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {audit,parseInventory} from './audit.ts'
import {migrationPlan} from './codemod.ts'
const header='file\tcallLine\tcallee\tbudgetMs\tclockDomain\tquickShard\tsuiteJobs\tprofileClock\tprofileConflict\tcertainty\ttestName\timportSource\tbudgetGrants'
const row=(callee:string,grants:object[]=[],module='./dsl.ts',testName='<file-helper>')=>parseInventory(header+'\n'+['fixture.ts','1',callee,'10','unknown','null','[]','','false','source',testName,JSON.stringify({name:callee,module}),JSON.stringify(grants)].join('\t'))
async function fixture(source:string,callee:string,grants:object[]=[],module?:string,testName?:string){
 const root=mkdtempSync(join(tmpdir(),'budget-audit-'))
 try{writeFileSync(join(root,'fixture.ts'),source);return (await audit(root,row(callee,grants,module,testName)))[0]!}
 finally{rmSync(root,{recursive:true,force:true})}
}
test('inventory parser rejects shifted TSV rows',()=>expect(()=>parseInventory('file\tcallLine\n')).toThrow('unexpected inventory TSV header'))
test('all 509 original candidates remain present with stable IDs and original grants',async()=>{
 const rows=parseInventory(await Bun.file(join(import.meta.dir,'0501-BUDGET-INVENTORY.tsv')).text())
 expect(rows).toHaveLength(509)
 const entries=await audit('/definitely-not-a-checkout',rows)
 expect(new Set(entries.map(e=>e.id)).size).toBe(509)
 expect(entries.every(e=>e.classification==='needs-reviewed-support')).toBe(true)
 expect(entries.map(e=>e.grants)).toEqual(rows.map(r=>JSON.parse(r.budgetGrants)))
})
test('missing source never authenticates an old work grant',async()=>{
 const entries=await audit('/definitely-not-a-checkout',row('proveRule',[{path:'search.work',expression:'100',literal:100}]))
 expect(entries[0]).toMatchObject({classification:'needs-reviewed-support',grants:[{path:'search.work'}]})
})
test('empty recorded grants do not turn internal withWall into a watchdog',async()=>{
 expect(await fixture('withWall(clock()+1000,()=>proveRule(r,ls,{search:{work:100}}))','withWall')).toMatchObject({classification:'needs-reviewed-support',ast:{properties:[]}})
})
test('native child process timeouts remain watchdogs, not work conversions',async()=>{
 expect(await fixture('spawnSync("java",[],{timeout:5000})','spawnSync',[{path:'timeout',expression:'5000',literal:5000}],'node:child_process')).toMatchObject({classification:'watchdog-only'})
})
test('only direct reviewed work grants authenticate conversion; mixed options block',async()=>{
 expect(await fixture('proveRule(r,ls,{search:{work:123}})','proveRule')).toMatchObject({classification:'converted'})
 expect(await fixture('proveRule(r,ls,{search:{work:123,ms:123}})','proveRule')).toMatchObject({classification:'needs-reviewed-support'})
 expect(await fixture('helper(()=>proveRule(r,ls,{search:{work:123}}))','helper')).toMatchObject({classification:'needs-reviewed-support',ast:{properties:[]}})
})
test('reviewed codemod never invents work from elapsed values or missing measurements',async()=>{
 const entry=await fixture('proveRule(r,ls,{search:{work:123}})','proveRule')
 const reviewed={id:entry.id,work:123,observedMaximumWork:100,batch:'native-batch',test:entry.file,reason:'measured'}
 expect(migrationPlan([entry],[reviewed])[0]).toMatchObject({action:'verified-applied',replacement:{units:123},evidence:{observedMaximumWork:100}})
 expect(migrationPlan([entry],[])[0]).toMatchObject({action:'blocked'})
 expect(()=>migrationPlan([entry],[{...reviewed,work:99}])).toThrow('invalid counted baseline')
 expect(()=>migrationPlan([entry],[{...reviewed,id:'missing'}])).toThrow('missing candidate')
})

test('a unique named-test anchor tolerates line drift but ambiguous helpers do not',async()=>{
 const source='\n'.repeat(30)+'test("fixture",()=>proveRule(r,ls,{search:{work:123}}))'
 expect(await fixture(source,'proveRule',[],'./dsl.ts','fixture')).toMatchObject({classification:'converted',ast:{line:31,resolved:true}})
 expect(await fixture(source,'proveRule')).toMatchObject({classification:'needs-reviewed-support',ast:{resolved:false}})
})
