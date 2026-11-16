// Data-only source export. Never invoke proof search or replay the target family.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join,resolve} from 'node:path'
import {pathToFileURL} from 'node:url'
import {createHash} from 'node:crypto'
import {machineLit} from '../../lean-kernel/emit.ts'
import {leanTerms} from '../../lean-kernel/lean-terms.ts'
import {boundOf,witnessesOf} from '../../kernel/kernel.ts'
import type {Machine,Law} from '../../core/machine.ts'
const hash=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
const root=process.cwd(),out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
if(!out)throw Error('output directory required')
mkdirSync(out,{recursive:true})
const raw=readFileSync(join(root,'skt-source-input/models.ts'),'utf8')
const expected='3063304ae3bf8d7c7cc9870c838f7f5da7ab916a96d3729a7ca0b8db5f5b1d76'
if(hash(raw)!==expected)throw Error('pinned p4 source changed')
const common=readFileSync(join(root,'research/protocols/ic3syn/common.ts'))
if(hash(common)!=='d84face9091688872b001f28d0ff31f1180590c57bf944efe6b32168651cd324')throw Error('common source changed')
// Only import locations change; the original source bytes are retained too.
if(raw.split("'../../../core/").length!==3||raw.split("'./common.ts'").length!==2)throw Error('unexpected source imports')
const staged=raw.replaceAll("'../../../core/",`'${root}/core/`).replace("'./common.ts'",`'${root}/research/protocols/ic3syn/common.ts'`)
writeFileSync(join(out,'SktSourceOriginal.ts'),raw)
writeFileSync(join(out,'SktSourceLoaded.ts'),staged)
const {protocols}=await import(pathToFileURL(resolve(out,'SktSourceLoaded.ts')).href)
const p=protocols.find((p:{id:string})=>p.id==='sharded_kv')
if(!p)throw Error('missing source protocol')
const broken=process.argv.includes('--broken-source'),r=p.make(broken?p.bug:undefined)
const m:Machine=r.machine,laws:Law[]=p.laws(r),law=laws[0]!
if(laws.length!==1||!law.forall||law.keys?.length!==4||law.some||law.ex||Object.keys(m.sums??{}).length||Object.keys(m.counts??{}).length||m.history)throw Error('unsupported source')
if(JSON.stringify(m.params)!==JSON.stringify(['nodes','keys','values']))throw Error('source parameter drift')
const q=m.step.flags?.unowned,each=m.step.maps?.TransferMsg
if(!q||q.op!=='all'||boundOf(q).length!==1||!each||!('each' in each))throw Error('unexpected source binders')
const ws=witnessesOf('unowned',q)
if(ws.length!==1)throw Error('unexpected witness arity')
const vars=Array.from({length:44},(_,i)=>'unused$'+i)
for(const [i,name] of [[0,'op'],[1,'n'],[2,'k'],[3,'v'],[4,'n2'],[5,'started'],[8,law.forall],...law.keys.map((k,i)=>[9+i,k]),[31,'?unowned'],[32,'?allOwned'],[33,'?owns'],[34,'?starts'],[35,'?reshards'],[36,'?receives'],[37,'?puts'],[38,ws[0]!],[39,boundOf(q)[0]!],[40,each.each],[41,'nodes'],[42,'keys'],[43,'values']] as [number,string][])vars[i]=name
if(new Set(vars).size!==vars.length)throw Error('basis alias')
const maps=['Table','Owner','TransferMsg','Owned'],t=leanTerms(vars,maps,'skt source')
const ix=(n:string)=>{const i=vars.indexOf(n);if(i<0)throw Error('unbound source variable '+n);return i}
const mx=(n:string)=>{const i=maps.indexOf(n);if(i<0)throw Error('unbound source map '+n);return i}
const text=`import Sets\nopen Kern\n-- Exact pinned source AST in an explicit retained-compatible basis.\ndef skt_source : SMachine := ${machineLit(m,t,ix,mx)}\ndef skt_source_law : MLaw := ⟨${t.c(law.holds)}, some ${ix(law.forall)}⟩\ndef skt_source_keys : List Nat := [${law.keys.map(ix).join(',')}]\n`
writeFileSync(join(out,'SktSourceDefs.lean'),text)
writeFileSync(join(out,'SOURCE-DATA.json'),JSON.stringify({protocol:p.id,brokenSource:broken,machine:m,laws,vars,maps,modelSHA256:hash(raw),loadedSourceSHA256:hash(staged),frontendSHA256:hash(readFileSync(join(root,'core/dsl.ts'))),commonSHA256:hash(common),sourceSHA256:hash(JSON.stringify({machine:m,laws})),leanSHA256:hash(text),newProofSearches:0,targetFamilyReplays:0},null,2)+'\n')
console.log('source emitted; no proof claim')
