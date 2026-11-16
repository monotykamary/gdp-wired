// Data-only export of the actual symbolic protocol. No prove/search entrypoint.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
import {protocols} from '../protocols/ic3syn/models.ts'
import {machineLit} from '../../lean-kernel/emit.ts'
import {leanTerms} from '../../lean-kernel/lean-terms.ts'
const p=protocols.find(p=>p.id==='simple_decentralized_lock')!
const brokenSource=process.argv.includes('--broken-source')
const r=p.make(brokenSource?p.bug:undefined),m=r.machine,laws=p.laws(r),law=laws[0]!
if(laws.length!==1||!law.forall||law.keys?.length!==1||law.some||law.ex||Object.keys(m.sums??{}).length||Object.keys(m.counts??{}).length||m.history)throw Error('unsupported SDL source')
const each=m.step.maps?.HasLock
if(!each||!('each' in each))throw Error('missing HasLock whole-map update')
const vars=Array.from({length:28},(_,i)=>'unused$'+i)
for(const [i,name]of [[0,'op'],[1,'src'],[2,'dst'],[3,'started'],[4,'sum$HasLock'],[5,'sum$Message'],[8,law.forall],[9,law.keys[0]!],[15,'?inits'],[16,'?sends'],[17,'?recvs'],[24,each.each],[27,'size']] as const)vars[i]=name
if(new Set(vars).size!==vars.length)throw Error('basis alias')
const maps=['Message','HasLock'],t=leanTerms(vars,maps,'sdl source'),ix=(n:string)=>{const i=vars.indexOf(n);if(i<0)throw Error('unbound source variable '+n);return i},mx=(n:string)=>{const i=maps.indexOf(n);if(i<0)throw Error('unbound source map '+n);return i}
const text=`import Sets\nopen Kern\n-- Exact source AST, emitted in the retained basis; no proof asserted.\ndef sdl_source : SMachine := ${machineLit(m,t,ix,mx)}\ndef sdl_source_law : MLaw := ⟨${t.c(law.holds)}, some ${ix(law.forall)}⟩\ndef sdl_source_keys : List Nat := [${law.keys.map(ix).join(',')}]\n`
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!
mkdirSync(out,{recursive:true});writeFileSync(join(out,'SdlSourceDefs.lean'),text)
const hash=(s:string|Buffer)=>createHash('sha256').update(s).digest('hex')
writeFileSync(join(out,'SOURCE-DATA.json'),JSON.stringify({protocol:p.id,brokenSource,machine:m,laws,vars,maps,modelSHA256:hash(readFileSync('research/protocols/ic3syn/models.ts')),sourceSHA256:hash(JSON.stringify({machine:m,laws})),leanSHA256:hash(text),newProofSearches:0},null,2)+'\n')
