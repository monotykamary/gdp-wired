// Capture the actual original entry's generation result, then stop before proof.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
const source='core/counts.ts',old="countsDump.on?.({phase: 'candidates', machine: m, laws: set})",text=readFileSync(source,'utf8')
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1'||text.split(old).length!==2)throw Error('disposable original source required')
writeFileSync(source,text.replace(old,"countsDump.on?.({phase: 'candidates', machine: m, laws: set, caller, support})"))
const {countsDump}=await import('../../core/counts.ts'),{proveRule}=await import('../../core/dsl.ts'),{protocols}=await import('../protocols/ic3syn/models.ts')
const out=process.argv[2];if(!out)throw Error('OUTPUT required')
const stop={},p=protocols.find(p=>p.id==='mldr')!,r=p.make();let captured=false
countsDump.on=e=>{const v=e as any;if(v.phase!=='candidates')return;const laws=v.laws,targets={overlap:laws.findIndex((l:any)=>l.name.includes('stored guard')&&l.name.endsWith('or disabled/0'))};if(targets.overlap<0)throw Error('missing actual overlap target')
 const data={conditional:true,source:'original proveRule/run.ts generation callback before admission',generatorOnly:true,suppliedLaws:[],m:v.machine,laws,caller:v.caller.map((l:any)=>laws.indexOf(l)),support:[...v.support].map((l:any)=>laws.indexOf(l)),targets},json=JSON.stringify(data)
 writeFileSync(out,json);console.log(JSON.stringify({captured:true,actualOriginal:true,laws:laws.length,targets,sha256:createHash('sha256').update(json).digest('hex')}));captured=true;throw stop}
try{proveRule(r,p.laws(r),{search:{ms:60000}})}catch(e){if(e!==stop)throw e}finally{countsDump.on=undefined}
if(!captured)throw Error('original entry did not produce family')
