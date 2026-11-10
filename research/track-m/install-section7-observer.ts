// Install observation-only hooks in the disposable proof source.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.platform!=='linux'||process.env.TRACK_M_DISPOSABLE_PROFILE!=='1')throw new Error('disposable Linux snapshot required')
const file='core/count-recovery/derivability-closure.ts';let s=readFileSync(file,'utf8')
const replace=(a:string,b:string)=>{if(s.split(a).length!==2)throw new Error('missing unique T0 hook '+a);s=s.replace(a,b)}
replace('    const reused=models.some(savedModel=>{',"    __section7.attempt(part,path,index,scopes.indexOf(scope),inst.wit)\n    const reused=models.some(savedModel=>{")
replace('     return brokenOf(renamed)(savedModel.model).length===0',"     const valid=brokenOf(renamed)(savedModel.model).length===0\n     if(valid)__section7.reuse(part,renamed,path,index,scopes.indexOf(scope),inst.wit,savedModel.witness,savedModel.model)\n     return valid")
s="import {section7 as __section7} from '../../research/track-m/section7-observer.ts'\n"+s
writeFileSync(file,s)
