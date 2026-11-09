// Observation only: no skipped check, changed answer, or final-check deferral.
import {readFileSync,writeFileSync} from 'node:fs'
import {createHash} from 'node:crypto'
if(process.platform!=='linux'||process.env.LAB_DISPOSABLE!=='1')throw Error('disposable Linux copy required')
const changes:{path:string,before:string,after:string}[]=[],hash=(s:string)=>createHash('sha256').update(s).digest('hex')
const replace=(s:string,a:string,b:string)=>{if(s.split(a).length!==2)throw Error('check-profile anchor '+a);return s.replace(a,b)}
const change=(path:string,transform:(s:string)=>string)=>{const before=readFileSync(path,'utf8'),after=transform(before);writeFileSync(path,after);changes.push({path,before:hash(before),after:hash(after)})}
const wrap=(name:string,raw:string,label:string)=>`\nfunction ${name}(...args:Parameters<typeof ${raw}>):ReturnType<typeof ${raw}>{return profileCheck('${label}',()=>${raw}(...args))}\n`
change('core/counts.ts',s=>"import {profileCheck} from '../research/track-m/check-cost-profile.ts'\n"+replace(s,'checkCountedLaws, checkMC,','checkCountedLaws as __rawFamilyCheck, checkMC as __rawCheckMC,')+wrap('checkMC','__rawCheckMC','counts.checkMC')+wrap('checkCountedLaws','__rawFamilyCheck','counts.finalFamily'))
change('core/count-cases.ts',s=>"import {profileCheck} from '../research/track-m/check-cost-profile.ts'\n"+replace(s,'checkMC,linear','checkMC as __rawCaseCheck,linear')+wrap('checkMC','__rawCaseCheck','cases.checkMC'))
change('core/count-recovery/conditional-proof.ts',s=>"import {profileCheck} from '../../research/track-m/check-cost-profile.ts'\n"+replace(replace(s,'function independent(','function __rawIndependent('),'function retarget(','function __rawRetarget(')+wrap('independent','__rawIndependent','conditional.independent')+wrap('retarget','__rawRetarget','conditional.retarget'))
change('core/count-recovery/conditional-check-cache.ts',s=>"import {profileCheck} from '../../research/track-m/check-cost-profile.ts'\n"+replace(s,'export function slicedCheck(','function __rawSlicedCheck(')+'\nexport '+wrap('slicedCheck','__rawSlicedCheck','conditional.slicedCheck').trimStart())
change('research/track-m/lane-b-cost.ts',s=>"import {profileCheck} from './check-cost-profile.ts'\n"+replace(s,'import {checkMC,columnTerm,','import {checkMC as __rawWorkerCheck,columnTerm,')+wrap('checkMC','__rawWorkerCheck','worker.finalCheckMC'))
console.log(JSON.stringify({observationOnly:true,finalCheckUnchanged:true,changes}))
