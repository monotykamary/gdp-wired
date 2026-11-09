// Disposable experiment only: undo precisely the active-leaf slice, keeping telemetry.
import {readFileSync,writeFileSync} from 'node:fs'
if(process.env.LAB_DISPOSABLE!=='1')throw Error('disposable copy required')
const variant=process.argv[2];if(variant!=='before'&&variant!=='after')throw Error('before|after required')
if(variant==='before'){const p='core/count-recovery/guard-cases.ts',s=readFileSync(p,'utf8'),a='active?Math.min(until,start+leafAllowance(until-start,1)):Math.min(until,start+500)';if(s.split(a).length!==2)throw Error('slice anchor changed');writeFileSync(p,s.replace(a,'active?until:Math.min(until,start+500)'))}
