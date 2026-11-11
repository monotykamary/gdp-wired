// Read-only research comparison: no binder, candidate or certificate writes.
import {readFileSync} from 'node:fs'
import {type Machine,type Law} from '../../../core/machine.ts'
import {alphaAstKey,alphaStepKey,sameAlphaCounts} from './c2-alpha-audit.ts'
const pair=JSON.parse(readFileSync(process.argv[2]!,'utf8')) as {original:Machine,prepared:Machine,captured:Machine,family:Law[],capturedFamily:Law[]}
const stable=(value:unknown):string=>JSON.stringify(value,(_key,v)=>v&&typeof v==='object'&&!Array.isArray(v)?Object.fromEntries(Object.keys(v).sort().map(k=>[k,v[k]])):v)
const outside=(m:Machine)=>{const {step:_step,counts:_counts,...rest}=m;return rest}
const result={outsideStepAndCountsExact:stable(outside(pair.original))===stable(outside(pair.captured)),allOnlyStepAlpha:alphaAstKey(pair.original.step)===alphaAstKey(pair.captured.step),allAndMapUpdateStepAlpha:alphaStepKey(pair.original.step)===alphaStepKey(pair.captured.step),freshLawObjectsExact:stable(pair.family)===stable(pair.capturedFamily),derivedCountsConservative:sameAlphaCounts(pair.prepared.counts??{},pair.captured.counts??{}),laws:pair.family.length,counts:Object.keys(pair.prepared.counts??{}).length,readOnly:true,recaptureAuthorized:false,nativeChecked:false,leanClearance:false}
console.log('C2_READONLY_PAIR_AUDIT '+JSON.stringify(result))
if(!result.outsideStepAndCountsExact||!result.allAndMapUpdateStepAlpha||!result.freshLawObjectsExact||!result.derivedCountsConservative)process.exitCode=1
