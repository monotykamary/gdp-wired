// Authorized uncounted proof attempt only, not a canonical row or claim run.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {proveLaws} from '../../kernel/prove.ts'
import {checkGhostedLaws} from '../../kernel/kernel.ts'
import {withFunctionInstances} from '../../kernel/function-instances.ts'
import {rigidNaive} from './rigid-naive.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!, p=rigidNaive()
writeFileSync(join(out,'source-machine.json'),JSON.stringify({machine:p.machine,laws:p.laws,strategy:p.strategy,ghosted:p.ghosted},null,2)+'\n')
const result=withFunctionInstances(p.strategy,()=>proveLaws(p.machine,p.laws))
const checked=result.status==='complete' && result.value.proven && result.value.checked && !!result.value.proof && checkGhostedLaws(p.ghosted,p.laws,result.value.proof)
writeFileSync(join(out,'proof-report.json'),JSON.stringify({result,ghostedChecked:checked,helperClassification:'GIVEN, not found',groundSeed:'none',intersection:'original Ivy axiom assumed',counted:false,accepted:false},null,2)+'\n')
console.log(JSON.stringify({status:result.status,proven:result.status==='complete'&&result.value.proven,checked,stats:result.stats}))
if(!checked) throw Error('unseeded naive_consensus proof not complete; inspect retained report')
