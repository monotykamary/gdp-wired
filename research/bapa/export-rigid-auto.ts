// UNSEEDED changed-path gate. No new fact or selected witness is supplied.
import {writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {toLean} from '../../lean-kernel/emit.ts'
import {proveLaws} from '../../kernel/prove.ts'
import {withFunctionInstances} from '../../kernel/function-instances.ts'
import {rigidMinimal, rigidMinimalLaw} from './rigid-minimal.ts'
import {rigidMinimalWrapper} from './rigid-minimal-wrapper.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR!, p=rigidMinimal(), machine=p.abstractMachine
const before=JSON.stringify(machine)
const result=withFunctionInstances(p.functionInstances,()=>{
  const report=proveLaws(machine,[rigidMinimalLaw])
  if(!report.proven || !report.checked) return {report}
  const text=toLean([{id:'rigid_minimal',machine,laws:[rigidMinimalLaw],lean:{after:ix=>rigidMinimalWrapper(machine,p.auxiliaries.intersection!,ix)}}],{native:false,cyclic:false})
  writeFileSync(join(out,'RigidMinimalAuto.lean'),text.replace('import History','import RigidEncoding\nimport History'))
  return {report}
})
writeFileSync(join(out,'unseeded-report.json'),JSON.stringify({result,groundSeed:'none',machineUnchanged:before===JSON.stringify(machine),accepted:false},null,2)+'\n')
if(result.status!=='complete' || !result.value.report.proven || !result.value.report.checked) throw Error('unseeded minimal did not close')
