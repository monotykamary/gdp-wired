// Disposable negative control: restore just the stale-first-SAT admission bug.
import {readFileSync,writeFileSync} from 'node:fs'
const path='kernel/prove.ts',source=readFileSync(path,'utf8')
const old='  let at = inst, cap = 0',next='  let at = inst, cap = 0, first: {result: T, inst: Instances} | undefined'
const anchor='    const abandon = (why: string) => ({result: unknown(result, `unconfirmed model: ${why}`), inst: at})'
if(source.split(old).length!==2||source.split(anchor).length!==2)throw Error('mutation anchor drift')
try {
 writeFileSync(path,source.replace(old,next).replace(anchor,'    first ??= {result, inst: at}\n    const abandon = (_why: string) => first!'))
 const out=Bun.spawnSync(['bun','test','--timeout','120000','research/bapa/model-confirmation-public.test.ts'],{env:{...process.env,GDP_EPR:'0',GDP_SET_FIRST:'0'},stdout:'pipe',stderr:'pipe'})
 const log=Buffer.concat([out.stdout,out.stderr]).toString()
 writeFileSync(process.env.SUPERCOMPUTER_OUTPUT_DIR+'/legacy-control.log',log)
 if(out.exitCode===0||!log.includes('(fail) public proveRule keeps retained:7')||!log.includes('dropped')||!log.includes('retained:7:'))throw Error('public regression did not reject stale-first-SAT mutation')
 console.log(JSON.stringify({status:'ok',legacyExit:out.exitCode,regressionRejectedStaleSAT:true}))
} finally {writeFileSync(path,source)}
