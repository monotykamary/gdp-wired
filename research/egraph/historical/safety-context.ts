import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {E,Law,Machine} from '../../../core/machine.ts'
import {countedObligations,mcGoal,type Goal,type Instances,type CountInst,type MapRead} from '../../../kernel/kernel.ts'
export const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
export function safetyContext(){
  if(sha(readFileSync('kernel/kernel.ts'))!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('checker pin')
  const path='research/egraph/historical/inputs/m2/one-value-decided.json.gz',bytes=readFileSync(path)
  if(sha(bytes)!=='c5eac7b02e6ab460d9d9e3864ad7d2a667ec583f7fb6478da7abcb75a71c7bc1')throw Error('Safety input pin')
  const input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal,witness?:Record<string,number>}}
  const raw=readFileSync('research/egraph/historical/recovery/safety-v11.json')
  if(sha(raw)!=='ada88e46d2c4139ad33cdb9cd68273ec3765b35874213357273a934d0d9dc727')throw Error('Safety context pin')
  const metadata=(JSON.parse(raw.toString()) as {metadata:{instances:Instances,reads:MapRead[],insts:CountInst[],picks:[string,E[]][]}}).metadata
  const base=countedObligations(input.m,input.laws,{[input.law.name]:metadata.instances},input.laws.findIndex(l=>l.name===input.law.name)).find(x=>x.goal.name.endsWith('@step'))
  if(!base)throw Error('Safety base missing')
  const reconstructed=mcGoal(base.goal.hyps,base.decls,metadata)
  if(!reconstructed)throw Error('Safety reconstruction failed')
  reconstructed.name=input.failure.goal.name
  const goalSha256=sha(JSON.stringify(reconstructed))
  if(goalSha256!=='58496db30029729c33954d6cc01f61673dbe5bc0c52c4f64b1b4126c0dcc20ca')throw Error('not the exact ordered Safety goal')
  return {input,metadata,base,original:reconstructed,goalSha256}
}
