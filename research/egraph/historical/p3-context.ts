import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {E,Law,Machine} from '../../../core/machine.ts'
import {countedObligations,mcGoal,type Goal,type Instances,type CountInst,type MapRead} from '../../../kernel/kernel.ts'
export const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
export function p3Context(){
  if(sha(readFileSync('kernel/kernel.ts'))!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('checker pin')
  const path='research/egraph/historical/inputs/m2/decision-quorum.json.gz',bytes=readFileSync(path)
  if(sha(bytes)!=='6aac4db7a1f149f51ce8356e9f4f475474c583e36d7d44c69a4e7ba973411bba')throw Error('P3 input pin')
  const input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law,failure:{goal:Goal,witness?:Record<string,number>}}
  const raw=readFileSync('research/egraph/historical/recovery/p3-v9.json')
  if(sha(raw)!=='60ca6e820e25336230430a4ee648c2842759ca08b05f77b579e74ebe0b873675')throw Error('P3 context pin')
  const metadata=(JSON.parse(raw.toString()) as {metadata:{instances:Instances,reads:MapRead[],insts:CountInst[],picks:[string,E[]][]}}).metadata
  const base=countedObligations(input.m,input.laws,{[input.law.name]:metadata.instances},input.laws.findIndex(l=>l.name===input.law.name)).find(x=>x.goal.name.endsWith('@step'))
  if(!base)throw Error('P3 base missing')
  const reconstructed=mcGoal(base.goal.hyps,base.decls,metadata)
  if(!reconstructed)throw Error('P3 reconstruction failed')
  reconstructed.name=input.failure.goal.name
  const goalSha256=sha(JSON.stringify(reconstructed))
  if(goalSha256!=='a7cee3dd679c5c19df5fd6110c24a723158e8644299c98243df8c0513bd57357')throw Error('not the exact ordered P3 goal')
  return {input,metadata,base,original:reconstructed,goalSha256}
}
