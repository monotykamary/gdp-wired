import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import type {Machine,Law} from '../../../core/machine.ts'
import {countedObligations,mcGoal} from '../../../kernel/kernel.ts'
export const sha=(x:Buffer|string)=>createHash('sha256').update(x).digest('hex')
export function frozenStart(id:string){
  const pins:Record<string,[string,string]>={safety:['one-value-decided','c5eac7b02e6ab460d9d9e3864ad7d2a667ec583f7fb6478da7abcb75a71c7bc1'],p3:['decision-quorum','6aac4db7a1f149f51ce8356e9f4f475474c583e36d7d44c69a4e7ba973411bba']}
  const pin=pins[id];if(!pin)throw Error('unknown start')
  if(sha(readFileSync('kernel/kernel.ts'))!=='596eaaea9a44a11330178ac37b55377f5747a4ed08a8dd010c26b393c69521e2')throw Error('kernel pin')
  const bytes=readFileSync(`research/egraph/historical/inputs/m2/${pin[0]}.json.gz`);if(sha(bytes)!==pin[1])throw Error('input pin')
  const input=JSON.parse(gunzipSync(bytes).toString()) as {m:Machine,laws:Law[],law:Law}
  const base=countedObligations(input.m,input.laws,{[input.law.name]:{}},input.laws.findIndex(l=>l.name===input.law.name)).find(g=>g.goal.name.endsWith('@start'))!
  const goal=mcGoal(base.goal.hyps,base.decls,{reads:[],insts:[],picks:[]})!;goal.name=base.goal.name
  return {input,base,goal,inputSha256:pin[1],goalSha256:sha(JSON.stringify(goal))}
}
