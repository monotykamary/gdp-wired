// Search-only experimental representation. A binder unused in a flag's body
// lets the local prover branch on its value without repeatedly expanding it.
// This representation is NOT source evidence absent exact Lean transport.
import type {C,Machine} from '../../core/machine.ts'
import {walkOnce} from '../../core/machine.ts'
import {ghostedOk,substC} from '../../kernel/kernel.ts'
import type {WeightedCandidate} from './weighted.ts'

export function closeWeightedFlags(c:WeightedCandidate):WeightedCandidate|undefined {
  const flags:Record<string,C>=Object.create(null), inlined:Record<string,C>=Object.create(null)
  const src=JSON.stringify(c.machine);let stem='internal$';while(src.includes(stem))stem+='a'
  for(const [i,[name,value]] of Object.entries(c.ghost.orig.step.flags??{}).entries()){
    if(value.op==='all')return undefined
    const body=substC(value,{vars:{},maps:{},flags:inlined})
    let open=false;walkOnce(body,e=>{const t=e as C;if(t.op==='flag'||t.op==='all')open=true})
    if(open)return undefined
    inlined[name]=body
    flags[name]={op:'all',key:`${stem}${i}`,c:body}
  }
  const replace=(m:Machine):Machine=>({...m,step:{...m.step,flags}})
  const ghost={...c.ghost,orig:replace(c.ghost.orig)}
  if(!ghostedOk(ghost))return undefined
  return {...c,ghost,machine:replace(c.machine)}
}
