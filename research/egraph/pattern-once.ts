// Public engine entry for protocol pattern scope only; never performs model refinement.
import type {Law,Machine} from '../../core/machine.ts'
import type {Goal,Instances} from '../../kernel/kernel.ts'
import {withModels} from '../../kernel/prove.ts'
export function withProtocolPatterns<T>(machine:Machine,laws:Law[],instances:Instances,goal:Goal,ask:()=>T):T{
  let calls=0
  const out=withModels(machine,laws,instances,()=>[goal],()=>{if(++calls!==1)throw Error('unexpected extra query');return ask()},()=>undefined,()=>true)
  if(calls!==1||out.inst!==instances)throw Error('unexpected refinement')
  return out.result
}
