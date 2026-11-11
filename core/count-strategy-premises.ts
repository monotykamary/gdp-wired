// Audit metadata, never a new premise or proof authority. The composer calls
// this only after checking its original INIT/STEP certificate. Offered laws
// without an actual tuple do not enter it. Scalar laws are always assumed by
// kernel.assumed, even without an explicit entry in the instance map.
import {type Law} from './machine.ts'
import {type CountStrategyProof} from './count-strategy.ts'
export function recordCountStrategyPremises(family:readonly Law[],proof:CountStrategyProof):CountStrategyProof&{premises:readonly string[]}{
 if(new Set(family.map(law=>law.name)).size!==family.length)throw Error('ambiguous strategy premise name')
 const premises=family.filter(law=>{
  const arity=law.forall?1+(law.keys?.length??0):0
  if(!Object.hasOwn(proof.instances,law.name))return arity===0
  const values=proof.instances[law.name]!
  if(arity?values.length%arity!==0:values.length!==0)throw Error('malformed strategy premise tuple: '+law.name)
  return arity===0||values.length>0
 })
 return {...proof,premises:Object.freeze(premises.map(law=>law.name))}
}
