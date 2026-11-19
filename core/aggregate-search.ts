import type {Law,Machine} from './machine.ts'
import {searchWall} from './wall.ts'
import {proposeFilteredCounters} from './filtered-sum-candidates.ts'
import {weightedSearch} from './aggregate-weighted/search.ts'
import {checkFiniteSum,finiteSumTheory,sumLocalGoal,type FiniteSumCertificate} from '../kernel/finite-sum.ts'
import {checkGhostWrite,type GhostWriteCertificate} from '../kernel/ghost-write.ts'
import type {Tree} from '../kernel/kernel.ts'
import {clock,grow,withWall} from '../kernel/prove.ts'

export type AggregateCertificate = FiniteSumCertificate | GhostWriteCertificate

export function searchAggregate(m:Machine, law:Law, ms:number):AggregateCertificate|undefined {
  if (ms<=0 || m.history || m.primitiveFailure || Object.keys(m.sums??{}).length || Object.keys(m.counts??{}).length ||
      Object.keys(m.fns??{}).length || m.facts?.length || m.inputMaps?.length || law.keys?.length || law.some?.length || law.ex) return
  const maps=Object.values(m.step.maps??{})
  if (!law.forall) {
    if (maps.length!==1 || !('each' in maps[0]!)) return
    const allowance=Math.min(1_000,ms)
    return withWall(searchWall(allowance),()=>{
      const until=clock()+allowance
      for (const p of proposeFilteredCounters(m,law)) {
        if (p.bound.op!=='var') continue
        const layout={map:p.map,bound:p.bound.name,key:p.key,offset:p.offset,fields:p.fields.map(({field,value})=>({field,value}))}
        const t=finiteSumTheory(m,law,layout)
        if (!t) continue
        const trees:Record<string,Tree>=Object.create(null)
        for (const local of t.locals) {
          const result=grow(sumLocalGoal(local),new Map(),{nodes:0,until})
          if (!('tree' in result)) break
          trees[local.name]=result.tree
        }
        const cert={kind:'finite-sum' as const,layout,trees}
        if (checkFiniteSum(m,law,cert)) return cert
      }
      return undefined
    })
  }
  if (!maps.some(write=>'each' in write) || !maps.some(write=>!('each' in write))) return
  const p=weightedSearch(m,law,ms)
  if (!p) return
  const cert:GhostWriteCertificate={kind:'ghost-write',recipe:p.recipe,projection:{omitMap:p.recipe.ghostMap},target:p.machine,laws:p.laws,pointLaw:p.pointLaw,proof:p.proof}
  return checkGhostWrite(m,law,cert) ? cert : undefined
}
