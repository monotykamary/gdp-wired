// The aggregate law does not need any kind as a premise. Prove the kinds
// independently on the same source machine; ordinary checking is mandatory.
import {type C,type E,type Law,type Machine,walkOnce} from './machine.ts'
import {checkLaws,obligations,own,type Instances,type Tree} from '../kernel/kernel.ts'
import {clock,grow,pastWall} from '../kernel/prove.ts'
import {growCdcl} from '../kernel/cdcl.ts'

export type AggregateKinds = {laws:Law[],proof:{instances:Record<string,Instances>,trees:Record<string,Tree>}}
export function checkAggregateKinds(m:Machine,kinds:Law[],until:number):AggregateKinds|undefined {
  if (kinds.some(l=>l.some?.length||l.keys?.length||l.finite!==undefined||l.ex)) return
  // A conjunction at any key holds iff each conjunct holds at that same key.
  const parts=(c:C):C[]=>c.op==='and'&&c.xs.length ? c.xs.flatMap(parts) : [c]
  const laws=kinds.flatMap(k=>parts(k.holds).map((holds,i)=>({...k,name:`${k.name} [kind ${i+1}]`,holds})))
  const instances:Record<string,Instances>=Object.fromEntries(laws.filter(l=>l.forall).map(l=>{
    const reads=new Set<string>(), probe:E={op:'var',name:`${l.forall}#`}
    walkOnce(l.holds,t=>{ const e=t as E; if(e.op==='get') reads.add(e.map) })
    const addresses=[...reads].flatMap(map=>{
      const w=own(m.step.maps??{},map)
      return w&&'key' in w?[w.key]:[]
    })
    const terms=[...new Map([probe,...addresses].map(t=>[JSON.stringify(t),t])).values()]
    return [l.name,{[l.name]:terms}]
  }))
  let goals:ReturnType<typeof obligations>
  try { goals=obligations(m,laws,instances) } catch {
    if (pastWall()) return
    return
  }
  const trees:Record<string,Tree>=Object.create(null)
  for (const goal of goals) {
    const quick=grow(goal,new Map(),{nodes:0,until:Math.min(until,clock()+75)})
    const short = 'tree' in quick ? quick : growCdcl(goal,new Map(),{nodes:0,until:Math.min(until,clock()+3500)})
    const got = 'tree' in short ? short : grow(goal,new Map(),{nodes:0,until})
    if (!('tree' in got)) return
    trees[goal.name]=got.tree
  }
  const proof={instances,trees}
  return checkLaws(m,laws,proof) ? {laws,proof} : undefined
}
