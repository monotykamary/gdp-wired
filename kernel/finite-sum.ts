// Lean twin: FiniteSumComposition.state_law, restricted to a symbolic prefix,
// one touched site or a zero-row rebuild, and unit site capacity.
import {type C,type E,type Law,type Machine,atMost,get,n,not,plus,same,walkOnce,x} from '../core/machine.ts'
import {check,mapArities,obligations,own,substC,substE,type Goal,type Tree} from './kernel.ts'

export type FiniteSumLayout = {
  map:string, bound:string, key:string, offset:number,
  fields:{field:string,value:number}[]
}
export type FiniteSumCertificate = {kind:'finite-sum',layout:FiniteSumLayout,trees:Record<string,Tree>}
export type SumLocal = {name:string,assumptions:C[],conclusion:C}
export const sumLocalGoal = (l:SumLocal): Goal => ({name:l.name,hyps:[...l.assumptions,not(l.conclusion)]})
const zero = n(0)
const safeNat = (x:unknown): x is number => typeof x === 'number' && Number.isSafeInteger(x) && x >= 0

// The caller supplies the source and claim, not the packet. Only site/field
// coordinates are proposals. Build the obligations over actual source terms.
export function finiteSumTheory(m:Machine, law:Law, p:FiniteSumLayout) {
  const maps=m.maps??{}, writes=m.step.maps??{}, defaultCell=own(maps,p.map), wr=own(writes,p.map)
  if (m.history || m.primitiveFailure || Object.keys(m.sums??{}).length || Object.keys(m.counts??{}).length ||
      Object.keys(m.fns??{}).length || m.facts?.length || m.inputMaps?.length || m.leasts && Object.keys(m.leasts).length ||
      law.forall !== undefined || law.keys?.length || law.some?.length || law.ex || law.finite !== undefined ||
      !m.assume || Object.keys(maps).length!==1 || Object.keys(writes).length!==1 || !safeNat(defaultCell) ||
      !wr || !('each' in wr) || wr.value.op!=='if' ||
      !m.params.includes(p.bound) || !m.inputs.includes(p.key) || !safeNat(p.offset) || !Array.isArray(p.fields) || !p.fields.length) return
  if (new Set(p.fields.map(f=>f.field)).size !== p.fields.length ||
      !p.fields.every(f=>safeNat(f.value)&&f.value!==defaultCell&&own(m.state,f.field)&&own(m.step.state??{},f.field))) return
  let unsupported=false
  walkOnce([m,law.holds],o=>{
    const t=o as {op?:string,map?:string,value?:unknown,k?:unknown}
    if (t.op==='all'||t.op==='get'&&t.map?.startsWith('worddiv$')||t.op==='const'&&!safeNat(t.value)||t.op==='mul'&&!safeNat(t.k)) unsupported=true
  })
  if (unsupported || (own(mapArities(m,[law]),p.map)??1)!==1) return
  // Existing scope/natural checks establish disjoint params, inputs, state,
  // flags and source binders. In particular, no step can assign the bound.
  obligations(m,[law])

  let coordinate='agg$coordinate'
  const occupied=JSON.stringify([m,law])
  while (occupied.includes(coordinate)) coordinate+='0'
  const flags:Record<string,C>=Object.create(null)
  for (const [name,c] of Object.entries(m.step.flags??{})) flags[name]=substC(c,{vars:{},maps:{},flags})
  const inline={vars:{},maps:{},flags}, step=m.step.state??{}
  const assume=substC(m.assume,inline), bound=x(p.bound), input=x(p.key), j=x(coordinate)
  const point:E=p.offset?{op:'sub',a:input,b:n(p.offset)}:input
  const addr=(k:E):E=>p.offset?plus(k,n(p.offset)):k
  const after=(k:E)=>substE(wr.value,{...inline,vars:{[wr.each]:k}})
  const reset=substC(wr.value.c,{...inline,vars:{[wr.each]:input}}), coord=addr(j), atPoint=addr(point)
  const local=(name:string,assumptions:C[],conclusion:C):SumLocal=>({name,assumptions,conclusion})
  const locals=[
    local('point_inside',[assume],{op:'<',a:point,b:bound}),
    local('other_cells_frame',[assume,not(reset),not(same(j,point))],same(after(coord),get(p.map,coord))),
    local('broadcast_reset',[assume,reset],same(after(coord),n(defaultCell))),
    local('capacity_entails_claim',[atMost(p.fields.map(f=>x(f.field)).reduce(plus),bound)],law.holds),
  ]
  const indicator=(value:number,cell:E):E=>({op:'if',c:same(cell,n(value)),then:n(1),else:zero})
  for (const [i,f] of p.fields.entries()) {
    const next=substE(own(step,f.field)!,inline)
    locals.push(
      local(`field${i}_init`,[],same(own(m.state,f.field)!,zero)),
      local(`field${i}_reset`,[assume,reset],same(next,zero)),
      local(`field${i}_delta`,[assume,not(reset)],same(plus(next,indicator(f.value,get(p.map,atPoint))),plus(x(f.field),indicator(f.value,after(atPoint))))),
    )
  }
  locals.push(local('disjoint_capacity',[],atMost(p.fields.map(f=>indicator(f.value,get(p.map,coord))).reduce(plus),n(1))))
  return {locals,coordinate,point,bound,reset}
}

export function checkFiniteSum(m:Machine, law:Law, p:FiniteSumCertificate):boolean {
  try {
    if (p.kind!=='finite-sum') return false
    const theory=finiteSumTheory(m,law,p.layout)
    return !!theory && Object.keys(p.trees).length===theory.locals.length && theory.locals.every(local=>{
      const tree=own(p.trees,local.name)
      return !!tree && check(sumLocalGoal(local),tree)
    })
  } catch { return false }
}
