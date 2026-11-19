// A local certificate schema, outside the trusted checker. Its finite-fold
// composition and binding to the original step are checked in Lean.
import {type C,type E,type Law,type Machine,atMost,get,n,not,plus,same,x} from '../../core/machine.ts'
import {check,substC,substE,type Goal,type Tree} from '../../kernel/kernel.ts'
import {clock,grow,withWall} from '../../kernel/prove.ts'
import {searchWall} from '../../core/wall.ts'
import {proposeFilteredCounters,type FilteredCounterProposal} from './aggregate.ts'

const zero = n(0)
const lt = (a:E,b:E):C => ({op:'<',a,b})
const iff = (c:C,then:E,otherwise:E):E => ({op:'if',c,then,else:otherwise})
export type Scope = 'plain' | 'row'
export type Local = {name:string, assumptions:C[], conclusion:C, scope:Scope}
export type FoldTheory = {locals:Local[], bound:E, coordinate:string, point:E, proposal:FilteredCounterProposal}
export type FoldPacket = {kind:'point-fold',machine:Machine,laws:Law[],trees:Record<string,Tree>}
const toGoal = (l:Local):Goal => ({name:l.name,hyps:[...l.assumptions,not(l.conclusion)]})

export function foldTheory(m: Machine, law: Law): FoldTheory | undefined {
  // Closed fragment for source binding: one source map, no carried maps, no
  // external facts or special postprocessing. Unrecognized syntax falls back.
  if (m.facts?.length || Object.keys(m.fns ?? {}).length || m.inputMaps?.length || Object.keys(m.maps ?? {}).length !== 1 || Object.keys(m.step.maps ?? {}).length !== 1) return
  const p = proposeFilteredCounters(m,law)[0]
  if (!p || p.fields.length < 2 || p.fields.length > 6 || !m.assume || p.bound.op !== 'var' || !m.params.includes(p.bound.name)) return
  const wr = m.step.maps![p.map]!
  if (!('each' in wr)) return
  const occupied = JSON.stringify([m,law])
  let local = 'agg$coordinate'; while (occupied.includes(local)) local += '0'
  const j = x(local), input = x(p.key)
  const plusOffset = (k:E):E => p.offset ? plus(k,n(p.offset)) : k
  const point:E = p.offset ? {op:'sub',a:input,b:n(p.offset)} : input
  const flags:Record<string,C> = Object.create(null)
  for (const [name, c] of Object.entries(m.step.flags ?? {})) {
    if (c.op === 'all') return
    flags[name] = substC(c,{vars:{},maps:{},flags})
  }
  const inline = {vars:{},maps:{},flags}
  const assume = substC(m.assume,inline), reset = substC(p.reset,inline), after = (k:E) => substE(wr.value,{...inline,vars:{[wr.each]:k}})
  const plain = (name:string,assumptions:C[],conclusion:C):Local => ({name,assumptions,conclusion,scope:'plain'})
  const row = (name:string,assumptions:C[],conclusion:C):Local => ({name,assumptions,conclusion,scope:'row'})
  const coord = plusOffset(j), atPoint = plusOffset(point)
  const locals:Local[] = [
    plain('point_inside',[assume],lt(point,p.bound)),
    row('other_cells_frame',[assume,not(reset),not(same(j,point))],same(after(coord),get(p.map,coord))),
    row('broadcast_reset',[assume,reset],same(after(coord),n(m.maps![p.map]!))),
    plain('capacity_entails_claim',[atMost(p.fields.map(f=>x(f.field)).reduce(plus),p.bound)],law.holds),
  ]
  for (const [i,f] of p.fields.entries()) {
    const next = substE(m.step.state![f.field]!,inline)
    const indicator = (cell:E) => iff(same(cell,n(f.value)),n(1),zero)
    locals.push(
      plain(`field${i}_init`,[],same(m.state[f.field]!,zero)),
      plain(`field${i}_reset`,[assume,reset],same(next,zero)),
      plain(`field${i}_delta`,[assume,not(reset)],same(plus(next,indicator(get(p.map,atPoint))),plus(x(f.field),indicator(after(atPoint))))),
    )
  }
  const classified = p.fields.map(f=>iff(same(get(p.map,coord),n(f.value)),n(1),zero)).reduce(plus)
  locals.push(row('disjoint_capacity',[],atMost(classified,n(1))))
  return {locals,coordinate:local,bound:p.bound,point,proposal:p}
}

export function provePointFold(m:Machine,law:Law,ms:number):FoldPacket|undefined {
  const theory = foldTheory(m,law)
  if (!theory || ms <= 0) return
  return withWall(searchWall(ms),()=> {
    const until = clock()+ms, trees:Record<string,Tree> = Object.create(null)
    for (const local of theory.locals) {
      const out = grow(toGoal(local),new Map(),{nodes:0,until})
      if (!('tree' in out)) return
      trees[local.name] = out.tree
    }
    const packet = {kind:'point-fold' as const,machine:m,laws:[law],trees}
    return checkPointFold(packet) ? packet : undefined
  })
}

export function checkPointFold(packet:FoldPacket):boolean {
  const t = packet.laws.length === 1 && foldTheory(packet.machine,packet.laws[0]!)
  return !!t && Object.keys(packet.trees).length === t.locals.length && t.locals.every(local=>{
    const tree = Object.hasOwn(packet.trees,local.name) && packet.trees[local.name]
    return !!tree && check(toGoal(local),tree)
  })
}

export const localGoal = toGoal
