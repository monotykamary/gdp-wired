import {expect, test} from 'bun:test'
import {type Machine, type Law, x, n, all, same, get} from './machine.ts'
import {scanPrefixes} from './carry.ts'
import {protocols} from '../research/protocols/ic3syn/models.ts'
import {type CountCert, type Instances, countedObligations, checkCountedLaws, mcGoal} from '../kernel/kernel.ts'
import {grow, modelInstances, clock, counted, fullRate, fullWork, withWork, withDeadline, withWall} from '../kernel/prove.ts'
const p = protocols.find(p => p.id === 'paxos_epr')!
const m = p.make().machine
const rename = (o: unknown, names: Map<string, string>): any => typeof o === 'string' ? names.get(o) ?? o : Array.isArray(o) ? o.map(v => rename(v, names)) : o && typeof o === 'object' ? Object.fromEntries(Object.entries(o).map(([k,v]) => [names.get(k) ?? k, rename(v,names)])) : o

test('syntax candidates survive systematic renaming and ignore unrelated or nonincrementing counters', () => {
  const ls = scanPrefixes(m)
  expect(ls).toHaveLength(2)
  const names = new Map([...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...Object.keys(m.step.flags ?? {})].map((s,i) => [s, `renamed${i}`]))
  expect(scanPrefixes(rename(m,names))).toHaveLength(2)
  const unrelated: Machine = {name:'unrelated', params:[], inputs:[], state:{i:n(0)}, step:{state:{i:{op:'add',a:x('i'),b:n(1)}}}}
  expect(scanPrefixes(unrelated)).toEqual([])
  const nonincrementing = structuredClone(m)
  nonincrementing.step.state!.cnt = n(0)
  expect(scanPrefixes(nonincrementing)).toEqual([])
  expect(scanPrefixes(m, [ls[0]!])).toEqual([])
  expect(scanPrefixes(m, [ls[1]!])).toEqual([])
  expect(new Set(ls.map(l => l.name)).size).toBe(ls.length)
})

test('multiple structural matches have stable distinct names', () => {
  const many = structuredClone(m)
  many.maps!.Extra = 0
  many.step.flags!.fails = all(many.step.flags!.fails!, same(get('Extra', x('cnt')),n(1)))
  // Place another membership beside the negated row flag itself.
  const f = m.step.flags!.fails!
  many.step.flags!.fails = f.op === 'and' ? all(...f.xs, same(get('Extra',x('cnt')),n(1))) : all(f,same(get('Extra',x('cnt')),n(1)))
  const ls = scanPrefixes(many)
  expect(ls.length).toBeGreaterThan(2)
  expect(new Set(ls.map(l => l.name)).size).toBe(ls.length)
  expect(scanPrefixes(structuredClone(many))).toEqual(ls)
})

// The unchanged automatic model-instance mechanism; no handwritten law or flag tuple.
function automatic(machine: Machine, laws: Law[]) {
  const certs: Record<string, CountCert> = {}, instances: Record<string, Instances> = {}
  for (let i=0;i<laws.length;i++) {
    const law=laws[i]!, terms=[...(law.forall ? [x(law.forall+'#')] : []), ...(law.keys ?? []).map(x)]
    let at: Instances = Object.fromEntries(Object.entries(machine.step.flags ?? {}).filter(([,q]) => q.op==='all' && !q.keys?.length).map(([f]) => ['?'+f,terms]))
    let complete=false
    for (let round=0;round<4;round++) {
      let retry=false
      for (const {goal,decls} of countedObligations(machine,laws,{[law.name]:at},i)) {
        const c={reads:[],insts:[]}, gg=mcGoal(goal.hyps,decls,c)!, out=grow(gg,new Map(),{nodes:0,until:clock()+60000})
        if ('tree' in out) {certs[goal.name]={...c,tree:out.tree};continue}
        const next=out.stuck==='sat' && out.witness && goal.name.endsWith('@step') ? modelInstances(machine,laws,at,gg,out.witness) : undefined
        if (!next) return undefined
        at=next;retry=true;break
      }
      if (!retry) {complete=true;break}
    }
    if (!complete) return undefined
    instances[law.name]=at
  }
  return {instances,certs}
}
test('automatic instances check generic prefix; broken row check rejects the same certificate', () => {
  const laws=scanPrefixes(m), work=fullWork()
  const proof=withWall(performance.now()+59500,()=>counted(fullRate,()=>withWork(work+60000*fullRate,()=>withDeadline(clock()+60000,()=>automatic(m,laws))),true))
  expect(proof).toBeDefined()
  expect(checkCountedLaws(m,laws,proof!)).toBe(true)
  expect(checkCountedLaws(p.make(p.bug).machine,laws,proof!)).toBe(false)
  expect(scanPrefixes(p.make(p.bug).machine)).toEqual([])
},60000)
