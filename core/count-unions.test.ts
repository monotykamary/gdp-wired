import {expect, test} from 'bun:test'
import {all, get, ite, less, n, not, plus, same, x} from './machine.ts'
import {certFor} from './counts.ts'
import {checkMC, mcGoal} from '../kernel/kernel.ts'
import {clock, grow} from '../kernel/prove.ts'
import {proposeCountUnions} from './count-unions.ts'
import {countsForReads} from './count-facts.ts'

test('raw indicator partitions keep a checked pointwise alternative',()=>{
  const k=x('cell'),a=same(get('A',k),n(1)),b=same(get('B',k),n(1)),base={j:'row',key:'cell',below:n(4)}
  const ds=[{...base,map:'Acount',body:get('A',k)},{...base,map:'OnlyA',body:ite(all(a,not(b)),n(1),n(0))},{...base,map:'Both',body:ite(all(a,b),n(1),n(0))}]
  const reads:[string,string,ReturnType<typeof n>][]=[['aa','Acount',n(0)],['ab','OnlyA',n(0)],['ac','Both',n(0)]]
  const insts=proposeCountUnions(countsForReads(ds,reads)!,[])
  const inst=insts.find(i=>i.terms.some(([s,v])=>s===1&&v==='aa'))!
  expect(inst.terms).toHaveLength(3)
  const broken=less(plus(get('OnlyA',n(0)),get('Both',n(0))),get('Acount',n(0))),cert={reads,insts:[inst]}
  const hyps=[same(get('A',x(inst.wit)),n(1)),broken],g=mcGoal(hyps,ds,cert)!
  const proof=grow(g,new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in proof).toBe(true)
  if('tree'in proof)expect(checkMC(hyps,ds,{...cert,tree:proof.tree})).toBe(true)
  const weighted=[same(get('A',x(inst.wit)),n(2)),broken],bad=mcGoal(weighted,ds,cert)!
  const counter=grow(bad,new Map(),{nodes:0,until:clock()+1000})
  expect('tree'in counter).toBe(false)
  expect('stuck'in counter&&counter.stuck).toBe('sat')
})

test('Boolean indicators retain partition identities without a global atom table',()=>{
  const k=x('cell'),a=same(get('A',k),n(1)),b=same(get('B',k),n(1)),base={j:'row',key:'cell',below:n(4)}
  const ds=[{...base,map:'Acount',body:ite(a,n(1),n(0))},{...base,map:'OnlyA',body:ite(all(a,not(b)),n(1),n(0))},{...base,map:'Both',body:ite(all(a,b),n(1),n(0))}]
  const reads:[string,string,ReturnType<typeof n>][]=[['aa','Acount',n(0)],['ab','OnlyA',n(0)],['ac','Both',n(0)]]
  const insts=proposeCountUnions(countsForReads(ds,reads)!,[])
  expect(insts).toHaveLength(2)
  for(const instance of insts){
    const broken=instance.terms[0]![0]===1?less(plus(get('OnlyA',n(0)),get('Both',n(0))),get('Acount',n(0))):less(get('Acount',n(0)),plus(get('OnlyA',n(0)),get('Both',n(0))))
    const cert={reads,insts:[instance]},g=mcGoal([broken],ds,cert)!,proof=grow(g,new Map(),{nodes:0,until:clock()+1000})
    expect('tree'in proof).toBe(true)
    if('tree'in proof)expect(checkMC([broken],ds,{...cert,tree:proof.tree})).toBe(true)
  }
})

test('a five-term single-witness certificate bounds disjoint subsets by a relational union', () => {
  const k = x('member'), a = same(get('A', k), n(1)), b = same(get('B', k), n(1)), v = same(get('Vote', k), n(1))
  const base = {j: 'unused', key: 'member', below: n(4)}, bit = (c: Parameters<typeof ite>[0]) => ite(c, n(1), n(0))
  const decls = [
    {...base, map: 'Remaining#', body: bit(all(a, not(v)))},
    {...base, map: 'Voters', body: bit(all(b, v))},
    {...base, map: 'Left', body: bit(all(a, not(b)))},
    {...base, map: 'Middle', body: bit(all(a, b))},
    {...base, map: 'Right', body: bit(all(not(a), b))},
  ]
  const at = (s: string) => get(s, n(0))
  const hyps = [less(plus(plus(at('Left'), at('Middle')), at('Right')), plus(at('Remaining#'), at('Voters')))]
  const proposed = certFor({hyps}, decls, true, 1000)
  const five = proposed.insts.filter(i => i.terms.length === 5)
  expect(five.length).toBeGreaterThan(0)
  const cert = {...proposed, insts: five, picks: []}
  const goal = mcGoal(hyps, decls, cert)!
  const proof = grow({name: 'union bound', hyps: goal.hyps}, new Map(), {nodes: 0, until: clock() + 1500})
  expect('tree' in proof).toBe(true)
  if ('tree' in proof) expect(checkMC(hyps, decls, {...cert, tree: proof.tree})).toBe(true)
})
