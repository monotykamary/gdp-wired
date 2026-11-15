import {expect,test} from 'bun:test'
import {rule,proveRule} from '../../core/dsl.ts'
import {proofOutput,type PublicProofOutput} from '../../core/proof-output.ts'
import {checkLaws} from '../../kernel/kernel.ts'
import type {Law} from '../../core/machine.ts'
const make=()=>rule('seeded public').state({x:0,y:0}).step(({y})=>({x:y,y:0}))
test('public candidate option retains one complete checked family and unchanged input',()=>{
  const r=make(), goal=r.law('x stays zero',({x})=>x.atMost(0)), seed=r.law('y stays zero',({y})=>y.atMost(0)), laws=[goal]
  const events:PublicProofOutput[]=[], audits:unknown[]=[], prior=proofOutput.on
  try {
    proofOutput.on=e=>events.push(e)
    const result=proveRule(r as never,laws,{search:true,candidateSeeds:{laws:[seed],report:a=>audits.push(a)}})
    expect(result.proven&&result.checked).toBe(true)
    expect(events).toHaveLength(1);expect(events[0]!.result).toBe(result);expect(events[0]!.original.laws).toBe(laws)
    expect(audits).toEqual([{status:'checked',kept:['y stays zero'],dropped:[]}])
    let node=events[0]!.proof
    while(node?.kind==='derived') {expect(node.parents).toHaveLength(1);node=node.parents[0]}
    expect(node?.kind).toBe('usual')
    if(node?.kind!=='usual') throw Error('missing retained usual family')
    expect(node.laws.map(l=>l.name)).toContain('x stays zero')
    expect(node.laws.map(l=>l.name)).toContain('y stays zero')
    expect(checkLaws(node.machine,node.laws,node.proof)).toBe(true)
  } finally {proofOutput.on=prior}
})
test('false candidate cannot establish a false public goal',()=>{
  const r=make(), zero=r.law('zero',({x})=>x.atMost(0))
  const falseLaw:Law={name:'false initially',holds:{op:'not',x:zero.holds}}
  const result=proveRule(r as never,[falseLaw],{search:true,candidateSeeds:{laws:[{...falseLaw,name:'false candidate'}]}})
  expect(result.proven&&result.checked).toBe(false)
})
