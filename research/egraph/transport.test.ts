import {test,expect} from 'bun:test'
import {canon,check,leafConstraints,type Goal,type Tree} from '../../kernel/kernel.ts'
import {Meter} from './match.ts'
import {renameLinear,transportTree} from './transport.ts'
const source:Goal={name:'source',hyps:[{op:'<',a:{op:'var',name:'old'},b:{op:'const',value:0}}]}
const target:Goal={name:'target',hyps:[{op:'=',a:{op:'var',name:'new'},b:{op:'var',name:'new'}},{op:'<',a:{op:'var',name:'new'},b:{op:'const',value:0}}]}
const rows=leafConstraints(source,new Map()),i=rows.findIndex(r=>canon(r.lin)===canon({old:1,'1':1})),j=rows.findIndex(r=>canon(r.lin)===canon({old:-1}))
const proof:Tree={leaf:[{kind:'input',index:i},{kind:'input',index:j},{kind:'combine',a:0,b:1,ma:1,mb:1}]}
test('alpha transport reindexes an existing derivation without asking a solver',()=>{
  expect(check(source,proof)).toBe(true)
  const meter=new Meter(100000),out=transportTree(source,target,proof,{old:'new'},meter)
  expect(check(target,out)).toBe(true)
  expect(meter.used).toBeGreaterThanOrEqual(leafConstraints(source,new Map()).length+leafConstraints(target,new Map()).length)
})
test('transport cannot replace a missing premise',()=>{
  expect(()=>transportTree(source,{name:'missing',hyps:[target.hyps[0]!]},proof,{old:'new'},new Meter(100000))).toThrow('absent')
})
test('nested tuple-cell keys rename exact variables, not prefixes',()=>{
  const out=renameLinear({'M[⟨old:1|N[old:1]:1⟩]':1,oldish:3},{old:'new'},new Map(),new Meter(100000))
  expect(out).toEqual({'M[⟨new:1|N[new:1]:1⟩]':1,oldish:3})
})
