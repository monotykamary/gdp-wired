import {expect,test} from 'bun:test'
import {Cond,MapRef,Term,rule,nat,exists,everyKey,proveRule,proveSteps} from './dsl.ts'
import {side} from './compose.ts'
import {copyVariable,guardReserved} from './dsl-binders.ts'

test('generated sum provenance survives next-state priming without a name whitelist',()=>{
  const sum=new MapRef('pending',0).sum(cell=>cell.times(2))
  if(sum.e.op!=='var')throw Error('sum must be a variable')
  const name=`${sum.e.name}'`
  const primed=copyVariable(sum.e,{op:'var' as const,name})
  expect(()=>guardReserved(primed)).not.toThrow()
  // Issuing the real sum does not bless a later forged node of identical spelling.
  expect(()=>guardReserved({op:'var',name})).toThrow('free reserved')
  const r=rule('primed sum admission').maps({pending:0}).step(()=>({}))
  expect(()=>r.stepLaw('generated sum',()=>new Cond({op:'=',a:primed,b:primed}))).not.toThrow()
  expect(()=>r.stepLaw('forged sum',()=>new Term({op:'var',name}).eq(0))).toThrow('free reserved')
})

test('a generated primed sum is read and proven through its registered sum',()=>{
  const r=rule('after sum').maps({pending:0}).step(()=>({}))
  const law=r.stepLaw('sum remains natural',({pending})=>{
    const sum=pending.sum(cell=>cell.times(2))
    if(sum.e.op!=='var')throw Error('sum must be a variable')
    return new Term(copyVariable(sum.e,{op:'var',name:`${sum.e.name}'`})).atLeast(0)
  })
  expect(proveSteps(r,[],[law],{search:false})).toMatchObject({proven:true,checked:true})
})

test('a sparse custom-kind ghost preserves its generated self-reference',()=>{
  const sparse=Object.create(nat) as typeof nat
  sparse.store=()=>({})
  const r=rule('sparse ghost').state({s:0}).step(()=>({}))
  const law=r.law('a zero ghost remains zero',()=>exists(sparse,k=>k.eq(0),{start:0,step:k=>k}))
  expect(proveRule(r,[law],{search:false})).toMatchObject({proven:true,checked:true})
  const forged=Object.create(nat) as typeof nat
  forged.store=name=>({[name]:new Term({op:'var',name:'?forged-ghost'})})
  expect(()=>r.law('forged ghost',()=>exists(forged,k=>k.eq(0),{start:0,step:k=>k}))).toThrow('free reserved')
})

test('composition preserves raw quantified provenance but not forged copies',()=>{
  const part=rule('part').maps({M:0}).step(()=>({}))
  const original=everyKey(k=>new MapRef('M',0).at(k).atLeast(0))
  const placed=side(part.machine,'a_',original.c)
  const r=rule('composed raw condition').maps({a_M:0}).flags(()=>({valid:new Cond(placed)})).step(()=>({}))
  const law=r.law('placed cells natural',()=>new Cond(placed))
  expect(proveRule(r,[law],{search:false})).toMatchObject({proven:true,checked:true})
  expect(JSON.stringify(r.machine)).not.toContain('?k')
  const forged=side(part.machine,'a_',JSON.parse(JSON.stringify(original.c)))
  expect(()=>r.law('forged placed condition',()=>new Cond(forged))).toThrow('free reserved')
})
