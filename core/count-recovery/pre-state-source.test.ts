import {expect,test} from 'bun:test'
import {all,get,less,n,not,same,x} from '../machine.ts'
import {check,mcGoal,type CountCert} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {preStateCountSource} from './pre-state-source.ts'

test('pre-state ceiling sources remove discarded witness instances and preserve original CInst order',()=>{
 const d={j:'row',key:'member',below:n(3),body:n(1)},ds=[{...d,map:'Total'},{...d,map:'Total#'}]
 const cert:Pick<CountCert,'reads'|'insts'>={reads:[['old','Total',n(0)],['new','Total#',n(0)]],insts:[{wit:'kept',below:n(3),terms:[[1,'old']],unit:0},{wit:'discarded',below:n(3),terms:[[1,'new'],[-1,'old']],unit:0}]}
 const pre=same(get('Field',x('kept')),n(0)),post=same(get('Field',x('discarded')),n(0))
 const full=mcGoal([all(pre,post),less(get('Total#',n(0)),get('Total',n(0)))],ds,cert)!,claim=not(pre)
 const before=JSON.stringify({full,cert}),source=preStateCountSource(full,cert,claim,new Map())
 expect(source.cert.reads).toEqual([cert.reads[0]!])
 expect(source.cert.insts).toEqual([cert.insts[0]!])
 expect(source.goal.hyps).toContainEqual(pre)
 expect(source.goal.hyps).toContainEqual(claim)
 expect(JSON.stringify(source.goal)).not.toContain('discarded')
 expect(JSON.stringify(source.goal)).not.toContain('Total#')
 expect(source.goal.hyps.at(-1)).toBe(full.hyps.at(-2))
 expect(JSON.stringify({full,cert})).toBe(before)
 const proof=grow(source.goal,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in proof).toBe(true)
 if('tree'in proof){
  expect(check(source.goal,proof.tree)).toBe(true)
  const target={...full,hyps:[...full.hyps,claim]},lifted=widen(source.goal,target,proof.tree)
  expect(lifted).toBeDefined()
  if(lifted)expect(check(target,lifted)).toBe(true)
 }
})
