import {expect,test} from 'bun:test'
import {type Machine,all,any,atMost,get,n,x} from '../machine.ts'
import {type CountCert,check,mcGoal} from '../../kernel/kernel.ts'
import {clock,grow,widen} from '../../kernel/prove.ts'
import {fieldOnlyGoal} from './field-only.ts'
const m:Machine={name:'field projection',params:[],inputs:[],state:{},counts:{Rows:{j:'r',key:'k',below:n(2),body:n(1)}},step:{}}
const cert:Pick<CountCert,'reads'|'insts'>={reads:[['amount','Rows',n(0)]],insts:[]}
test('field projection only weakens premises and transports a checked proof',()=>{
 const field=atMost(x('value'),n(1)),count=atMost(get('Rows',n(0)),n(2)),g={name:'field',hyps:[all(field,count),{op:'not' as const,x:field}]}
 const small=fieldOnlyGoal(g,m,cert)!
 expect(small.hyps[0]).toEqual(all(field))
 const result=grow(small,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in result).toBe(true)
 if('tree'in result){const tree=widen(small,g,result.tree);expect(tree).toBeDefined();if(tree)expect(check(g,tree)).toBe(true)}
})
test('field projection uses the source conclusion before appended count bindings',()=>{
 const field=atMost(x('value'),n(1)),claim={op:'not' as const,x:field},ds=[{map:'Rows',...m.counts!.Rows!}]
 const goal=mcGoal([field,claim],ds,cert)!
 const projected=fieldOnlyGoal(goal,m,cert,claim)
 expect(projected).toBeDefined()
 expect(projected?.hyps.at(-1)).toBe(claim)
})
test('field projection does not strengthen disjunctions or discard a counted conclusion',()=>{
 const field=atMost(x('value'),n(1)),count=atMost(get('Rows',n(0)),n(2))
 expect(fieldOnlyGoal({name:'field',hyps:[any(field,count),{op:'not',x:field}]},m,cert)?.hyps).toEqual([{op:'not',x:field}])
 expect(fieldOnlyGoal({name:'count',hyps:[field,{op:'not',x:count}]},m,cert)).toBeUndefined()
})
