import {expect,test} from 'bun:test'
import {get,less,n,not,same,x,type Machine} from '../../core/machine.ts'
import {checkMC,mcGoal} from '../../kernel/kernel.ts'
import {clock,grow} from '../../kernel/prove.ts'
import {modelCountPicks} from './model-count-picks.ts'

test('model count picks retain distinct symbolic witnesses and remain kernel checked',()=>{
 const m:Machine={name:'members',params:[],inputs:[],state:{},maps:{A:0},step:{}},decls=[{map:'Total',j:'row',key:'k',below:n(3),body:get('A',x('k'))}]
 const cert={reads:[['count','Total',n(0)]] as [string,string,ReturnType<typeof n>][],insts:['alpha','beta'].map(wit=>({wit,below:n(3),unit:0,terms:[[1,'count']] as [number,string][]}))}
 const model={count:1,alpha:0,beta:1,'A[alpha:1]':1,'A[beta:1]':1},picks=modelCountPicks(m,decls,cert,model)
 expect(picks).toEqual([['count',[x('alpha'),x('beta')]]])
 const hyps=[less(x('alpha'),n(3)),less(x('beta'),n(3)),not(same(x('alpha'),x('beta'))),same(get('A',x('alpha')),n(1)),same(get('A',x('beta')),n(1)),less(get('Total',n(0)),n(2))]
 const c={...cert,picks},goal=mcGoal(hyps,decls,c)!,proof=grow(goal,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in proof).toBe(true)
 if('tree'in proof)expect(checkMC(hyps,decls,{...c,tree:proof.tree})).toBe(true)
 expect(modelCountPicks(m,decls,cert,{...model,count:2})).toEqual([])
 const aliased=[...hyps.filter((_,i)=>i!==2),same(x('alpha'),x('beta'))],counter=grow(mcGoal(aliased,decls,c)!,new Map(),{nodes:0,until:clock()+1000})
 expect('tree'in counter).toBe(false)
})
