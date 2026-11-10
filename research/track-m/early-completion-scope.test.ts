import {expect,test} from 'bun:test'
import {type Law,type Machine,get,n,plus,x} from '../../core/machine.ts'
import {countedAttempts,countsDump} from '../../core/counts.ts'
import {clock,counted,fullRate,withDeadline,withWall} from '../../kernel/prove.ts'

test('early completion scope preserves unary order and defers multi-key tuples only in the candidate',()=>{
 const m:Machine={name:'completion scope',params:[],inputs:[],state:{},maps:{Cells:0},counts:{Total:{j:'countRow',key:'member',below:n(2),body:n(1)}},step:{}}
 const deferred=process.env.LANE_B_EXPECT_DEFER_MULTI==='1',prior=countsDump.on
 try{
  for(const binary of [false,true]){
   const law:Law={name:binary?'false pair bound':'false row bound',forall:'row',...(binary?{keys:['other']}:{}),holds:{op:'<=',a:get('Total',binary?plus(x('row'),x('other')):x('row')),b:n(1)}}
   const phases:string[]=[]
   countsDump.on=e=>{if('phase'in e&&typeof e.phase==='string')phases.push(e.phase)}
   const result=withWall(performance.now()+3000,()=>counted(fullRate,()=>{
    const end=clock()+1000
    return withDeadline(end,()=>countedAttempts(m,[law],new Set(),end).traced(law,[law],1,1000))
   },true))
   expect('proof'in result).toBe(false) // Total=2: no schedule may prove its false INIT.
   const query=phases.indexOf('query'),completion=phases.indexOf('count-completion')
   expect(query).toBeGreaterThanOrEqual(0)
   if(binary&&deferred)expect(completion===-1||completion>query).toBe(true)
   else {expect(completion).toBeGreaterThanOrEqual(0);expect(completion).toBeLessThan(query)}
   expect(phases.filter(p=>p==='count-completion').length).toBeLessThanOrEqual(1)
  }
 }finally{countsDump.on=prior}
})
