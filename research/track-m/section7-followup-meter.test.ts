import {expect,test} from 'bun:test'
import {FollowupMeter} from './section7-followup-meter.ts'
import type {C} from '../../core/machine.ts'
import {type Goal,type Path,type Tree} from '../../kernel/kernel.ts'

test('post-timing audit separates bindings, frames and exact repeated checks',()=>{
 const meter=new FollowupMeter();meter.enabled=true;meter.reset('synthetic')
 const c=():C=>({op:'<=',a:{op:'const',value:0},b:{op:'const',value:1}})
 const own=Array.from({length:398},c),goal:Goal={name:'synthetic',hyps:[...own,c(),c(),c()]}
 meter.noteGoal([own,[],{reads:[['r','size',{op:'var',name:'i'}]],insts:[{wit:'frame$0'},{wit:'w$0'}]}],goal)
 const tree:Tree={leaf:[]},path:Path=new Map(),caller='core/count-recovery/conditional-proof.ts:checked'
 meter.withLeafContext(goal,tree,path,[],()=>{meter.record([goal,tree,path],caller);meter.record([goal,tree,path],caller)})
 meter.withLeafContext(goal,{leaf:[]},path,[],()=>meter.record([goal,{leaf:[]},path],caller))
 meter.seal();const [audit]=meter.audits()
 expect(audit!.calls).toBe(3)
 expect(audit!.provenance[0]!.provenance).toEqual({'obligation':398,'read-binding':1,'frame-count-clause':1,'other-count-clause':1})
 expect(audit!.sameTreeObject.distinct).toBe(2)
 expect(audit!.sameExactCheckedLeaf).toMatchObject({calls:3,distinct:1,repeatedLeaves:1,extraChecks:2})
})

test('disabled audit does not retain data or change return values',()=>{
 const meter=new FollowupMeter();meter.enabled=false
 expect(meter.noteGoal([],undefined)).toBeUndefined()
 meter.record([],'core/count-recovery/conditional-proof.ts:checked');meter.seal()
 expect(meter.audits()).toEqual([])
})
