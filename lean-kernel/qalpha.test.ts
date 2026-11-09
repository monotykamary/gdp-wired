import {expect,test} from 'bun:test'
import type {C,Law,Machine} from '../core/machine.ts'
import {quantifiedRenames} from './qalpha.ts'
const body: C = {op:'<=',a:{op:'var',name:'g'},b:{op:'const',value:3}}
const machine = (flags: Record<string,C>): Machine => ({name:'alpha-test',params:[],inputs:[],state:{},step:{flags}})
const law: Law = {name:'bound',forall:'a',keys:['g'],holds:body}
test('only colliding local binders change; source objects remain byte-identical', () => {
  const m=machine({good:{op:'all',key:'g',c:body}}),before=JSON.stringify({m,law})
  expect(quantifiedRenames(m,[law])).toEqual([{flag:'good',old:'g',fresh:'qalpha$0'}])
  expect(JSON.stringify({m,law})).toBe(before)
  expect(quantifiedRenames(m,[])).toEqual([])
})
test('fresh names avoid all source and generated certificate names', () => {
  const m={...machine({good:{op:'all',key:'g',c:body}}),params:['qalpha$0']}
  expect(quantifiedRenames(m,[law],['qalpha$1'])).toEqual([{flag:'good',old:'g',fresh:'qalpha$2'}])
})
test('multiple binders, repeated names, and generated law skolems are covered', () => {
  const m=machine({one:{op:'all',key:'g',keys:['h'],c:body},two:{op:'all',key:'g',c:body},three:{op:'all',key:'a#',c:body}})
  const plan=quantifiedRenames(m,[law])
  expect(plan.map(r=>[r.flag,r.old])).toEqual([['one','g'],['two','g'],['three','a#']])
  expect(new Set(plan.map(r=>r.fresh)).size).toBe(plan.length)
})
