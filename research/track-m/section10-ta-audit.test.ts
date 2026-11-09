import {test,expect} from 'bun:test'
import {passesT10B} from './section10-ta-audit.ts'
const valid=()=>({instanceInViolatedSet:true,modelValid:true,sourceProjectionMatches:true,guardAtom:{x:1,y:-1,'1':1},attempt:{outcome:'checked',coreSize:5,queryCountedUnits:14,saved:{lemma:{when:[{x:1,y:-1,'1':1}]}}},numeric:{numericChecked:true,conditionalChecked:true,queryCountedUnits:19},numericCore:4,countedUnits:34})
test('all T-10A pass lines are explicit',()=>expect(passesT10B(valid())).toBe(true))
test('a dropped guard cannot pass',()=>{const r=valid();r.attempt.saved.lemma.when=[];expect(passesT10B(r)).toBe(false)})
test('source SAT cannot pass',()=>{const r=valid();r.attempt.outcome='sat';expect(passesT10B(r)).toBe(false)})
test('a missing source core cannot pass',()=>{const r=valid();r.attempt.coreSize=0;expect(passesT10B(r)).toBe(false)})
test('a missing numeric core cannot pass',()=>{const r=valid();r.numericCore=0;expect(passesT10B(r)).toBe(false)})
test('unchecked numeric transport cannot pass',()=>{const r=valid();r.numeric.conditionalChecked=false;expect(passesT10B(r)).toBe(false)})
test('nonviolated candidates cannot pass',()=>{const r=valid();r.instanceInViolatedSet=false;expect(passesT10B(r)).toBe(false)})
test('each counted limit is enforced',()=>{for(const k of ['source','numeric','branch']){const r=valid();if(k==='source')r.attempt.queryCountedUnits=30.1;else if(k==='numeric')r.numeric.queryCountedUnits=20.1;else r.countedUnits=120.1;expect(passesT10B(r)).toBe(false)}})
