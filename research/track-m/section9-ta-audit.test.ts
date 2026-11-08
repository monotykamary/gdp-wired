import {test,expect} from 'bun:test'
import {supportsNamedGap} from './section9-ta-audit.ts'
const branch=()=>({name:'complement',queries:[{validModel:true,outcome:'sat',violated:[27,32,77,84]}],attempts:[27,32,77,84].map(originalIndex=>({originalIndex,outcome:'sat',sourceAndScopeValid:true}))})
test('a named gap requires validated SAT sources for every violated fact',()=>expect(supportsNamedGap(branch())).toBe(true))
test('an unknown source is not a generator gap',()=>{const b=branch();b.attempts[0]!.outcome='unknown';expect(supportsNamedGap(b)).toBe(false)})
test('a refuted but unadmitted source is not SAT',()=>{const b=branch();b.attempts[2]!.outcome='refuted-unadmitted';expect(supportsNamedGap(b)).toBe(false)})
test('an invalid model cannot establish a gap',()=>{const b=branch();b.queries[0]!.validModel=false;expect(supportsNamedGap(b)).toBe(false)})
test('the guard branch is not the named complement gap',()=>{const b=branch();b.name='guard';expect(supportsNamedGap(b)).toBe(false)})
test('both requested candidates must be queried even if absent from V',()=>{const b=branch();b.queries[0]!.violated=[77,84];b.attempts=b.attempts.slice(2);expect(supportsNamedGap(b)).toBe(false)})
