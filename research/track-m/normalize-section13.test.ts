import {test,expect} from 'bun:test'
import {normalizeSection13} from './normalize-section13.ts'
test('publication drops columns without changing raw receipt data',()=>{
 const r={columns:[1],closed:true,trace:{frames:[]},units:50,sources:[]};const n=normalizeSection13(r)
 expect('columns'in n).toBe(false);expect(r.columns).toEqual([1]);expect(n.units).toBe(50)
})
test('a pre-leaf cap carries actual closure guards and no invented model',()=>{
 const path=[['p',{lin:{p:1},holds:true}]],r=normalizeSection13({closed:false,firstFailure:{kind:'budget',path:[]},trace:{frames:[{id:0,kind:'closure',meta:{path}}]}})
 expect(r.firstFailure.path).toEqual(path);expect(r.firstFailure.numericModel).toBeNull();expect(r.firstFailure.phase).toBe('closure-preparation-before-numeric-leaf')
})
test('a recorded numeric failure is preserved exactly',()=>{
 const failure={kind:'stop',path:[1],capture:{model:{n:1}}};expect(normalizeSection13({closed:false,firstFailure:failure}).firstFailure).toBe(failure)
})
