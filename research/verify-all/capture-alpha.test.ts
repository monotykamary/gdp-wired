import {expect,test} from 'bun:test'
import {alphaProjection as alpha} from './capture-alpha.ts'
const variable=(name:string)=>({op:'var',name}),body=(name:string)=>({op:'<=',a:variable(name),b:{op:'const',value:1}}),all=(key:string,c:object)=>({op:'all',key,c})
test('free names cannot impersonate canonical binders',()=>{
 expect(alpha(all('g',body('__verify_bound_0')))).not.toEqual(alpha(all('h',body('h'))))
 expect(alpha(all('g',body('free')))).not.toEqual(alpha(all('h',body('h'))))
})
test('valid binder alpha conversion preserves comparison and free names',()=>{
 expect(alpha(all('g',body('g')))).toEqual(alpha(all('h',body('h'))))
 expect(alpha(all('g',body('free')))).toEqual(alpha(all('h',body('free'))))
 expect(alpha({each:'g',value:variable('g')})).toEqual(alpha({each:'h',value:variable('h')}))
 expect(alpha({key:'g',term:variable('g')})).toEqual(alpha({key:'h',term:variable('h')}))
})
test('nested shadowing and witness scope are respected',()=>{
 expect(alpha(all('g',all('g',body('g'))))).toEqual(alpha(all('a',all('b',body('b')))))
 expect(alpha(all('g',all('h',body('g'))))).not.toEqual(alpha(all('a',all('b',body('b')))))
 expect(alpha({...all('g',body('g')),witness:variable('g')})).not.toEqual(alpha({...all('h',body('h')),witness:variable('h')}))
})
