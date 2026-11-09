import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {brotliCompressSync} from 'node:zlib'
import {capturedFamily,identity} from './range-regression-input.ts'
const family={machine:{name:'fixture',params:[]},laws:[{name:'a',holds:{op:'=',a:0,b:0}}]}
function capture(){const text=JSON.stringify(family),bytes=brotliCompressSync(Buffer.from(JSON.stringify({'family-source.json':text})));return {artifact:'mldr-incl-production-capture',omitted:0,sha256:createHash('sha256').update(bytes).digest('hex'),data:bytes.toString('base64')}}
test('exact family is recovered only after checking the compressed hash',()=>{
 const row=capture(),found=capturedFamily(JSON.stringify(row));expect(found.family).toEqual(family)
 expect(()=>capturedFamily(JSON.stringify({...row,sha256:'0'.repeat(64)}))).toThrow('capture hash mismatch')
})
test('missing, ambiguous, or incomplete capture is rejected',()=>{
 const row=JSON.stringify(capture());expect(()=>capturedFamily('')).toThrow()
 expect(()=>capturedFamily(row+'\n'+row)).toThrow()
 expect(()=>capturedFamily(JSON.stringify({...capture(),omitted:1}))).toThrow()
})
test('identity ignores object key order, never array order or a changed clause',()=>{
 expect(identity({b:2,a:1})).toBe(identity({a:1,b:2}))
 expect(identity([1,2])).not.toBe(identity([2,1]));expect(identity(family)).not.toBe(identity({...family,laws:[]}))
})
