import {test,expect,afterEach} from 'bun:test'
import {nativeMethod,nativeSpan,readNativeSpan,sameNativeSpan,setNativeSpanBuffer} from './native-spans.ts'
const buffer=()=>new Int32Array(new SharedArrayBuffer(36))
afterEach(()=>setNativeSpanBuffer())
test('receiver/method/arguments retain order and this, before the call span',()=>{
 const shared=buffer(),order:string[]=[];setNativeSpanBuffer(shared)
 const receiver={get method(){order.push('method');expect(readNativeSpan(shared).id).toBe(0);return function(this:object,value:object){order.push('call');expect(this).toBe(receiver);expect(readNativeSpan(shared).id).toBe(3);return value}}}
 const value={};expect(nativeMethod<object>(3,receiver,'method',()=>{order.push('args');expect(readNativeSpan(shared).id).toBe(0);return[value]})).toBe(value)
 expect(order).toEqual(['method','args','call']);expect(readNativeSpan(shared).id).toBe(0)
})
test('nested calls restore the parent and invalidate a crossed capture',()=>{
 const shared=buffer();setNativeSpanBuffer(shared)
 nativeSpan(1,()=>{const before=readNativeSpan(shared);expect(sameNativeSpan(before,readNativeSpan(shared))).toBe(true)
  nativeSpan(2,()=>expect(readNativeSpan(shared).id).toBe(2))
  const after=readNativeSpan(shared);expect(after.id).toBe(1);expect(sameNativeSpan(before,after)).toBe(false)
 });expect(readNativeSpan(shared).depth).toBe(0)
})
test('exception identity survives and span state is restored',()=>{
 const shared=buffer(),error={sentinel:true};setNativeSpanBuffer(shared)
 let caught:unknown;try{nativeSpan(4,()=>{throw error})}catch(e){caught=e}
 expect(caught).toBe(error);expect(readNativeSpan(shared).id).toBe(0);expect(readNativeSpan(shared).valid).toBe(true)
})
test('odd publication sequence and idle spans cannot be attributed',()=>{
 const shared=buffer();Atomics.store(shared,4,1);expect(readNativeSpan(shared).valid).toBe(false)
 Atomics.store(shared,4,2);const idle=readNativeSpan(shared);expect(sameNativeSpan(idle,idle)).toBe(false)
})
test('bounded counter overflow disables attribution without changing the result',()=>{
 const shared=buffer();setNativeSpanBuffer(shared);Atomics.store(shared,6,100_000_000)
 expect(nativeSpan(1,()=>42)).toBe(42);expect(readNativeSpan(shared).overflow).toBe(true);expect(readNativeSpan(shared).valid).toBe(false)
})
test('disabled spans and in-place native sorts retain identity',()=>{
 const values=[3,1,2];expect(nativeMethod<number[]>(1,values,'sort',()=>[(a:number,b:number)=>a-b])).toBe(values);expect(values).toEqual([1,2,3])
})
