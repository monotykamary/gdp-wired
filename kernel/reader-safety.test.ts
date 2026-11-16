import {expect,test} from 'bun:test'
import type {E} from '../core/machine.ts'
import {linear} from './kernel.ts'
import {Reader,type Trail} from './reader.ts'

const trail:Trail={get:()=>undefined,stamp:()=>0,size:()=>0,lin:()=>{throw Error('empty trail')}}
const n=(value:number):E=>({op:'const',value})
const read=(e:E)=>new Reader({name:'reader arithmetic safety',hyps:[]},trail).linear(e).lin

test('incremental reader preserves the kernel safe-integer arithmetic boundary',()=>{
  const unsafe:E[]=[
    n(Number.MAX_SAFE_INTEGER+1),
    {op:'add',a:n(Number.MAX_SAFE_INTEGER),b:n(1)},
    {op:'mul',k:0.5,a:n(2)},
    {op:'mul',k:2**32,a:n(2**32)},
    {op:'sub',a:{op:'add',a:n(Number.MAX_SAFE_INTEGER),b:n(1)},b:n(Number.MAX_SAFE_INTEGER)},
  ]
  for(const e of unsafe) {
    expect(linear(e,new Map())).toBeUndefined()
    expect(read(e)).toBeUndefined()
  }
  const safe:E[]=[n(0),n(Number.MAX_SAFE_INTEGER),{op:'var',name:'value'},{op:'mul',k:2,a:n(3)},{op:'add',a:n(20),b:n(22)}]
  for(const e of safe) expect(read(e)).toEqual(linear(e,new Map()))
})
