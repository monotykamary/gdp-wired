import {expect,test} from 'bun:test'
import {nativeWireDecoder} from './native-wire.ts'
import {nativeSame,nativeSnapshot} from './source-check.ts'
const object=(id:string,items:unknown[])=>({kind:'object',id,items})
const array=(id:string,items:unknown[])=>({kind:'array',id,items})
const wire=(root:unknown)=>({version:1,root})

test('native wire retains real identity but snapshots keep historical values',()=>{
  const decode=nativeWireDecoder()
  const frame=(id:string,n:number)=>wire(object('1',[['items',array('2',[object(id,[['n',n]])])]]))
  const before=nativeSnapshot(decode(frame('3',1))) as {items:{n:number}[]}
  const after=nativeSnapshot(decode(frame('3',2))) as {items:{n:number}[]}
  expect(before.items[0]!.n).toBe(1);expect(after.items[0]!.n).toBe(2)
  expect(nativeSame(before.items[0],after.items[0])).toBe(true)
  const distinct=nativeSnapshot(decode(frame('4',2))) as {items:{n:number}[]}
  expect(nativeSame(after.items[0],distinct.items[0])).toBe(false)
})

test('native wire preserves aliases without prototype mutation',()=>{
  const decode=nativeWireDecoder()
  const result=decode(wire(object('1',[
    ['a',object('2',[['n',7]])],['b',{kind:'ref',id:'2'}],['__proto__','literal'],
  ]))) as Record<string,unknown>
  expect(result.a).toBe(result.b);expect(Object.getPrototypeOf(result)).toBeNull()
  expect(result.__proto__).toBe('literal')
})

test('native wire rejects malformed identities, references, numbers and bounds',()=>{
  const bad=[
    {version:2,root:null},wire(Number.MAX_SAFE_INTEGER+1),wire({kind:'ref',id:'1'}),
    wire(object('0',[])),wire(object('1',[['x',object('1',[])]])),
    wire({kind:'array',id:'1',items:'not an array'}),wire(object('1',[['x',1],['x',2]])),
    wire({kind:'unknown',id:'1',items:[]}),
  ]
  for(const value of bad) expect(()=>nativeWireDecoder()(value)).toThrow()
  expect(()=>nativeWireDecoder(0)).toThrow()
  expect(()=>nativeWireDecoder(1)(wire(array('1',[object('2',[])])))).toThrow('identity bound')
  expect(()=>nativeWireDecoder(2,1)(wire(array('1',[1])))).toThrow('node bound')
  const decode=nativeWireDecoder()
  decode(wire(array('1',[])))
  expect(()=>decode(wire(object('1',[])))).toThrow('changed kind')
  expect(()=>decode(wire({kind:'ref',id:'1'}))).toThrow('unbound')
})
