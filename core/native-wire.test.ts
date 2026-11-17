import {expect,test} from 'bun:test'
import {nativeWireDecoder,snapshotNativeBindings} from './native-wire.ts'
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

test('native binding journal rows retain history when later calls update aliased source state',()=>{
  const decode=nativeWireDecoder()
  const state=(n:number)=>wire(object('1',[['item',object('3',[['n',n]])]]))
  const bindings=(id:string,n:number)=>wire(object(id,[['arg',object('3',[['n',n]])]]))
  const before=nativeSnapshot(decode(state(7))) as {item:{n:number}}
  const first=snapshotNativeBindings(decode,bindings('2',7)) as {arg:{n:number}}
  // The actual input object is also state and is reused by a later call. Both
  // later frames mutate the decoder's canonical id 3, not the saved journal.
  const after=nativeSnapshot(decode(state(8))) as {item:{n:number}}
  const second=snapshotNativeBindings(decode,bindings('4',8)) as {arg:{n:number}}
  expect(first.arg.n).toBe(7)
  expect(second.arg.n).toBe(8)
  expect(before.item.n).toBe(7)
  expect(after.item.n).toBe(8)
  expect(nativeSame(first.arg,before.item)).toBe(true)
  expect(nativeSame(first.arg,after.item)).toBe(true)
  expect(nativeSame(first.arg,second.arg)).toBe(true)
  const distinct=snapshotNativeBindings(decode,wire(object('5',[['arg',object('6',[['n',8]])]]))) as {arg:{n:number}}
  expect(nativeSame(second.arg,distinct.arg)).toBe(false)
  expect(first.arg.n).toBe(7)
})

test('native wire preserves aliases without prototype mutation',()=>{
  const decode=nativeWireDecoder()
  const result=decode(wire(object('1',[
    ['a',object('2',[['n',7]])],['b',{kind:'ref',id:'2'}],['__proto__','literal'],
  ]))) as Record<string,unknown>
  expect(result.a).toBe(result.b);expect(Object.getPrototypeOf(result)).toBeNull()
  expect(result.__proto__).toBe('literal')
})

test('native wire preserves set type, historical membership and identity',()=>{
  const set=(id:string,items:unknown[])=>({kind:'set',id,items})
  const decode=nativeWireDecoder()
  const frame=(items:unknown[])=>wire(object('1',[
    ['values',set('2',items)],['alias',{kind:'ref',id:'2'}],
  ]))
  const before=nativeSnapshot(decode(frame(['alpha','beta']))) as {values:Set<string>,alias:Set<string>}
  const after=nativeSnapshot(decode(frame(['beta','gamma']))) as typeof before
  expect(before.values).toBeInstanceOf(Set)
  expect(after.values).toBeInstanceOf(Set)
  expect(before.values).toEqual(new Set(['alpha','beta']))
  expect(after.values).toEqual(new Set(['beta','gamma']))
  expect(before.alias).toBe(before.values)
  expect(after.alias).toBe(after.values)
  expect(nativeSame(before.values,after.values)).toBe(true)
  expect(()=>decode(wire(array('2',[])))).toThrow('changed kind')
  expect(()=>nativeWireDecoder()(wire(set('1',['alpha','alpha'])))).toThrow('duplicate native snapshot set item')
  expect(()=>nativeWireDecoder(2,1)(wire(set('1',['alpha'])))).toThrow('node bound')
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
