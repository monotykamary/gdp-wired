import {nativeSnapshot} from './source-check.ts'

// Bindings are retained directly by the journal. Snapshot the decoder's mutable
// canonical objects before any later state/binding frame can update them.
export const snapshotNativeBindings = (decode: (wire: unknown) => unknown, wire: unknown): Record<string, unknown> => nativeSnapshot(decode(wire)) as Record<string, unknown>

// Decode identity-bearing snapshots returned by the real native harness. This
// is observation transport only: no model values or proof results are supplied.
export function nativeWireDecoder(maxObjects=100000, maxNodes=10000):(wire:unknown)=>unknown {
  if(!Number.isSafeInteger(maxObjects)||maxObjects<1||!Number.isSafeInteger(maxNodes)||maxNodes<1) throw Error('invalid native snapshot bounds')
  const objects=new Map<string,{kind:string,value:object}>()
  return wire=>{
    let nodes=0
    const seen=new Set<string>()
    const record=(value:unknown):Record<string,unknown>=>{
      if(value===null||typeof value!=='object'||Array.isArray(value)) throw Error('invalid native snapshot node')
      return value as Record<string,unknown>
    }
    const decode=(value:unknown):unknown=>{
      if(++nodes>maxNodes) throw Error('native snapshot exceeds node bound')
      if(value===null||typeof value==='string'||typeof value==='boolean') return value
      if(typeof value==='number') {if(!Number.isSafeInteger(value)) throw Error('unsafe native snapshot number'); return value}
      const node=record(value),id=node.id,kind=node.kind
      if(typeof id!=='string'||!/^[1-9][0-9]*$/.test(id)) throw Error('invalid native snapshot identity')
      if(kind==='ref') {if(!seen.has(id)) throw Error('unbound native snapshot reference'); return objects.get(id)!.value}
      if(kind!=='object'&&kind!=='array'&&kind!=='map'&&kind!=='set') throw Error('unsupported native snapshot kind')
      if(seen.has(id)) throw Error('duplicate native snapshot identity')
      seen.add(id)
      let kept=objects.get(id)
      if(kept&&kept.kind!==kind) throw Error('native snapshot identity changed kind')
      if(!kept) {
        if(objects.size>=maxObjects) throw Error('native snapshot exceeds identity bound')
        const fresh:object=kind==='array'?[]:kind==='map'?new Map<unknown,unknown>():kind==='set'?new Set<unknown>():Object.create(null) as object
        kept={kind,value:fresh};objects.set(id,kept)
      }
      if(!Array.isArray(node.items)) throw Error('invalid native snapshot entries')
      if(kind==='array') {
        const target=kept.value as unknown[];target.length=0
        for(const item of node.items) target.push(decode(item))
      } else if(kind==='set') {
        const target=kept.value as Set<unknown>;target.clear()
        for(const item of node.items) {
          const value=decode(item);if(target.has(value)) throw Error('duplicate native snapshot set item')
          target.add(value)
        }
      } else if(kind==='map') {
        const target=kept.value as Map<unknown,unknown>;target.clear()
        for(const item of node.items) {
          if(!Array.isArray(item)||item.length!==2||(typeof item[0]!=='string'&&typeof item[0]!=='number')) throw Error('invalid native snapshot map entry')
          const key=decode(item[0]);if(target.has(key)) throw Error('duplicate native snapshot map key')
          target.set(key,decode(item[1]))
        }
      } else {
        const target=kept.value as Record<string,unknown>
        for(const key of Object.keys(target)) delete target[key]
        for(const item of node.items) {
          if(!Array.isArray(item)||item.length!==2||typeof item[0]!=='string'||Object.hasOwn(target,item[0])) throw Error('invalid native snapshot object entry')
          Object.defineProperty(target,item[0],{value:decode(item[1]),writable:true,enumerable:true,configurable:true})
        }
      }
      return kept.value
    }
    const envelope=record(wire)
    if(envelope.version!==1) throw Error('unsupported native snapshot version')
    return decode(envelope.root)
  }
}
