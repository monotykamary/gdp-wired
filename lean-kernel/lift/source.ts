/// <reference types="node" />
import {createHash} from 'node:crypto'
import {lstatSync, readFileSync} from 'node:fs'
import type {Machine, Law} from '../../core/machine.ts'
import type {NativeBundle} from './proof-capture.ts'

export type LiftTheoremNames={family:string,source:string[]}
export type GenericLiftSource = {schema:'gdp-lift-source/v1', id:string, machine:Machine, laws:Law[], theorems?:LiftTheoremNames}
export const sha256 = (data:string|Uint8Array):string => createHash('sha256').update(data).digest('hex')

// JSON cannot retain functions, accessors, cycles, sparse arrays, IEEE special
// values or object identity. Reject those, rather than silently dropping them.
// Undefined OPTIONAL OBJECT members are the sole normalization: JSON has no
// spelling for them. All other AST and metadata keys participate in equality.
export function sourceStructure(value:unknown):string {
  const active=new Set<object>(); let nodes=0
  const visit=(v:unknown, depth:number):string=>{
    if(++nodes>2000000||depth>512)throw Error('source structure limit exceeded')
    if(v===null||typeof v==='string'||typeof v==='boolean')return JSON.stringify(v)
    if(typeof v==='number'){
      if(!Number.isFinite(v)||Object.is(v,-0))throw Error('source JSON cannot represent this number exactly')
      return JSON.stringify(v)
    }
    if(!v||typeof v!=='object')throw Error('source JSON cannot represent functions or non-data values')
    if(active.has(v))throw Error('source JSON cannot represent cycles')
    const proto=Object.getPrototypeOf(v)
    if(proto!==Object.prototype&&proto!==null&&proto!==Array.prototype)throw Error('source JSON cannot represent this prototype')
    active.add(v)
    try {
      if(Array.isArray(v)){
        if(Reflect.ownKeys(v).some(k=>k!=='length'&&(typeof k!=='string'||!/^\d+$/.test(k)||Number(k)>=v.length)))throw Error('source array has non-JSON metadata')
        const items:string[]=[]
        for(let i=0;i<v.length;i++){
          const d=Object.getOwnPropertyDescriptor(v,String(i))
          if(!d||!('value'in d))throw Error('source JSON cannot represent sparse/accessor arrays')
          items.push(visit(d.value,depth+1))
        }
        return '['+items.join(',')+']'
      }
      const entries:[string,unknown][]=[]
      for(const key of Reflect.ownKeys(v)){
        if(typeof key!=='string')throw Error('source JSON cannot represent symbol metadata')
        const d=Object.getOwnPropertyDescriptor(v,key)!
        if(!('value'in d))throw Error('source JSON cannot represent accessors')
        if(!d.enumerable)throw Error('source JSON cannot represent hidden metadata')
        if(d.value!==undefined)entries.push([key,d.value])
      }
      entries.sort(([a],[b])=>a<b?-1:a>b?1:0)
      return '{'+entries.map(([k,x])=>JSON.stringify(k)+':'+visit(x,depth+1)).join(',')+'}'
    } finally {active.delete(v)}
  }
  return visit(value,0)
}

export function readBoundedData(path:string,maxBytes:number):Uint8Array {
  if(!Number.isSafeInteger(maxBytes)||maxBytes<1)throw Error('finite positive file limit required')
  const stat=lstatSync(path)
  if(!stat.isFile()||stat.size>maxBytes)throw Error('invalid or oversized data file: '+path)
  const bytes=readFileSync(path)
  if(bytes.length!==stat.size||bytes.length>maxBytes)throw Error('data file changed: '+path)
  return bytes
}
// Match Buffer's UTF-8 decoding, including retaining a leading BOM for JSON
// to reject. Only portable byte-array/string types cross this module boundary.
export function dataText(bytes:Uint8Array):string {
  return new TextDecoder('utf-8',{ignoreBOM:true}).decode(bytes)
}
export function readLiftSource(path:string,maxBytes=64*1024*1024):{source:GenericLiftSource,sourceSha256:string} {
  const bytes=readBoundedData(path,maxBytes), input:unknown=JSON.parse(dataText(bytes))
  if(!input||typeof input!=='object'||Array.isArray(input))throw Error('expected gdp-lift-source/v1 JSON object')
  const source=input as GenericLiftSource
  if(Object.keys(source).filter(k=>k!=='theorems').sort().join(',')!=='id,laws,machine,schema'||source.schema!=='gdp-lift-source/v1'||typeof source.id!=='string'||!/^[A-Za-z][A-Za-z0-9_]*$/.test(source.id)||source.id.length>75)throw Error('invalid gdp-lift-source/v1 envelope')
  const m=source.machine
  if(!m||typeof m!=='object'||Array.isArray(m)||typeof m.name!=='string'||!Array.isArray(m.params)||!Array.isArray(m.inputs)||!m.state||typeof m.state!=='object'||!m.step||typeof m.step!=='object'||!Array.isArray(source.laws)||!source.laws.length)throw Error('invalid source machine or nonempty laws')
  sourceStructure({machine:m,laws:source.laws})
  if(source.theorems!==undefined){
    const names=source.theorems
    if(!names||typeof names!=='object'||Array.isArray(names)||Object.keys(names).sort().join(',')!=='family,source'||!Array.isArray(names.source)||names.source.length!==source.laws.length)throw Error('invalid output theorem naming contract')
    const all=[names.family,...names.source]
    if(all.some(n=>typeof n!=='string'||! /^(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*$/.test(n))||new Set(all).size!==all.length)throw Error('invalid or duplicate output theorem name')
  }
  if(Object.keys(m.fns??{}).length)throw Error('source functions are unsupported; no function deserialization')
  return {source,sourceSha256:sha256(bytes)}
}

export function assertSourceMatches(source:GenericLiftSource,bundle:NativeBundle):void {
  if(sourceStructure({machine:source.machine,laws:source.laws})!==sourceStructure(bundle.original))throw Error('source machine/law AST or metadata differs from capsule original')
}
export function sourceLeanId(id:string):string {
  if(!/^[A-Za-z][A-Za-z0-9_]*$/.test(id)||id.length>75)throw Error('unsafe source identifier (max 75 characters, for the 80-character bapa_ name bound)')
  return 'bapa_'+id
}
