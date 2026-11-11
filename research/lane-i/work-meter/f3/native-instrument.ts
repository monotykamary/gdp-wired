import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {createHash} from 'node:crypto'
// Diagnostic-only, exact-source replacements. The helper preserves receiver,
// method lookup, argument evaluation, result/exception identity, and nesting.
// A call span includes callbacks and GC; it never claims a native instruction.
export function instrumentNativeCanon(root:string,extended=false){
 const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
 const mapping=[
  {id:1,file:'kernel/kernel.ts',name:'canon.lookup',kind:'WeakMap.get'},
  {id:2,file:'kernel/kernel.ts',name:'canon.keys',kind:'Object.keys'},
  {id:3,file:'kernel/kernel.ts',name:'canon.sort',kind:'Array.sort'},
  {id:4,file:'kernel/kernel.ts',name:'canon.map',kind:'Array.map'},
  {id:5,file:'kernel/kernel.ts',name:'canon.join',kind:'Array.join'},
  {id:6,file:'kernel/kernel.ts',name:'canon.remember',kind:'WeakMap.set'},
  {id:7,file:'kernel/kernel.ts',name:'canonFlip.lookup',kind:'WeakMap.get'},
  {id:8,file:'kernel/kernel.ts',name:'canonFlip.keys',kind:'Object.keys'},
  {id:9,file:'kernel/kernel.ts',name:'canonFlip.sort',kind:'Array.sort'},
  {id:10,file:'kernel/kernel.ts',name:'canonFlip.join',kind:'Array.join'},
  {id:11,file:'kernel/kernel.ts',name:'canonFlip.remember',kind:'WeakMap.set'},
  {id:12,file:'core/solver.ts',name:'solver.canon.keys',kind:'Object.keys'},
  {id:13,file:'core/solver.ts',name:'solver.canon.sort',kind:'Array.sort'},
  {id:14,file:'core/solver.ts',name:'solver.canon.map',kind:'Array.map'},
  {id:15,file:'core/solver.ts',name:'solver.canon.stringify',kind:'JSON.stringify'}
 ]
 if(extended)mapping.push(
  {id:16,file:'core/counts.ts',name:'counts.json',kind:'JSON.stringify'},
  {id:17,file:'core/counts.ts',name:'certFor.sort',kind:'Array.sort'},
  {id:18,file:'core/machine.ts',name:'walkOnce.lookup',kind:'Set.has'},
  {id:19,file:'core/machine.ts',name:'walkOnce.remember',kind:'Set.add'},
  {id:20,file:'core/machine.ts',name:'walkOnce.values',kind:'Object.values'})
 const results=[]
 for(const path of ['kernel/kernel.ts','core/solver.ts',...(extended?['core/counts.ts','core/machine.ts']:[])]){
  const full=join(root,path),before=readFileSync(full,'utf8');let after=before
  const replace=(old:string,next:string)=>{assert.equal(after.split(old).length,2,'exact unique anchor: '+old);after=after.replace(old,next)}
  if(path==='kernel/kernel.ts'){
   replace('let out = canonMemo.get(lin)',"let out = nativeMethod<string | undefined>(1, canonMemo, 'get', () => [lin])")
   replace("if (out === undefined) canonMemo.set(lin, (out = Object.keys(lin).sort().map(key => (kernelMeter.tableCells += key.length + 1, `${key}:${lin[key]}`)).join(',')))", "if (out === undefined) nativeMethod(6, canonMemo, 'set', () => [lin, (out = nativeMethod<string>(5, nativeMethod<string[]>(4, nativeMethod<string[]>(3, nativeMethod<string[]>(2, Object, 'keys', () => [lin]), 'sort', () => []), 'map', () => [(key: string) => (kernelMeter.tableCells += key.length + 1, `${key}:${lin[key]}`)]), 'join', () => [',']))])")
   replace('let out = flipMemo.get(lin)',"let out = nativeMethod<string | undefined>(7, flipMemo, 'get', () => [lin])")
   replace('const keys = Object.keys(lin)',"const keys = nativeMethod<string[]>(8, Object, 'keys', () => [lin])")
   replace('for (const key of keys.sort())',"for (const key of nativeMethod<string[]>(9, keys, 'sort', () => []))")
   replace("flipMemo.set(lin, (out = parts.join(',')))", "nativeMethod(11, flipMemo, 'set', () => [lin, (out = nativeMethod<string>(10, parts, 'join', () => [',']))])")
   replace('  return out\n}\n// canon(1', '  return out!\n}\n// canon(1')
   replace('  return out\n}\nexport const atomOf', '  return out!\n}\nexport const atomOf')
  }else if(path==='core/solver.ts') replace('export const canon = (l: Lin) => JSON.stringify(Object.keys(l).sort().map(x => [x, l[x]]))',"export const canon = (l: Lin) => nativeMethod<string>(15, JSON, 'stringify', () => [nativeMethod<unknown[]>(14, nativeMethod<string[]>(13, nativeMethod<string[]>(12, Object, 'keys', () => [l]), 'sort', () => []), 'map', () => [(x: string) => [x, l[x]]])])")
  else if(path==='core/counts.ts'){
   replace('const json = (t: unknown) => JSON.stringify(t)', "const json = (t: unknown) => nativeMethod<string>(16, JSON, 'stringify', () => [t])")
   replace('const rs = all0.sort((x, y) => rank(x) - rank(y))', "const rs = nativeMethod<typeof all0>(17, all0, 'sort', () => [(x: [string,E], y: [string,E]) => rank(x) - rank(y)])")
  }else{
   replace("if (!x || typeof x !== 'object' || seen.has(x)) return", "if (!x || typeof x !== 'object' || nativeMethod<boolean>(18, seen, 'has', () => [x])) return")
   replace('seen.add(x); f(x)', "nativeMethod(19, seen, 'add', () => [x]); f(x)")
   replace('for (const y of Object.values(x)) go(y)', "for (const y of nativeMethod<unknown[]>(20, Object, 'values', () => [x])) go(y)")
  }
  after="import {nativeMethod} from '../research/lane-i/f3/native-spans.ts'\n"+after
  writeFileSync(full,after);results.push({path,before:hash(before),after:hash(after)})
 }
 return {scope:'diagnostic call boundaries, not native-instruction or W evidence',mapping,files:results}
}
