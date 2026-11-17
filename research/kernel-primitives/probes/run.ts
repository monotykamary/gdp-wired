// Native differential gate. Run on the supercomputer boat only; no local test invocation.
// All wire operands/results are decimal strings; JS Number never carries a value.
import {evaluatePrimitive, type PrimitiveSpec, type Width, type OverflowMode, type DivisionMode} from '../../../kernel/integer-primitives.ts'
import {spawnSync} from 'node:child_process'
import {mkdtempSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, dirname} from 'node:path'
import {fileURLToPath} from 'node:url'

const root = dirname(fileURLToPath(import.meta.url))
const widths: Width[] = [8,16,32,64]
const policies: OverflowMode[] = ['WRAP','SATURATE','TRAP']
const modes: DivisionMode[] = ['FLOOR','TRUNCATING','EUCLIDEAN']
type Case = {spec:PrimitiveSpec, a:bigint, b?:bigint}
const cases: Case[] = []
let seed = 0x51a1f00dn
function random(): bigint {seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n<<64n)-1n);return seed}
function add(spec: PrimitiveSpec,a:bigint,b?:bigint) {cases.push({spec,a,...(b===undefined?{}:{b})})}
for (const width of widths) for (const signed of [false,true]) {
  const modulus=1n<<BigInt(width), min=signed?-(modulus>>1n):0n, max=signed?(modulus>>1n)-1n:modulus-1n
  const distinct=(xs:bigint[])=>[...new Set(xs.map(x=>x.toString()))].map(BigInt).filter(x=>x>=min&&x<=max)
  const edge=distinct([min,min+1n,min+2n,-3n,-2n,-1n,0n,1n,2n,3n,max-2n,max-1n,max,
    ...Array.from({length:6},()=>min+random()%(max-min+1n))])
  const casts=[min-1n,min,max,max+1n,-1n,0n,1n,1n<<64n,-(1n<<64n),
    (1n<<100n)+123456789n,-((1n<<100n)+123456789n)]
  for(const overflow of policies) {
    for(const a of casts) add({width,signed,operation:'cast',overflow},a)
    for(const a of edge) {
      add({width,signed,operation:'neg',overflow},a)
      for(const b of edge) {
        for(const operation of ['add','sub','mul'] as const) add({width,signed,operation,overflow},a,b)
        for(const division of modes) for(const operation of ['div','rem'] as const)
          add({width,signed,operation,overflow,division},a,b)
      }
    }
  }
}
function command(cmd:string[],input?:string) {
  if (!cmd.length) throw new Error('empty native command')
  const r=spawnSync(cmd[0]!,cmd.slice(1),{cwd:root,input,encoding:'utf8',maxBuffer:32*1024*1024,timeout:120_000})
  if(r.error||r.status!==0) throw new Error(`${cmd[0]} failed: status=${r.status} signal=${r.signal} error=${r.error ?? ''} stderr=${r.stderr?.slice(0,1200)}`)
  return r.stdout
}
const directory=mkdtempSync(join(tmpdir(),'kernel-primitive-probes-'))
const reports: unknown[]=[]
let failures=0
try {
  const sources: [string,string[]][] = [
    ['C',['cc','-x','c','-std=gnu11','-O2','-Wall','-Wextra','-Werror','-fsanitize=undefined','-fno-sanitize-recover=all',join(root,'native.c.in'),'-o',join(directory,'probe-c')]],
    ['Rust',['rustc','-O',join(root,'native.rs'),'-o',join(directory,'probe-rust')]],
    ['Go',['go','build','-o',join(directory,'probe-go'),join(root,'native.go')]],
    ['Python',[]],
  ]
  const input=cases.map(({spec,a,b})=>`${spec.width} ${Number(spec.signed)} ${spec.operation} ${spec.overflow} ${spec.division??'-'} ${a} ${b??0n}`).join('\n')+'\n'
  for(const [language,compile] of sources) {
    if(compile.length) command(compile)
    const executable=language==='Python'?['python3',join(root,'native.py')]:[join(directory,`probe-${language.toLowerCase()}`)]
    const lines=command(executable,input).trimEnd().split('\n')
    const mismatches: unknown[]=[]
    if(lines.length!==cases.length) throw new Error(`${language}: expected ${cases.length} native receipts, got ${lines.length}`)
    for(let i=0;i<cases.length;i++) {
      const {spec,a,b}=cases[i]!; const expected=evaluatePrimitive(spec,a,b)
      const line=lines[i]!;const match=/^(OK (-?(?:0|[1-9][0-9]*))|ERR ([a-z_]+))$/.exec(line)
      if(!match) throw new Error(`${language}: malformed native receipt at ${i}: ${line.slice(0,160)}`)
      const actual=match[2]!==undefined?{ok:true,value:match[2]}:{ok:false,reason:match[3]}
      // Error text is diagnostic, not semantic equality. Failure versus success IS semantic.
      if(expected.ok!==actual.ok || (expected.ok && expected.value.toString()!==('value' in actual?actual.value:undefined))) {
        failures++;if(mismatches.length<12)mismatches.push({index:i,spec,a:a.toString(),...(b===undefined?{}:{b:b.toString()}),
          expected:expected.ok?{ok:true,value:expected.value.toString()}:{ok:false,reason:expected.reason},actual})
      }
    }
    reports.push({language,cases:cases.length,mismatches:failures-(reports as {mismatches:number}[]).reduce((n,r)=>n+r.mismatches,0),sample:mismatches})
  }
  console.log(JSON.stringify({kind:'kernel-primitives-native-probe',version:1,seed:'0x51a1f00d',caseCount:cases.length,
    comparisons:cases.length*4,failures,reports}))
  if(failures) process.exitCode=1
} catch(error) {
  console.log(JSON.stringify({kind:'kernel-primitives-native-probe',version:1,caseCount:cases.length,failures:failures+1,
    fatal:String(error),reports}))
  process.exitCode=1
} finally {rmSync(directory,{recursive:true,force:true})}
