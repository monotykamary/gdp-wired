import {afterAll,expect,test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync,rmSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {extractPython} from '../../core/extract-py.ts'
import {buildLaw,parse,ScalarListQuantifierError} from '../../core/laws.ts'
import {nativeLaw} from '../../core/native-law.ts'
import {proveRule} from '../../core/dsl.ts'
const dir=mkdtempSync(join(tmpdir(),'ordered-source-refusal-'))
afterAll(()=>rmSync(dir,{recursive:true,force:true}))
const scalar=`class Queue:
    def __init__(self):
        self.items: list[int] = []
    def put(self, x: int) -> None:
        self.items.append(x)
    def take(self) -> int:
        if not self.items:
            return -1
        return self.items.pop(0)
`
const file=join(dir,'queue.py');writeFileSync(file,scalar)
const check={runs:20,depth:1,states:0,probes:false} as const
const x=extractPython(file,{check})
const fifo='forall o in old(self.items): forall j in old(self.items): o in self.items or o <= j'
const nonnegative='forall o in self.items: o >= 0'

test('actual FIFO and negative insertion falsify the original scalar-value claims',()=>{
  const values=JSON.parse(execFileSync('python3',['-c',scalar+`\nimport json\nq=Queue()\nq.put(2)\nq.put(1)\nbefore=list(q.items)\nr=q.take()\nafter=list(q.items)\np=Queue()\np.put(-1)\nprint(json.dumps({'before':before,'after':after,'result':r,'negative':p.items}))`],{encoding:'utf8'})) as {before:number[],after:number[],result:number,negative:number[]}
  expect(values).toEqual({before:[2,1],after:[1],result:2,negative:[-1]})
  const observation={where:'actual Python FIFO',method:'take',before:{items:values.before},after:{items:values.after},params:{},inputs:{},bindings:{},args:[],result:values.result,failed:false}
  expect(nativeLaw(parse(fifo),{},parse,{},new Set(['self']))(observation)).toBe(false)
  expect(nativeLaw(parse(nonnegative),{},parse,{},new Set(['self']))({...observation,method:'put',before:{items:[]},after:{items:values.negative},args:[-1]})).toBe(false)
})

test('scalar list quantifiers refuse before a public invariant or step proof can accept positions',()=>{
  expect(x.ok).toBe(true)
  expect(x.names?.find(n=>n.code==='items')?.map).toMatchObject({ordered:true,scalar:true})
  for(const [expr,method] of [[fifo,'take'],[nonnegative,undefined]] as const) {
    let error:unknown
    try {buildLaw(x,{name:'scalar value claim',expr,...(method?{method}:{})})} catch(e){error=e}
    expect(error).toBeInstanceOf(ScalarListQuantifierError)
    expect(error).toMatchObject({shape:'scalar-ordered-list-quantification'})
    expect((error as Error).message).toContain('scalar ordered list')
  }
})

test('one-field records named value remain records, not scalar lists',()=>{
  const source=`from dataclasses import dataclass
@dataclass
class Item:
    value: int
class Records:
    def __init__(self):
        self.items: list[Item] = []
    def put(self, x: int) -> None:
        self.items.append(Item(x))
`
  const path=join(dir,'records.py');writeFileSync(path,source)
  const rec=extractPython(path,{check})
  expect(rec.ok).toBe(true)
  expect(rec.names?.find(n=>n.code==='items')?.map).toMatchObject({ordered:true,scalar:false,fields:['value']})
  const law=buildLaw(rec,{name:'record reflexivity',expr:'forall o in self.items: o.value == o.value'})
  expect(law.kind).toBe('law')
  expect(proveRule(rec.rule!,[...(rec.invariants??[]),law.law],{search:false})).toMatchObject({proven:true,checked:true})
  const unknownKind={...rec,names:rec.names!.map(n=>{if(!n.map?.ordered)return n;const map={...n.map};Reflect.deleteProperty(map,'scalar');return {...n,map}})}
  expect(()=>buildLaw(unknownKind,{name:'untyped item',expr:'forall o in self.items: o.value == o.value'})).toThrow(ScalarListQuantifierError)
})
