import {expect,test} from 'bun:test'
import {mkdtempSync,writeFileSync,mkdirSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {extractPython} from '../../core/extract-py.ts'
import {extractGo} from '../../core/extract-go.ts'
import {buildLaw} from '../../core/laws.ts'
import {proveSteps} from '../../core/dsl.ts'

for (const language of ['python','go'] as const) {
  test(`${language}: native journal survives harness timing metadata`,()=>{
    const root=mkdtempSync(join(tmpdir(),'gdp-journal-custody-'))
    try {
      const run=(disabled=false)=>{
        const check={runs:2,depth:3,states:2,probes:false as const,...(disabled?{lawCrossCheck:false}: {})}
        if(language==='python') {
          const file=join(root,'meter.py')
          writeFileSync(file,'class Meter:\n    def __init__(self):\n        self.n = 0\n    def inc(self):\n        self.n += 1\n')
          return extractPython(file,{entry:'Meter',check})
        }
        writeFileSync(join(root,'go.mod'),'module example.com/custody\n\ngo 1.22\n')
        mkdirSync(join(root,'p'),{recursive:true})
        writeFileSync(join(root,'p','meter.go'),'package p\ntype Meter struct { N uint32 }\nfunc (m *Meter) Inc() { if m.N < 100 { m.N++ } }\n')
        return extractGo(join(root,'p'),{entry:'Meter',check})
      }
      for(const disabled of [false,true]) {
        const x=run(disabled)
        if(!x.ok) throw Error(JSON.stringify(x.refusals))
        expect(x.evidence!.requests).toBeGreaterThan(0)
        const b=buildLaw(x,{name:'nondecreasing',expr:language==='python'?'self.n >= old(self.n)':'N >= old(N)',method:language==='python'?'inc':'Inc'})
        if(b.kind!=='step') throw Error('expected step law')
        const verdict=proveSteps(x.rule!,x.invariants??[],[b.law],{search:false,from:'any'})
        if(disabled) expect(verdict).toMatchObject({proven:false,checked:false,kernelProven:true,translation:'unchecked'})
        else {
          expect(verdict).toMatchObject({proven:true,checked:true,translation:'sampled'})
          expect(verdict.translationChecks).toBeGreaterThan(0)
        }
      }
    } finally {rmSync(root,{recursive:true,force:true})}
  },180000)
}
