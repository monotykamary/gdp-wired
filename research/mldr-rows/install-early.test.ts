import {expect,test} from 'bun:test'
import {readFileSync} from 'node:fs'
import {installEarly} from './install-early.ts'
const fixture=`prefix\n    let built = build()
    let countCompleted = false
    const completeCounts = (): boolean => {
      const completion = completeCountLawInstances(modelLaws, at, ts, filter, generation.tick)
      return !!completion
    }
    let decideStep = decisions.get(id)
    if (completeCounts()) build()
    if (completeCounts()) build()
`
for(const mode of ['early','row-first'] as const)test(mode+' moves the same bounded completion and retains both fallbacks',()=>{
 const next=installEarly(fixture,mode)
 expect(next.indexOf('let countCompleted')).toBeLessThan(next.indexOf('let built'))
 expect(next.match(/if \(completeCounts\(\)\)/g)).toHaveLength(2)
 expect(next.match(/if \(pass\) completeCounts\(\)/g)).toHaveLength(1)
 expect(next).toContain('generation.tick')
 expect(next.includes('completionTerms')).toBe(mode==='row-first')
 expect(next).not.toContain('Inv1758')
})
test('unexpected source anchors fail closed',()=>{
 expect(()=>installEarly(fixture+fixture,'early')).toThrow('anchors changed')
 expect(()=>installEarly(fixture.replace('modelLaws, at, ts,','other,'),'early')).toThrow('unexpected completion block')
})
test('real source keeps exactly one completion implementation',()=>{
 const source=readFileSync('core/counts.ts','utf8')
 // This test runs on the already transformed disposable copy.
 expect(source.match(/const completeCounts =/g)).toHaveLength(1)
 expect(source.match(/if \(completeCounts\(\)\)/g)).toHaveLength(2)
})
