import {expect,test} from 'bun:test'
import {limitMemberSources,rankAnchor} from './install-member-source-rank.ts'
const source=`unchanged flags\n${rankAnchor}\nunchanged admission caps`
test('rank probe narrows only the already ranked source-law list',()=>{
 const result=limitMemberSources(source,2)
 expect(result).toContain('sourceLaws.splice(2)')
 expect(result).toContain(rankAnchor)
 expect(result.startsWith('unchanged flags\n')).toBe(true)
 expect(result.endsWith('unchanged admission caps')).toBe(true)
 expect(limitMemberSources(source,0)).toContain('sourceLaws.splice(0)')
})
test('rank probe refuses invalid limits',()=>{
 for(const rank of [-1,0.5,65,NaN,Infinity])expect(()=>limitMemberSources(source,rank)).toThrow()
})
test('rank probe refuses absent, duplicate, and previously installed anchors',()=>{
 for(const text of ['',`${source}\n${rankAnchor}`,limitMemberSources(source,1)])expect(()=>limitMemberSources(text,1)).toThrow()
})
