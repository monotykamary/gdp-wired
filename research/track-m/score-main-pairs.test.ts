import {expect,test} from 'bun:test'
import {compareOutcome,parsePairLog} from './score-main-pairs.ts'
const log=(exit=0,verdict='proven')=>['base','cand'].flatMap(side=>['search','broken'].flatMap(phase=>[
 `PAIR begin side=${side} phase=${phase} id=p baseline=6a3874d3ffff`,
 JSON.stringify({id:'p',[phase]:{verdict:phase==='broken'?'refuted':verdict,ms:12}}),
 `PAIR end side=${side} phase=${phase} exit=${side==='cand'&&phase==='search'?exit:0}`,
])).join('\n')
test('strict pair parser retains both original protocol phases',()=>{const p=parsePairLog(log(),'p');expect(p.base.search.verdict).toBe('proven');expect(p.cand.broken.verdict).toBe('refuted')})
test('outer timeout overrides even an emitted positive result',()=>{const p=parsePairLog(log(137),'p');expect(p.cand.search.verdict).toBe('timeout');expect(compareOutcome('search',p.base.search,p.cand.search)).toBe('regression')})
test('a missing phase or wrong baseline cannot pass',()=>{expect(()=>parsePairLog(log().replace('6a3874d3ffff','844a1baf'),'p')).toThrow();expect(()=>parsePairLog(log().split('\n').slice(0,-1).join('\n'),'p')).toThrow()})
test('main refutations are required, while unresolved negative timing is cost-only',()=>{expect(compareOutcome('broken',{verdict:'refuted',exit:0},{verdict:'unknown',exit:0})).toBe('regression');expect(compareOutcome('broken',{verdict:'unknown',exit:0},{verdict:'timeout',exit:137})).toBe('cost-only');expect(compareOutcome('search',{verdict:'proven',exit:0},{verdict:'timeout',exit:137})).toBe('regression')})
test('new negative proofs are improvements, never false positive proofs',()=>{expect(compareOutcome('broken',{verdict:'unknown',exit:0},{verdict:'refuted',exit:0})).toBe('improvement');expect(compareOutcome('broken',{verdict:'unknown',exit:0},{verdict:'proven',exit:0})).toBe('regression')})
