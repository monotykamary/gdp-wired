import {expect,test} from 'bun:test'
import {type Goal,check} from '../kernel/kernel.ts'
import {clock,rowsAt} from '../kernel/prove.ts'
import {atMost,n,plus,same,x} from './machine.ts'
import {solve} from './solver.ts'
import {rebasePath} from './count-rebase-path.ts'
import {minimalViewFirst} from './count-minimal-view.ts'
test('a projected proof may be replayed, but only against the original goal',()=>{
 const path=new Map(),sum=plus(x('a'),x('b'))
 const full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(x('b'),n(0)),atMost(n(1),sum)]}
 const minimal:Goal={name:'minimal',hyps:[atMost(sum,n(0)),atMost(n(1),sum)]}
 const small=solve(rowsAt(minimal,path),2000);expect(small.kind).toBe('refuted');if(small.kind!=='refuted')return
 expect(rebasePath(minimal,{leaf:small.steps},path,path,Infinity,full)).toBeUndefined()
 const result=minimalViewFirst(full,minimal,path,Infinity)
 expect(result.kind).toBe('proof');expect(result.fallback).toBe(false)
 expect(result.tree&&check(full,result.tree,path)).toBe(true)
})
test('a contradictory projection cannot certify a satisfiable original goal',()=>{
 const full:Goal={name:'full-sat',hyps:[same(x('a'),n(0))]}
 const minimal:Goal={name:'invalid-projection',hyps:[atMost(x('a'),n(0)),atMost(n(1),x('a'))]}
 const result=minimalViewFirst(full,minimal,new Map(),Infinity)
 expect(result.kind).toBe('rejected');expect(result.fallback).toBe(false);expect(result.tree).toBeUndefined()
})
test('only a SAT minimal result permits full-goal search',()=>{
 const full:Goal={name:'full',hyps:[atMost(x('a'),n(0)),atMost(n(1),x('a'))]},minimal:Goal={name:'minimal-sat',hyps:[]}
 const sat=minimalViewFirst(full,minimal,new Map(),Infinity)
 expect(sat.minimalKind).toBe('sat');expect(sat.fallback).toBe(true);expect(sat.kind).toBe('proof')
 const expired=minimalViewFirst(full,minimal,new Map(),clock()-1)
 expect(expired.kind).toBe('unknown');expect(expired.fallback).toBe(false);expect(expired.tree).toBeUndefined()
})
