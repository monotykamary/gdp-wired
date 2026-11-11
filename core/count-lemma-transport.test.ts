import {expect,test} from 'bun:test'
import {type Goal,type LemmaCut,type Path,canon,checkGoalLemmas} from '../kernel/kernel.ts'
import {atMost,n,same,x} from './machine.ts'
import {solve,type Lin} from './solver.ts'
import {rowsAt} from '../kernel/prove.ts'
import {transportCountLemmas} from './count-lemma-transport.ts'
const bound=atMost(x('q'),n(3)),op=same(x('op'),n(5)),scope={assumed:op,when:[{op:1,'1':-5},{op:-1,'1':5}] as Lin[]}
const goal=(hyps:Goal['hyps']):Goal=>({name:'slice fixture',hyps})
function lemma(g:Goal,cut:Lin,slice:number[]):LemmaCut{const path:Path=new Map([[canon(cut),{lin:cut,holds:false}]]),out=solve(rowsAt({...g,hyps:slice.map(i=>g.hyps[i]!)},path),500);if(out.kind!=='refuted')throw Error('open lemma fixture');return {cut,when:[],slice,tree:{leaf:out.steps}}}
function checked(g:Goal,lemmas:LemmaCut[]){const out=solve(rowsAt(g,new Map()),500);if(out.kind!=='refuted')throw Error('open main fixture');return checkGoalLemmas(g,{leaf:out.steps},lemmas)}
test('reorders a sliced premise, rebases its proof, and leaves the input untouched',()=>{const source=goal([bound]),target=goal([atMost(n(4),x('q')),bound]),l=lemma(source,{q:1,'1':-3},[0]),before=JSON.stringify(l),out=transportCountLemmas(source,target,[l],scope,Infinity);expect(out?.[0]?.slice).toEqual([1]);expect(checked(target,out!)).toBe(true);expect(JSON.stringify(l)).toBe(before)})
test('discharges only the fixed operation assumption into exact scope rows',()=>{const source=goal([op]),target=goal([bound,atMost(n(4),x('q'))]),l=lemma(source,{op:1,'1':-5},[0]),out=transportCountLemmas(source,target,[l],scope,Infinity);expect(out?.[0]?.slice).toEqual([]);expect(checked(target,out!)).toBe(true)})
test('does not discharge the operation assumption under a wrong scope',()=>{const source=goal([op]),target=goal([bound,atMost(n(4),x('q'))]),l=lemma(source,{op:1,'1':-5},[0]);expect(transportCountLemmas(source,target,[l],{assumed:op,when:[{op:1,'1':-6},{op:-1,'1':6}]},Infinity)).toBeUndefined()})
test('rejects a missing non-operation premise',()=>{const source=goal([bound]),l=lemma(source,{q:1,'1':-3},[0]);expect(transportCountLemmas(source,goal([]),[l],scope,Infinity)).toBeUndefined()})
test('rejects an ambiguous destination and merged source occurrences',()=>{const source=goal([bound]),l=lemma(source,{q:1,'1':-3},[0]);expect(transportCountLemmas(source,goal([bound,bound]),[l],scope,Infinity)).toBeUndefined();expect(transportCountLemmas(goal([bound,bound]),source,[{...l,slice:[0,1]}],scope,Infinity)).toBeUndefined()})
test('does not extend an expired deadline',()=>{const source=goal([bound]);expect(transportCountLemmas(source,source,[lemma(source,{q:1,'1':-3},[0])],scope,-Infinity)).toBeUndefined()})
