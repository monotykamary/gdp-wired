import {expect,test} from 'bun:test'
import {get,n,x,same} from '../../core/machine.ts'
import {mcGoal,type CountDecl,type CountInst,type MapRead} from '../../kernel/kernel.ts'
import {Meter} from './match.ts'
import {recoverCounts} from './recover-counts.ts'
const decls:CountDecl[]=[{map:'C',j:'j',key:'k',below:n(3),body:get('A',x('k'))}]
const reads:MapRead[]=[['r$0','C',n(0)]]
const insts:CountInst[]=[{wit:'w$0',below:n(3),terms:[[1,'r$0']],unit:-1}]
const picks:[string,ReturnType<typeof n>[]][]=[['r$0',[n(0),n(1)]]]
test('count metadata reproduces complete original read, pick and instance rows',()=>{
  const original=mcGoal([],decls,{reads,insts,picks})!,out=recoverCounts(original,decls,reads,new Meter(100000))
  expect(out.reads).toEqual(reads);expect(out.insts).toEqual(insts);expect(out.picks).toEqual(picks)
  expect(mcGoal([],decls,out)).toEqual(original)
  expect(out.countRows).toEqual(original.hyps)
  expect(mcGoal([same(n(0),n(0))],decls,out)!.hyps).toEqual([same(n(0),n(0)),...out.countRows])
})
test('a matched count prefix cannot hide a changed witness/body branch',()=>{
  const original=mcGoal([],decls,{reads,insts})!,bad=structuredClone(original),row=bad.hyps.at(-1)!
  if(row.op!=='or')throw Error('fixture shape');row.xs[1]=same(n(0),n(0))
  expect(recoverCounts(bad,decls,reads,new Meter(100000)).insts).toEqual([])
})
test('absent read metadata and exhausted work are refused',()=>{
  const original=mcGoal([],decls,{reads,insts})!
  expect(()=>recoverCounts(original,decls,[['wrong','C',n(0)]],new Meter(100000))).toThrow('absent')
  expect(()=>recoverCounts(original,decls,reads,new Meter(1))).toThrow('budget')
})
