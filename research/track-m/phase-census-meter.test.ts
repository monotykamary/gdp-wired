import {expect,test} from 'bun:test'
import {PhaseCensus} from './phase-census-meter.ts'
test('wall phases are exclusive and kernel work is not double counted',()=>{
 let now=0;const m=new PhaseCensus(()=>now);m.enabled=true;m.reset()
 m.run('other','all',()=>{now+=2;m.run('demand','proposal',()=>{now+=3;m.run('kernel','check',()=>{now+=5});now+=7});now+=11})
 expect(m.snapshot().exclusiveMs).toEqual({other:13,demand:10,proposals:0,A:0,B:0,C:0,kernel:5,search:0})
})
test('phase-local solver work remains charged to its phase',()=>{
 let now=0;const m=new PhaseCensus(()=>now);m.enabled=true;m.reset()
 m.closure({name:'g'},null,null,()=>{m.phase('A');m.run('search','solve',()=>{now+=3});m.run('kernel','check',()=>{now+=2});m.phase('B');now+=7;m.phase('other');now+=1})
 const s=m.snapshot().exclusiveMs;expect(s.A).toBe(3);expect(s.B).toBe(7);expect(s.kernel).toBe(2);expect(s.other).toBe(1)
})
test('cut-use audit distinguishes offered, core and checked proof references',()=>{
 const m=new PhaseCensus();m.enabled=true;m.reset();const good={op:'var',name:'count'},saved={good,lemma:{when:[],cut:{x:1}},index:0}
 m.closure({name:'g'},null,null,()=>{m.phase('B');m.cut(saved,null,{insts:[{wit:'w'}]});m.phase('other');const l=m.beginLeaf(new Map(),[saved]);m.endLeaf(l,{hyps:[good]},undefined,{stuck:'sat'});m.finishLeaf(l,false)})
 const captured=m.capture();m.reset();const audit=captured.audit(()=>false,()=>new Set());expect(audit.counts.proven).toBe(1);expect(audit.counts.offered).toBe(1);expect(audit.counts.referenced).toBe(0);expect(audit.counts.offeredNotReferenced).toBe(1)
})
