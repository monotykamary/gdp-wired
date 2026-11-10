import {test,expect} from 'bun:test'
import {diagnostic as d} from './section10-diagnostic.ts'
import {costs} from '../../core/solver.ts'
import {fullWork} from '../../kernel/prove.ts'
test('empty diagnostic spans and dumps charge no counted work',()=>{d.reset('empty');const start=fullWork();d.run('outer',{},()=>d.run('inner',{},()=>undefined));d.dump();expect(fullWork()).toBe(start);expect(d.frames.map(f=>f.units)).toEqual([0,0])})
test('nested span totals conserve measured work without double counting',()=>{d.reset('nested');const start=costs.goalNodes;try{d.run('outer',{},()=>{costs.goalNodes+=10;d.run('inner',{},()=>{costs.goalNodes+=20});costs.goalNodes+=5});expect(d.frames[0]!.units).toBeCloseTo(35*0.492/250,9);expect(d.frames[0]!.exclusive!+d.frames[1]!.exclusive!).toBeCloseTo(d.frames[0]!.units!,9)}finally{costs.goalNodes=start}})
test('capture and dump never execute deferred source construction',()=>{d.reset('capture');let calls=0;d.capture({closure:0,path:[]},()=>{calls++;return undefined});d.dump();expect(calls).toBe(0)})
test('unbalanced diagnostics are rejected',()=>{d.reset('balance');const outer=d.begin('outer'),inner=d.begin('inner');expect(()=>d.reset('bad')).toThrow();d.end(inner);d.end(outer);expect(d.frames.every(f=>f.end!==undefined)).toBe(true)})
