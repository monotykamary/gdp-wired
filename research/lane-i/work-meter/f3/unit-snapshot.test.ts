import {test,expect} from 'bun:test'
import {createUnitPublisher,readUnitSnapshot,observeUnitProgress,unitSnapshotBytes,meterKeys} from './unit-snapshot.ts'
import type {Raw} from '../calibration/contract.ts'
const zeros=()=>Object.fromEntries(meterKeys.map(k=>[k,0])) as Raw
const setup=()=>{const buffer=new SharedArrayBuffer(unitSnapshotBytes),p=createUnitPublisher(buffer,zeros()),weights=meterKeys.map(()=>0);weights[0]=2.33;weights[15]=2;return{buffer,p,weights}}
test('weighted units equal the budget summation order',()=>{const{buffer,p,weights}=setup();p.publish('fm',3);p.publish('evals',8);expect(readUnitSnapshot(buffer,weights).units).toBe(2.33*3+2*8)})
test('zero-price raw movement is not unit progress',()=>{const{buffer,p,weights}=setup(),before=readUnitSnapshot(buffer,weights);p.publish('tableCells',100);const after=readUnitSnapshot(buffer,weights);expect(before.sequence).not.toBe(after.sequence);expect(observeUnitProgress(before,after)).toEqual({eligible:true,advanced:false,unchanged:true})})
test('positive-price raw movement advances units',()=>{const{buffer,p,weights}=setup(),before=readUnitSnapshot(buffer,weights);p.publish('evals',1);expect(observeUnitProgress(before,readUnitSnapshot(buffer,weights)).advanced).toBe(true)})
test('version changes cannot starve an atomic monotone scan',()=>{const{buffer,weights}=setup(),before=readUnitSnapshot(buffer,weights);Atomics.add(new Int32Array(buffer,0,4),0,1);const after=readUnitSnapshot(buffer,weights);expect(after.valid).toBe(true);expect(observeUnitProgress(before,after).unchanged).toBe(true)})
test('counter reset fails closed without throwing into the solver',()=>{const{buffer,p,weights}=setup();p.publish('evals',2);p.publish('evals',1);expect(readUnitSnapshot(buffer,weights).valid).toBe(false)})
test('publication rollover fails closed',()=>{const{buffer,p,weights}=setup();Atomics.store(p.control,0,2_000_000_000);p.publish('evals',1);expect(readUnitSnapshot(buffer,weights).valid).toBe(false)})
test('missing or negative weights are rejected',()=>{const{buffer}=setup();expect(()=>readUnitSnapshot(buffer,[])).toThrow();expect(()=>readUnitSnapshot(buffer,meterKeys.map(()=>-1))).toThrow()})
