import {test,expect} from 'bun:test'
import {installUnitPublisher} from './unit-publisher.ts'
import {meterKeys,readUnitSnapshot} from './unit-snapshot.ts'
const fixture=()=>{const core:Record<string,number>={},costs:Record<string,number>={},epr={n:0};meterKeys.forEach((k,i)=>{if(k!=='epr')(i<12||k==='cdclNodes'?costs:core)[k]=0});return{core,costs,epr}}
test('counter identity and final values survive observation',()=>{const{core,costs,epr}=fixture(),observer=installUnitPublisher(core,costs,epr);core.evals!+=7;costs.fm!+=2;epr.n+=3;const snap=readUnitSnapshot(observer.buffer,meterKeys.map(()=>1));expect(snap.valid).toBe(true);expect(snap.units).toBe(12);observer.restore();observer.restore();expect(core.evals).toBe(7);expect(Object.getOwnPropertyDescriptor(core,'evals')?.writable).toBe(true)})
test('a missing counter refuses installation before mutation',()=>{const{core,costs,epr}=fixture();delete core.evals;expect(()=>installUnitPublisher(core,costs,epr)).toThrow();expect(Object.getOwnPropertyDescriptor(costs,'fm')?.writable).toBe(true)})
