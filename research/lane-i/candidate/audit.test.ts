import {expect,test} from 'bun:test'
import {validate} from './audit.ts'
const keys=['fm','fcells','plainRows','values','copies','edges','scan','pivotRows','unitRows','unfoldRows','goalNodes','translateRows','tableCells','checkSteps','astNodes','evals','cubeTests','ticks','cdclNodes','epr']
const fixture=()=>{const raw=Object.fromEntries(keys.map(key=>[key,0]));return {schema:'lane-i-candidate-v1',variant:'original',unitStatus:'UNCALIBRATED',status:'PENDING-D',weights:Object.fromEntries(keys.slice(12).map(key=>[key,1])),raw,units:0,phases:[{parentId:null,raw:{...raw},exclusiveRaw:{...raw}}],result:{verdict:'unknown',proven:false,checked:false}}}
test('a complete zero-work receipt is valid',()=>expect(validate(fixture())).toBe(true))
test('raw root corruption is rejected',()=>{const r=fixture();r.phases[0]!.raw.fm=1;expect(()=>validate(r)).toThrow()})
test('exclusive phase corruption is rejected',()=>{const r=fixture();r.phases[0]!.exclusiveRaw.fm=1;expect(()=>validate(r)).toThrow()})
test('incorrect weighted totals are rejected',()=>{const r=fixture();r.units=1;expect(()=>validate(r)).toThrow()})
test('unchecked proof labels are rejected',()=>{const r=fixture();r.result.verdict='proven';expect(()=>validate(r)).toThrow()})
test('different diagnostic weights are rejected',()=>{const r=fixture();r.weights.epr=2;expect(()=>validate(r)).toThrow()})
