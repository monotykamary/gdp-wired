import {expect,test} from 'bun:test'
import {type C,type Machine,all,any,get,ite,less,n,not,same,x} from '../machine.ts'
import {type CountCert,type CountDecl} from '../../kernel/kernel.ts'
import {memberInclusions} from './member-inclusions.ts'
function fixture(prefix=''){
 const s=(v:string)=>prefix+v,k=x(s('k')),actor=x(s('actor')),other=x(s('other')),q=get(s('Parcel'),k),cell=(map:string,at= k)=>get(s(map),at)
 const flag=(c:C):C=>({op:'all',key:s('k'),c:any(not(same(q,n(1))),c)})
 const m:Machine={name:'arbitrary',params:[],inputs:[s('actor'),s('other')],inputMaps:[s('Parcel')],state:{},maps:{[s('Rows')]:0,[s('Epoch')]:0,[s('Version')]:0},step:{flags:{view:flag(same(cell('Rows'),n(1))),aligned:flag(all(same(cell('Epoch'),cell('Epoch',actor)),same(cell('Version',actor),cell('Version'))))}}}
 const base={j:s('unused'),key:s('k'),below:n(12)},ds:CountDecl[]=[{...base,map:s('Incoming'),body:q},{...base,map:s('Eligible'),body:ite(all(same(cell('Rows'),n(1)),less(cell('Epoch'),cell('Epoch',other)),not(any(less(cell('Epoch',actor),cell('Epoch')),all(same(cell('Epoch',actor),cell('Epoch')),less(cell('Version',actor),cell('Version')))))),n(1),n(0))}]
 const reads:CountCert['reads']=[['input',s('Incoming'),n(0)],['eligible',s('Eligible'),n(0)]]
 return {m,ds,reads,cell,actor,other,s,run:()=>memberInclusions(m,ds,reads)}
}
for(const prefix of ['', 'renamed_'])test('equality consequents discharge reflexive bodies and retain scalar residue '+prefix,()=>{
 const f=fixture(prefix),before=JSON.stringify([f.m,f.ds,f.reads])
 expect(f.run()).toEqual([{positive:'input',negative:'eligible',carried:f.s('Parcel'),below:n(12),guards:[less(f.cell('Epoch',f.actor),f.cell('Epoch',f.other))]}])
 expect(JSON.stringify([f.m,f.ds,f.reads])).toBe(before)
})
test('unknown membership is not treated as implied',()=>{const f=fixture();delete f.m.step.flags!.view;expect(f.run()).toEqual([])})
test('an inequality is not a substitution',()=>{const f=fixture();f.m.step.flags!.aligned={op:'all',key:'k',c:any(not(same(get('Parcel',x('k')),n(1))),less(get('Epoch',x('k')),get('Epoch',x('actor'))))};expect(f.run()).toEqual([])})
test('different domains cannot form an inclusion',()=>{const f=fixture();f.ds[1]!.below=n(13);expect(f.run()).toEqual([])})
test('another carried map does not supply these member facts',()=>{const f=fixture();f.m.inputMaps=['Unrelated'];expect(f.run()).toEqual([])})
test('a still-member-dependent predicate is not a scalar residue',()=>{const f=fixture();const old=f.ds[1]!.body;if(old.op!=='if')throw new Error('fixture');old.c=all(old.c,less(get('Unknown',x('k')),n(4)));expect(f.run()).toEqual([])})
test('without an equality rewrite, ordinary membership stays with the old family',()=>{const f=fixture();f.ds[1]!.body=ite(same(get('Rows',x('k')),n(1)),n(1),n(0));expect(f.run()).toEqual([])})
test('a discharged equality may yield an unconditional candidate, never an asserted cut',()=>{const f=fixture();f.ds[1]!.body=ite(all(same(get('Rows',x('k')),n(1)),same(get('Epoch',x('k')),get('Epoch',x('actor')))),n(1),n(0));expect(f.run()[0]!.guards).toEqual([])})
test('cyclic input is refused before recursive substitution',()=>{const f=fixture();const c:any={op:'not'};c.x=c;f.m.step.flags!.bad=c;expect(f.run()).toEqual([])})
