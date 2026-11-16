import {test,expect} from 'bun:test'
import type {Machine,Law,C,E} from '../../core/machine.ts'
import {deriveTypedRoles} from './roles.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value})
const lt=(a:E,b:E):C=>({op:'<',a,b}),and=(...xs:C[]):C=>({op:'and',xs})
const t=(a:E,b:E):E=>({op:'tup',a,b}),get=(a:E,b:E):E=>({op:'get',map:'relation',key:t(a,b)})
const machine=(typed:boolean):Machine=>({name:'any',params:typed?['leftDomain','rightDomain']:[],inputs:['x','y'],state:{},maps:{relation:0},assume:and(lt(v('x'),typed?v('leftDomain'):n(64)),lt(v('y'),typed?v('rightDomain'):n(64))),step:{maps:{relation:{key:t(v('x'),v('y')),value:n(1)}}}})
const law=(typed:boolean):Law=>({name:'arbitrary',forall:'a',keys:['b'],holds:and(lt(v('a'),typed?v('leftDomain'):n(64)),lt(v('b'),typed?v('rightDomain'):n(64)),{op:'=',a:get(v('a'),v('b')),b:n(1)})})
const fixture=()=>({source:{schema:'gdp-lift-source/v1' as const,id:'not_an_algorithm',machine:machine(true),laws:[law(true)]},old:{machine:machine(false),laws:[law(false)]}})
test('distinct domains and reused local names derive per-coordinate roles',()=>{const {source,old}=fixture();const rs=deriveTypedRoles(source,old,old.machine,old.laws)!;expect(rs.coordinates.relation).toEqual(['leftDomain','rightDomain']);expect(rs.base.x).toBe('leftDomain');expect(rs.scopes[0]!.a).toBe('leftDomain');expect(rs.scopes[0]!.b).toBe('rightDomain')})
test('inconsistent role swap is refused rather than merging independent parameters',()=>{const {source,old}=fixture();source.machine.step.maps!.relation={key:t(v('y'),v('x')),value:n(1)};expect(()=>deriveTypedRoles(source,old,old.machine,old.laws)).toThrow(/mixed typed roles/)})
test('ambiguous coordinate is refused',()=>{const {source,old}=fixture();source.machine.step.maps!.untyped={key:t(v('unknown'),v('y')),value:n(1)};expect(()=>deriveTypedRoles(source,old,old.machine,old.laws)).toThrow(/unclassified tuple/)})
test('law-local variables may reuse a name at different sorts',()=>{const {source,old}=fixture();source.laws.push({name:'other',forall:'a',holds:{op:'=',a:get(n(0),v('a')),b:n(1)}});old.laws.push({name:'other',forall:'a',holds:{op:'=',a:get(n(0),v('a')),b:n(1)}});const rs=deriveTypedRoles(source,old,old.machine,old.laws)!;expect(rs.scopes[0]!.a).toBe('leftDomain');expect(rs.scopes[1]!.a).toBe('rightDomain')})
