import {expect,test} from 'bun:test'
import {atMost,less,n,x} from './machine.ts'
import {type CountCert,type Goal,type LemmaCut,type Path,type Tree,canon,checkGoalLemmas,leafConstraintsReusing,lemmaPath} from '../kernel/kernel.ts'
import {refuteFast} from './solver.ts'
import {countedCertificateHyps,transportCountCertificate} from './count-cert-transport.ts'

const prove=(goal:Goal,path:Path):Tree=>{
 const result=refuteFast(leafConstraintsReusing(goal,path),256)
 if(result?.kind!=='refuted')throw new Error('expected fixture refutation')
 return {leaf:result.steps}
}
function fixture(){
 const goal:Goal={name:'certificate support',hyps:[atMost(x('y'),x('x')),atMost(x('x'),n(0)),less(n(0),x('y'))]},cut={y:1}
 const source={...goal,hyps:goal.hyps.slice(0,2)},path:Path=new Map([[canon(cut),{lin:cut,holds:false}]])
 const lemma:LemmaCut={when:[],cut,slice:[0,1],tree:prove(source,path)},lemmas=[lemma]
 const cert:CountCert={reads:[],insts:[],lemmas,tree:prove(goal,lemmaPath(lemmas,new Map()))}
 return {goal,cert}
}
test('counted support includes independent lemma source slices',()=>{
 const {goal,cert}=fixture()
 expect(checkGoalLemmas(goal,cert.tree,cert.lemmas)).toBe(true)
 expect([...countedCertificateHyps(goal,cert)!].sort((a,b)=>a-b)).toEqual([0,1,2])
})
test('complete counted certificates retain cuts across reordered and enlarged contexts',()=>{
 const {goal,cert}=fixture(),target={...goal,hyps:[atMost(n(0),n(1)),goal.hyps[2]!,goal.hyps[1]!,goal.hyps[0]!]}
 const next=transportCountCertificate(goal,target,cert,performance.now()+2000)
 expect(next).toBeDefined()
 if(next){expect(next.lemmas?.length).toBe(1);expect(checkGoalLemmas(target,next.tree,next.lemmas)).toBe(true)}
 expect(transportCountCertificate(goal,{...goal,hyps:goal.hyps.slice(1)},cert,performance.now()+2000)).toBeUndefined()
})
test('counted certificate transport does not extend expired deadlines',()=>{
 const {goal,cert}=fixture()
 expect(transportCountCertificate(goal,goal,cert,performance.now()-1)).toBeUndefined()
})
