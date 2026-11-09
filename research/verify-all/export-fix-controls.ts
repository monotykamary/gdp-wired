import {writeFileSync} from 'node:fs'
import type {C,E,Law,Machine} from '../../core/machine.ts'
import {checkCountedLaws,countedObligations,mcGoal,type CountCert,type Tree} from '../../kernel/kernel.ts'
import {grow} from '../../kernel/prove.ts'
import {cmachineToLean,encode} from '../../lean-kernel/emit.ts'
const v=(name:string):E=>({op:'var',name}),n=(value:number):E=>({op:'const',value}),get=(map:string,name:string):E=>({op:'get',map,key:v(name)})
const le=(a:E,b:E):C=>({op:'<=',a,b})
const law:Law={name:'bounded',forall:'a',keys:['g'],holds:{op:'and',xs:[{op:'or',xs:[le(get('B','a'),n(1))]},le(get('B','g'),n(1))]}}
const parts=['import QAlpha\nopen Kern Cert\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n']
for(const mode of ['collision','fresh']){
 const binder=mode==='collision'?'g':'qFresh'
 const m:Machine={name:mode,params:[],inputs:[],state:{},maps:{B:0},inputMaps:['Q'],step:{flags:{good:{op:'all',key:binder,c:le(get('Q',binder),n(1))}},maps:{B:{each:'copyKey',value:{op:'if',c:{op:'flag',name:'good'},then:get('Q','copyKey'),else:n(0)}}}}}
 const instances={bounded:{'?good':[v('a#'),v('g')],bounded:[v('a#'),v('g')]}},certs:Record<string,CountCert>={}
 for(const {goal,decls} of countedObligations(m,[law],instances)){
  const c={reads:[],insts:[]},g=mcGoal(goal.hyps,decls,c)!,out=grow(g)
  if(!('tree'in out))throw Error('control not proven '+mode)
  certs[goal.name]={...c,tree:out.tree}
 }
 const proof={instances,certs},before=JSON.stringify({m,law,proof})
 if(!checkCountedLaws(m,[law],proof))throw Error('control proof not accepted')
 const text=cmachineToLean(mode,m,[law],proof)
 if(JSON.stringify({m,law,proof})!==before)throw Error('emitter mutated source')
 if(text.includes('QAlpha.cmachine_sound')!==(mode==='collision'))throw Error('wrong alpha routing')
 parts.push(text,`#print axioms ${mode}_laws`)
}
const atom:C={op:'<',a:v('x'),b:v('y')},goal={name:'singleton',hyps:[{op:'or',xs:[atom]} as C,{op:'not',x:atom} as C]},tree:Tree={split:{x:1,y:-1,'1':1},yes:{leaf:[{kind:'input',index:2}]},no:{leaf:[{kind:'input',index:1}]}}
const en=encode({name:'singleton',goal,tree})
parts.push(`def singletonGoal : Goal := ⟨${en.tab},${en.hyps}⟩\ndef singletonTree : Tree := ${en.tree}\ntheorem retained_singleton : checkGoal singletonGoal singletonTree = true := by decide +kernel\n#print axioms retained_singleton`)
writeFileSync('/tmp/export-fix-controls.lean',parts.join('\n\n'))
console.log('CONTROLS_GENERATED collision fresh retained-singleton; inputs unchanged')
