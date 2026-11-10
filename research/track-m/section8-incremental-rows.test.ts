import {test,expect} from 'bun:test'
import {atMost,n,plus,x,type C} from '../../core/machine.ts'
import type {Lin} from '../../core/solver.ts'
import {type Goal,type Path,canon,leafConstraintsReusing} from '../../kernel/kernel.ts'
import {incrementalRows} from './section8-incremental-rows.ts'
test('incremental rows equal the unchanged builder across sibling paths and row aliases',()=>{
 const a=x('a'),b=x('b'),goal:Goal={name:'row differential',hyps:[atMost(a,b),atMost({op:'get',map:'M',key:a},{op:'get',map:'M',key:b}),{op:'<=',a:{op:'if',c:atMost(a,n(2)),then:plus(b,n(1)),else:n(0)},b:n(4)},...Array.from({length:20},(_,i)=>atMost(x('x'+i),n(i+3)))]}
 const atoms:Lin[]=[{a:1,b:-1},{a:-1,b:1},{a:1,'1':-2},{b:1,'1':-3}]
 for(let mask=0;mask<16;mask++){const path:Path=new Map(atoms.map((lin,i)=>[canon(lin),{lin,holds:!!(mask&(1<<i))}]));expect(incrementalRows(goal,path)).toEqual(leafConstraintsReusing(goal,path))}
})
test('newly read decisions and duplicate hypotheses remain exact',()=>{
 const hyp:C={op:'<=',a:{op:'if',c:atMost(x('a'),n(0)),then:{op:'if',c:atMost(x('b'),n(0)),then:n(1),else:n(2)},else:n(3)},b:n(2)},goal:Goal={name:'nested',hyps:[hyp,hyp]}
 for(const h of [false,true])for(const j of [false,true]){const path:Path=new Map<string,{lin:Lin,holds:boolean}>([['a:1',{lin:{a:1},holds:h}],['b:1',{lin:{b:1},holds:j}]]);expect(incrementalRows(goal,path)).toEqual(leafConstraintsReusing(goal,path))}
})
