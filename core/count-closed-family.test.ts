import {expect,test} from 'bun:test'
import {spawnSync} from 'node:child_process'
import {type Law,type Machine,n,same,x} from './machine.ts'
import {type CountCert,type Instances,checkCountedLaws,countedObligations,mcGoal} from '../kernel/kernel.ts'
import {clock,grow,withDeadline,withWall} from '../kernel/prove.ts'
import {greatestClosedCountFamily,closeGreatestCountFamily} from './count-closed-family.ts'
const bounded=<T>(body:(until:number)=>T)=>withWall(performance.now()+10000,()=>withDeadline(clock()+10000,()=>body(clock()+9000)))
function fixture(){
 const m:Machine={name:'closed bottom layer fixture',params:[],inputs:[],state:{a:n(0),b:n(0),c:n(0)},step:{state:{a:x('a'),b:x('c'),c:x('c')}}}
 const a:Law={name:'bottom',holds:same(x('a'),n(0))},b:Law={name:'dependent',holds:same(x('b'),n(0))},c:Law={name:'missing',holds:same(x('c'),n(0))}
 return {m,a,b,c,family:[a,b,c]}
}
function prove(m:Machine,owner:Law,family:Law[],until:number):{instances:Instances,certs:Record<string,CountCert>}{
 const certs:Record<string,CountCert>={};for(const {goal,decls}of countedObligations(m,family,{},family.indexOf(owner))){const base={reads:[],insts:[]},expanded=mcGoal(goal.hyps,decls,base)!;const result=grow(expanded,new Map(),{nodes:0,until});if(!('tree'in result))throw Error('fixture proof failed');certs[goal.name]={...base,tree:result.tree}}return {instances:{},certs}
}
const graph=(entries:readonly (readonly [string,readonly string[]])[])=>new Map(entries)
test('46.4 negative1: closes the native bottom layer once and leaves target unproven',()=>bounded(until=>{
 const f=fixture(),bottom=prove(f.m,f.a,[f.a],until),dependent=prove(f.m,f.b,f.family,until),rows=[{id:f.a.name,premises:[],payload:bottom},{id:f.b.name,premises:[f.c.name],payload:dependent}];let calls=0,reserves=0
 const result=closeGreatestCountFamily(f.b.name,rows,{legacy:()=>{throw Error('target not closed')},reserve:members=>{reserves++;expect(members[0]).toBe(rows[0]!);return true},submit:members=>{calls++;expect(members[0]!.payload).toBe(bottom);return checkCountedLaws(f.m,[f.a],{instances:{[f.a.name]:bottom.instances},certs:bottom.certs})}})
 expect(result.targetInFamily).toBe(false);expect(result.result).toBe(true);expect(result.plan.members).toEqual([f.a.name]);expect(result.plan.blockers).toEqual([f.c.name]);expect(result.plan.paths.get(f.b.name)).toEqual([{blocker:f.c.name,path:[f.b.name,f.c.name]}]);expect(calls).toBe(1);expect(reserves).toBe(1)
}))
test('46.4 negative2: understated dependencies do not bypass the native family check',()=>bounded(until=>{
 const f=fixture(),a=prove(f.m,f.a,[f.a,f.b],until),b=prove(f.m,f.b,f.family,until);let calls=0
 const result=closeGreatestCountFamily('unheld-target',[{id:f.a.name,premises:[],payload:a},{id:f.b.name,premises:[],payload:b}],{legacy:()=>{throw Error('outside target')},reserve:()=>true,submit:()=>{calls++;return checkCountedLaws(f.m,[f.a,f.b],{instances:{},certs:{...a.certs,...b.certs}})}})
 expect(result.targetInFamily).toBe(false);expect(result.result).toBe(false);expect(calls).toBe(1)
}))
test('46.4 negative3: a closed mutual cycle stays in the greatest fixed point',()=>{
 const result=greatestClosedCountFamily(['a','b'],graph([['a',['b']],['b',['a']]]));expect(result.members).toEqual(['a','b']);expect(result.blockers).toEqual([])
})
test('46.4 negative4: a cycle with an unheld dependency is removed and blocker paths terminate',()=>{
 const result=greatestClosedCountFamily(['a','b','c'],graph([['a',['b']],['b',['a','c']]]));expect(result.members).toEqual([]);expect(result.missing.get('a')).toEqual(['b']);expect(result.missing.get('b')).toEqual(['a','c']);expect(result.blockers).toEqual(['c']);expect(result.paths.get('a')).toEqual([{blocker:'c',path:['a','b','c']}])
})
test('46.4 negative5: a closed target invokes only the byte-identical legacy payload',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.a,[f.a],until),family=[f.a],bytes=JSON.stringify({family,proof});let calls=0
 const result=closeGreatestCountFamily(f.a.name,[{id:f.a.name,premises:[],payload:proof}],{legacy:()=>{calls++;expect(JSON.stringify({family,proof})).toBe(bytes);return checkCountedLaws(f.m,family,{instances:{},certs:proof.certs})},reserve:()=>{throw Error('legacy reserve must not be replaced')},submit:()=>{throw Error('legacy family must not be rebuilt')}})
 expect(result.targetInFamily).toBe(true);expect(result.result).toBe(true);expect(calls).toBe(1);expect(JSON.stringify({family,proof})).toBe(bytes)
}))
test('empty/unfunded closure starts no check and preserves the held payload',()=>{
 let calls=0;const callbacks={legacy:()=>++calls,reserve:()=>false,submit:()=>++calls}
 expect(closeGreatestCountFamily('t',[],callbacks).route).toBe('empty');const row={id:'a',premises:[],payload:{x:1}};expect(closeGreatestCountFamily('t',[row],callbacks).route).toBe('unfunded');expect(calls).toBe(0);expect(row.payload).toEqual({x:1})
})
test('false INIT and STEP mutations are refused by the real native subset checker',()=>bounded(until=>{
 const f=fixture(),proof=prove(f.m,f.a,[f.a],until)
 for(const m of [{...f.m,state:{...f.m.state,a:n(1)}},{...f.m,step:{state:{...f.m.step.state,a:n(1)}}}]){
  const result=closeGreatestCountFamily('t',[{id:f.a.name,premises:[],payload:proof}],{legacy:()=>true,reserve:()=>true,submit:()=>checkCountedLaws(m,[f.a],{instances:{},certs:proof.certs})});expect(result.result).toBe(false);expect(result.targetInFamily).toBe(false)
 }
}))
test('explicit checked basis and diamond blockers are stable and deduplicated',()=>{
 const held=graph([['a',['b','c']],['b',['d']],['c',['d']],['e',['basis']]])
 const result=greatestClosedCountFamily(['e','a','c','b','d'],held,{basis:new Set(['basis'])});expect(result.members).toEqual(['e']);expect(result.blockers).toEqual(['d']);expect(result.paths.get('a')).toHaveLength(1)
})
test('a thrown native callback is not retried or promoted to success',()=>{
 let calls=0;expect(()=>closeGreatestCountFamily('t',[{id:'a',premises:[],payload:{}}],{legacy:()=>true,reserve:()=>true,submit:()=>{calls++;throw Error('native failed')}})).toThrow('native failed');expect(calls).toBe(1)
})
test('greatest fixed point contains every closed subset of three members',()=>{
 const order=['a','b','c'];for(let edges=0;edges<512;edges++){const held=new Map(order.map((name,i)=>[name,order.filter((_,j)=>(edges>>(3*i+j))&1)])),g=new Set(greatestClosedCountFamily(order,held,{tick:()=>{}}).members);for(let mask=0;mask<8;mask++){const s=new Set(order.filter((_,i)=>(mask>>i)&1));if([...s].every(name=>held.get(name)!.every(p=>s.has(p))))expect([...s].every(name=>g.has(name))).toBe(true)}}
})
test('a zero work lease starts no closure body',()=>{
 const env=Object.fromEntries(Object.entries(process.env).filter(([k])=>!k.startsWith('GDP_'))),child=spawnSync(process.execPath,['--eval',`import {strict as a} from 'node:assert';import {greatestClosedCountFamily} from './core/count-closed-family.ts';import {withBudget,fullWork,BudgetExpired} from './kernel/prove.ts';const before=fullWork();let stopped=false;try{withBudget(0,()=>greatestClosedCountFamily(['a'],new Map([['a',[]]])))}catch(e){a(e instanceof BudgetExpired);stopped=true}a(stopped);a.equal(fullWork(),before)`],{cwd:new URL('../',import.meta.url).pathname,env:{...env,GDP_WORK_FULL:'1'},encoding:'utf8',timeout:10000});if(child.status!==0)throw Error(child.stderr);expect(child.status).toBe(0)
})
