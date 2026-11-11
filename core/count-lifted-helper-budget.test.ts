// Read the actual shipped routing expressions, then call the static helper
// and observe its deadline. A dropped option (d773's load bug) reaches legacy60.
import {expect,spyOn,test} from 'bun:test'
import {readFileSync} from 'node:fs'
import ts from 'typescript'
import {completeWorkProfile} from './work-profile.ts'
import {get,n,same,x,all,any,atMost,less,minus,plus,times,not} from './machine.ts'
import * as prover from '../kernel/prove.ts'
import * as facts from './count-guard-facts.ts'
import {UnwrittenCountPrefix} from './count-unwritten-prefix.ts'
import {proveQuorumCountLeaf} from './count-quorum-leaf.ts'
import {proveCountFrameGoal} from './count-frames.ts'
import {liftedLeafUntil,withLiftedLeaf} from './count-lifted-budget.ts'
const L=7000,stop={}
function expressions(file:string,name:string,construct=false){
 const text=readFileSync(new URL(file,import.meta.url),'utf8'),source=ts.createSourceFile(file,text,ts.ScriptTarget.Latest,true),out:ts.Expression[][]=[]
 const visit=(node:ts.Node)=>{if((construct?ts.isNewExpression(node):ts.isCallExpression(node))&&(node as ts.CallExpression).expression.getText(source)===name)out.push([...(node as ts.CallExpression).arguments??[]]);ts.forEachChild(node,visit)}
 visit(source);return out.map(args=>args.map(arg=>arg.getText(source)))
}
const routedOptions=(file:string,name:string,index:number,construct=false,leaf=L)=>{
 const args=expressions(file,name,construct)[0];expect(args).toBeDefined()
 // The probe supplies only these data bindings. Reject unsupported AST forms
 // instead of evaluating source text as JavaScript.
 const source=ts.createSourceFile('routed-options.ts','('+(args?.[index]??'{}')+')',ts.ScriptTarget.Latest,true),statement=source.statements[0]
 if(!statement||!ts.isExpressionStatement(statement)||!ts.isParenthesizedExpression(statement.expression)||!ts.isObjectLiteralExpression(statement.expression.expression))throw Error('expected routing options object')
 const bindings:Record<string,unknown>={options:{leafUnits:leaf},deferred:true,extraWhen:[]},routed:Record<string,unknown>={}
 for(const property of statement.expression.expression.properties){
  if(!ts.isPropertyAssignment(property)&&!ts.isShorthandPropertyAssignment(property))throw Error('unsupported routing option')
  if(!ts.isIdentifier(property.name)&&!ts.isStringLiteral(property.name))throw Error('unsupported routing option name')
  const value=ts.isPropertyAssignment(property)?property.initializer:property.name
  if(ts.isIdentifier(value)&&Object.hasOwn(bindings,value.text))routed[property.name.text]=bindings[value.text]
  else if(ts.isPropertyAccessExpression(value)&&ts.isIdentifier(value.expression)&&value.expression.text==='options'&&value.name.text==='leafUnits')routed[property.name.text]=leaf
  else throw Error('unsupported routing option value')
 }
 return routed as {leafUnits?:number}
}
function intercepted(run:()=>void,install:(capture:(end:number)=>never)=>{mockRestore:()=>void},legacy:number){
 prover.withBudget(1e9,()=>{let delta:number|undefined;const spy=install(end=>{delta=end-prover.clock();throw stop})
 try{try{run()}catch(error){if(error!==stop)throw error}}finally{spy.mockRestore()}
 expect(delta).toBeDefined();const wanted=completeWorkProfile.enabled?L:legacy
 expect(delta!).toBeLessThanOrEqual(wanted+0.001);expect(delta!).toBeGreaterThan(wanted-20)
 })
}
for(const [name,file]of [['load','./count-lifted-load.ts'],['replacement','./count-lifted-replacement.ts']]as const)test(name+' prefix forwards original leaf allowance under active profile',()=>{
 const options=routedOptions(file,'UnwrittenCountPrefix',6,true)
 const decls=[{map:'C',j:'j',key:'k',below:n(2),body:get('Cells',x('k'))},{map:'C#',j:'j',key:'k',below:n(2),body:get('Cells',x('k'))}],reads:[string,string,ReturnType<typeof x>][]=[['pre','C',x('a')],['post','C#',x('a')]]
 intercepted(()=>new UnwrittenCountPrefix(decls,reads,[],x('written'),n(2),'cdcl',options).prove('post','pre',[x('a')],1,prover.clock()+50000),capture=>spyOn(facts,'guardLinearFact').mockImplementation((_d,_r,_p,end)=>capture(end)),60)
})
test('quorum helper receives the replacement leaf allowance',()=>{
 const options=routedOptions('./count-lifted-replacement.ts','proveQuorumCountLeaf',8)
 const q=x('q'),v=x('v'),dq=x('dq'),dv=x('dv'),overlap=x('overlap'),hq=x('hq'),hv=x('hv'),rq=plus(dq,overlap),rv=plus(dv,overlap)
 const guard=all(atMost(times(2,hq),rq),less(rq,plus(times(2,hq),n(2))),atMost(times(2,hv),rv),less(rv,plus(times(2,hv),n(2)))),pair=any(not(guard),less(overlap,plus(minus(plus(hq,n(1)),dq),minus(plus(hv,n(1)),dv))),atMost(times(2,q),rq),atMost(times(2,v),rv)),goal={name:'quorum deadline',hyps:[guard,pair,less(rq,times(2,q)),less(rv,times(2,v)),atMost(plus(q,v),plus(plus(dq,dv),overlap)),atMost(v,rv),atMost(q,rq)]}
 intercepted(()=>{proveQuorumCountLeaf(goal,goal,new Map(),pair,{first:'q',second:'v'},[hq,hv],prover.clock()+50000,undefined,options)},capture=>spyOn(prover,'withDeadline').mockImplementation((end)=>capture(end)),500)
})
test('frame per-key helper receives the frame emitter leaf allowance',()=>{
 const options=routedOptions('./count-lifted-strategy.ts','proveCountFrameGoal',7)
 const decls=[{map:'C',j:'row',key:'k',below:n(2),body:get('Cells',x('k'))},{map:'C#',j:'row',key:'k',below:n(2),body:{op:'if' as const,c:same(x('action'),n(4)),then:n(0),else:get('Cells',x('k'))}}],request={reads:[['pre','C',n(0)],['post','C#',n(0)]] as [string,string,ReturnType<typeof n>][],insts:[]},goal={name:'frame deadline',hyps:[less(get('C',n(0)),get('C#',n(0))),same(x('action'),n(4))]}
 intercepted(()=>{proveCountFrameGoal(goal,decls,request,{name:'action',value:4,values:[0,1,4]},new Set(['C']),prover.clock()+50000,undefined,options)},capture=>spyOn(prover,'grow').mockImplementation((_g,_p,opts)=>capture(opts!.until!)),100)
})
for(const [name,file]of [['copy','./count-lifted-copy.ts'],['replacement','./count-lifted-replacement.ts'],['increment','./count-lifted-increment.ts'],['load','./count-lifted-load.ts']]as const)test(name+' short/query helper expressions reuse W/120 and their absolute parent',()=>{
 const calls=[...expressions(file,'liftedLeafUntil').map(args=>({args,scoped:false})),...expressions(file,'withLiftedLeaf').map(args=>({args,scoped:true}))];expect(calls.length).toBeGreaterThan(0)
 prover.withBudget(1e9,()=>{for(const {args,scoped} of calls){
  expect(args[1]).toBe('options');const alternatives=args[2]==="c2&&stage==='partition'?500:100"?[500,100]:[Number(args[2])]
  for(const legacy of alternatives){expect(Number.isFinite(legacy)).toBe(true)
  const parentName=args[0];if(parentName!=='until'&&parentName!=='deadline'&&parentName!=='end')throw Error('unsupported leaf parent')
  const evaluate=(leafUntil:typeof liftedLeafUntil,until:number,deadline:number,end:number,options:Parameters<typeof liftedLeafUntil>[1])=>scoped?withLiftedLeaf({until,deadline,end}[parentName],options,legacy,'test:static-routing',value=>value):leafUntil({until,deadline,end}[parentName],options,legacy)
  const now=prover.clock(),parent=now+50000,value=evaluate(liftedLeafUntil,parent,parent,parent,{leafUnits:L})
  expect(value-now).toBeCloseTo(completeWorkProfile.enabled?L:legacy,4)
  expect(evaluate(liftedLeafUntil,now+1,now+1,now+1,{leafUnits:L})).toBe(now+1)
  expect(evaluate(liftedLeafUntil,parent,parent,parent,{} )-now).toBeCloseTo(legacy,4)
 }}})
})
test('direct prefix with no leaf option keeps legacy60 even in FULL1',()=>{
 const decls=[{map:'C',j:'j',key:'k',below:n(2),body:get('Cells',x('k'))},{map:'C#',j:'j',key:'k',below:n(2),body:get('Cells',x('k'))}],reads:[string,string,ReturnType<typeof x>][]=[['pre','C',x('a')],['post','C#',x('a')]]
 prover.withBudget(1e9,()=>{let delta=0;const spy=spyOn(facts,'guardLinearFact').mockImplementation((_d,_r,_p,end)=>{delta=end-prover.clock();throw stop})
 try{try{new UnwrittenCountPrefix(decls,reads,[],x('written'),n(2)).prove('post','pre',[x('a')],1,prover.clock()+50000)}catch(error){if(error!==stop)throw error}}finally{spy.mockRestore()}
 expect(delta).toBeCloseTo(60,4)
 })
})
