import {expect,test} from 'bun:test'
import {type C,type E,n,x,get} from './machine.ts'
import {type CountCert,type CountDecl,type Goal,type Path,type Tree,canon,checkMC,mcGoal,framePath,leafConstraints} from '../kernel/kernel.ts'
import {countsForReads} from './count-facts.ts'
import {replayCountCertificate,transportCountCertificate,countedCertificateHyps} from './count-cert-transport.ts'
import {type Lin,type Step} from './solver.ts'
import {countReplayDiagnostic} from './count-replay-diagnostic.ts'
const lt=(a:E,b:E):C=>({op:'<',a,b})
function sum(goal:Goal,path:Path,wanted:Lin[]):Tree{
 const rows=leafConstraints(goal,path),steps:Step[]=wanted.map(lin=>{const i=rows.findIndex(row=>canon(row.lin)===canon(lin));if(i<0)throw Error('fixture row missing '+canon(lin));return {kind:'input',index:i}})
 let at=0;for(let i=1;i<wanted.length;i++){steps.push({kind:'combine',a:at,b:i,ma:1,mb:1});at=steps.length-1}return {leaf:steps}
}
// Raw map-cell hypotheses are not the fresh count variables. Include both
// native read-equality links explicitly rather than inventing a substituted row.
function countSum(goal:Goal,path:Path,cert:CountCert,rawCount:number,last:string,cuts:Lin[]):Tree{
 const rows=leafConstraints(goal,path)
 const fact=(i:number,name?:string,coefficient?:number):Lin=>{
  const row=rows.find(row=>row.src&&'fact'in row.src&&row.src.fact===i&&(name===undefined||row.lin[name]===coefficient))
  if(!row)throw Error('missing native source fact '+i);return row.lin
 }
 const firstIndex=cert.reads.findIndex(r=>r[0]==='ra'),lastIndex=cert.reads.findIndex(r=>r[0]===last)
 return sum(goal,path,[fact(0),fact(rawCount+firstIndex,'ra',1),fact(rawCount+lastIndex,last,-1),...cuts])
}
function impossible():Tree{
 const goal:Goal={name:'aux',hyps:[lt(x('kk'),n(2)),lt(n(0),n(0))]},rows=leafConstraints(goal,new Map())
 const index=rows.findIndex(row=>(row.lin['1']??0)>0&&Object.entries(row.lin).every(([key,value])=>key==='1'||value===0))
 if(index<0)throw Error('auxiliary constant contradiction missing');return {leaf:[{kind:'input',index}]}
}
function fixture(kinds:readonly ('frames'|'monos'|'lins')[]){
 const mixed=kinds.length>1
 const decls:CountDecl[]=(mixed?['A','B','C','D']:['A','B']).map(map=>({map,j:'row',key:'kk',below:n(2),body:get('Cells',x('kk'))}))
 const hyps:C[]=[lt(get('A',n(0)),get(mixed?'D':'B',n(0)))],cert:CountCert={reads:decls.map(d=>['r'+d.map.toLowerCase(),d.map,n(0)]),insts:[],tree:{leaf:[]}}
 if(kinds.includes('frames'))cert.frames=[{when:[],post:'rb',pre:'ra'}]
 if(kinds.includes('monos'))cert.monos=[{when:[],post:mixed?'rc':'rb',pre:mixed?'rb':'ra',tree:impossible()}]
 if(kinds.includes('lins'))cert.lins=[{when:[],pos:[[1,mixed?'rd':'rb']],neg:[[1,mixed?'rc':'ra']],tree:impossible()}]
 if(mixed){
  const hyp:C={op:'<=',a:x('h'),b:n(0)},cut={h:1},path:Path=new Map([[canon(cut),{lin:cut,holds:false}]])
  hyps.push(hyp)
  cert.lemmas=[{when:[],cut,slice:[1],tree:sum({name:'independent',hyps:[hyp]},path,[cut,{h:-1,'1':1}])}]
 }
 const goal=mcGoal(hyps,decls,cert)!,counts=countsForReads(decls,cert.reads)!
 cert.tree=countSum(goal,framePath(cert.frames??[],cert.lemmas??[],new Map(),cert.monos??[],cert.lins??[]),cert,hyps.length,mixed?'rd':'rb',mixed?[{rb:1,ra:-1},{rc:1,rb:-1},{rd:1,rc:-1}]:[{rb:1,ra:-1}])
 return {decls,hyps,cert,goal,counts,native:{from:{counts},to:{counts}}}
}
for(const kinds of [['frames'],['monos'],['lins'],['frames','monos','lins']] as const)test('native-valid '+kinds.join('+')+' certificate transports identically and remains native-valid',()=>{
 const f=fixture(kinds),before=JSON.stringify(f.cert)
 expect(checkMC(f.hyps,f.decls,f.cert)).toBe(true)
 expect(checkMC(f.hyps,f.decls,{...f.cert,frames:[],monos:[],lins:[]})).toBe(false)
 const moved=replayCountCertificate(f.goal,f.goal,f.cert,Infinity,{native:f.native})
 expect(moved).toBeDefined();expect(moved!.tree).toEqual(f.cert.tree)
 expect(moved!.frames).toBe(f.cert.frames);expect(moved!.monos).toBe(f.cert.monos);expect(moved!.lins).toBe(f.cert.lins)
 expect(checkMC(f.hyps,f.decls,moved!)).toBe(true);expect(JSON.stringify(f.cert)).toBe(before)
 expect(countedCertificateHyps(f.goal,f.cert)).toBeDefined()
})
for(const kinds of [['frames'],['monos'],['lins'],['frames','monos','lins']] as const)test('public transport derives actual declarations for '+kinds.join('+'),()=>{
 const f=fixture(kinds),targetHyps:C[]=[{op:'<=',a:x('unused'),b:n(0)},...f.hyps],target=mcGoal(targetHyps,f.decls,f.cert)!
 expect(checkMC(f.hyps,f.decls,f.cert)).toBe(true)
 const moved=transportCountCertificate(f.goal,target,f.cert,Infinity,{declarations:{from:f.decls,to:f.decls}})
 expect(moved).toBeDefined();expect(checkMC(targetHyps,f.decls,moved!)).toBe(true)
 // The inserted fact reindexes a referenced base row, even with distinct mixed
 // lin/mono/frame/lemma prefix rows. This is not an identity fast path.
 expect(moved!.tree).not.toEqual(f.cert.tree)
 expect(moved!.reads).toBe(f.cert.reads);expect(moved!.insts).toBe(f.cert.insts)
 expect(moved!.frames).toBe(f.cert.frames);expect(moved!.monos).toBe(f.cert.monos);expect(moved!.lins).toBe(f.cert.lins)
 expect(transportCountCertificate(f.goal,target,f.cert,Infinity)).toBeUndefined()
 const wrong=f.decls.map(d=>d.map==='B'?{...d,below:n(3)}:d)
 expect(transportCountCertificate(f.goal,target,f.cert,Infinity,{declarations:{from:f.decls,to:wrong}})).toBeUndefined()
})
test('cut-free native identity control remains unchanged',()=>{
 const hyps:C[]=[lt(n(0),n(0))],cert:CountCert={reads:[],insts:[],tree:{leaf:[{kind:'input',index:0}]}},goal=mcGoal(hyps,[],cert)!
 expect(checkMC(hyps,[],cert)).toBe(true)
 const moved=replayCountCertificate(goal,goal,cert,Infinity)!
 expect(moved.tree).toEqual(cert.tree);expect(checkMC(hyps,[],moved)).toBe(true)
})
test('full-cut contexts reject missing or changed native counts despite a cached tree/path',()=>{
 const f=fixture(['frames','monos','lins'])
 expect(checkMC(f.hyps,f.decls,f.cert)).toBe(true)
 expect(replayCountCertificate(f.goal,f.goal,f.cert,Infinity)).toBeUndefined()
 expect(replayCountCertificate(f.goal,f.goal,f.cert,Infinity,{native:f.native})).toBeDefined()
 const wrong=f.counts.map(c=>c.v==='rb'?{...c,below:n(3)}:c)
 expect(replayCountCertificate(f.goal,f.goal,f.cert,Infinity,{native:{from:{counts:f.counts},to:{counts:wrong}}})).toBeUndefined()
})
test('main cuts cannot prove an independent lemma',()=>{
 const f=fixture(['frames']),cut={rb:1,ra:-1},neg={ra:1,rb:-1,'1':1},path:Path=new Map([[canon(neg),{lin:neg,holds:true}]]),empty:Goal={name:'independent',hyps:[]}
 const tree=sum(empty,framePath(f.cert.frames!,[],path),[cut,neg])
 const bad={...f.cert,lemmas:[{when:[],cut,slice:[],tree}]}
 expect(checkMC(f.hyps,f.decls,bad)).toBe(false)
 expect(replayCountCertificate(f.goal,f.goal,bad,Infinity,{native:f.native})).toBeUndefined()
})
test('conditional activation uses only the original branch path',()=>{
 const m={op:1},nm={op:-1},decls:CountDecl[]=[{map:'A',j:'row',key:'kk',below:n(2),body:{op:'if',c:{op:'=',a:x('op'),b:n(0)},then:n(0),else:n(1)}},{map:'B',j:'row',key:'kk',below:n(2),body:n(0)}]
 const hyps:C[]=[lt(get('A',n(0)),get('B',n(0))),{op:'=',a:x('op'),b:n(0)}],cert:CountCert={reads:[['ra','A',n(0)],['rb','B',n(0)]],insts:[],frames:[{post:'rb',pre:'ra',when:[m,nm]}],tree:{leaf:[]}},goal=mcGoal(hyps,decls,cert)!,counts=countsForReads(decls,cert.reads)!
 const path=(pairs:[Lin,boolean][]):Path=>new Map(pairs.map(([lin,holds])=>[canon(lin),{lin,holds}]))
 cert.tree={split:m,no:sum(goal,path([[m,false]]),[m,{op:-1,'1':1}]),yes:{split:nm,no:sum(goal,path([[m,true],[nm,false]]),[nm,{op:1,'1':1}]),yes:countSum(goal,framePath(cert.frames!,[],path([[m,true],[nm,true]])),cert,hyps.length,'rb',[{rb:1,ra:-1}])}}
 expect(checkMC(hyps,decls,cert)).toBe(true)
 const moved=replayCountCertificate(goal,goal,cert,Infinity,{native:{from:{counts},to:{counts}}})!
 expect(moved).toBeDefined();expect(checkMC(hyps,decls,moved)).toBe(true)
 const bad={...cert,frames:[{...cert.frames![0]!,when:[m]}]}
 expect(checkMC(hyps,decls,bad)).toBe(false)
 expect(replayCountCertificate(goal,goal,bad,Infinity,{native:{from:{counts},to:{counts}}})).toBeUndefined()
})
test('a missing input row exports exact source provenance and stage',()=>{
 const hyps:C[]=[{op:'<=',a:x('a'),b:n(0)},{op:'<=',a:n(1),b:x('a')}],cert:CountCert={reads:[],insts:[],tree:{leaf:[]}},from=mcGoal(hyps,[],cert)!,to:Goal={name:'reduced',hyps:[hyps[0]!]}
 cert.tree=sum(from,new Map(),[{a:1},{a:-1,'1':1}]);expect(checkMC(hyps,[],cert)).toBe(true)
 const events:any[]=[],old=countReplayDiagnostic.on;countReplayDiagnostic.on=e=>events.push(e)
 try{expect(replayCountCertificate(from,to,cert,Infinity,{diagnostic:{member:'member',obligation:'member @step'}})).toBeUndefined()}finally{countReplayDiagnostic.on=old}
 expect(events).toHaveLength(1);const e=events[0]
 expect(e.kind).toBe('certificate-decline');expect(e.context.member).toBe('member');expect(e.detail.stage).toBe('leaf-mapping');expect(e.detail.part).toBe('main')
 expect(e.detail.sourceRow.src).toEqual({fact:1});expect(e.detail.sourceFact).toEqual(hyps[1]);expect(e.detail.sourceRow.lin).toEqual({a:-1,'1':1});expect(e.cutCounts).toEqual({frames:0,lemmas:0,monos:0,lins:0})
})
