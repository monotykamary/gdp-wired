import {test, expect} from 'bun:test'
import {createHash} from 'node:crypto'
import {type C,type E,type Law,type Machine,all,any,not,n,x,same,get} from './machine.ts'
import {carryCandidates, scanPrefixes, type GlobalAudit} from './carry.ts'
import {trueSmall} from './exists.ts'
import {scope,substC,checkLaws} from '../kernel/kernel.ts'
import {clock,counted,fullRate,proveLaws,withDeadline,withWall} from '../kernel/prove.ts'
const sha=(v:unknown)=>createHash('sha256').update(JSON.stringify(v)).digest('hex')
function need(v:unknown,s:string):asserts v{if(!v)throw Error(s)}

const cell=(map:string,key:E):E=>({op:'get',map,key}),pk=(a:E,b:E):E=>({op:'add',a:{op:'mul',k:5,a},b}),iff=(c:C,then:E,other:E):E=>({op:'if',c,then,else:other}),flag=(name:string):C=>({op:'flag',name})
const pos=(map:string,k:E):C=>same(cell(map,k),n(1)),sourcePos=(map:string,k:E):C=>({op:'<=',a:n(1),b:cell(map,k)})
const toy:Machine={name:'framed snapshot control',params:['B'],inputs:['a','op','node'],inputMaps:['incoming'],state:{active:n(0),saved:n(0)},maps:{snapshot:0,relation:0},pre:{op:'<=',a:n(1),b:x('B')},assume:all({op:'<',a:x('a'),b:x('B')},{op:'<',a:x('op'),b:n(3)}),step:{flags:{ready:{op:'all',key:'member',c:any(not(sourcePos('incoming',x('member'))),pos('relation',pk(x('a'),x('member'))))},enter:all(same(x('op'),n(0)),flag('ready')),leave:same(x('op'),n(1)),insert:same(x('op'),n(2))},state:{active:iff(flag('enter'),n(1),iff(flag('leave'),n(0),x('active'))),saved:iff(flag('enter'),x('a'),iff(flag('leave'),n(0),x('saved')))},maps:{snapshot:{each:'slot',value:iff(flag('enter'),iff(sourcePos('incoming',x('slot')),n(1),n(0)),iff(flag('leave'),n(0),cell('snapshot',x('slot'))))},relation:{key:pk(x('a'),x('node')),value:iff(flag('insert'),n(1),cell('relation',pk(x('a'),x('node'))))}}}}

test('range and frame proposals preserve source guards, bounds and renaming', () => {
const globals=(ls:Law[])=>ls.filter(l=>l.name.startsWith('carry:global-'))
const generated=(m:Machine)=>{scope(m);const audit:GlobalAudit={rows:[],work:0,exhausted:false},raw=carryCandidates(m,[],audit);need(raw.length<=128&&audit.work<=8192,'proposal/work cap');return {raw,global:globals(raw),audit}}
const hasRange=(ls:Law[])=>ls.some(l=>l.name.startsWith('carry:global-range:')),hasFrame=(ls:Law[])=>ls.some(l=>l.name.startsWith('carry:global-frame:'))
const controls:unknown[]=[]
const check=(name:string,change:(m:Machine)=>void,test:(ls:Law[])=>boolean)=>{const m=structuredClone(toy);change(m);const g=generated(m);need(test(g.global),name);controls.push({name,passed:true,global:g.global,audit:g.audit})}
const positive=generated(toy),old=positive.raw.filter(l => !l.name.startsWith('carry:global-'))
need(positive.raw.slice(0,old.length).every((l,i)=>sha(l)===sha(old[i])),'existing proposal prefix changed')
need(hasRange(positive.global)&&hasFrame(positive.global),'positive range/frame proposals missing')
check('range bad initializer',m=>{m.state.saved=x('B')},ls=>!hasRange(ls))
check('range unknown symbolic bound at init',m=>{delete m.pre},ls=>!hasRange(ls))
check('range conditional-only input bound',m=>{m.assume=any(same(x('op'),n(0)),{op:'<',a:x('a'),b:x('B')})},ls=>!hasRange(ls))
check('range missing input bound',m=>{m.assume={op:'<',a:x('op'),b:n(3)}},ls=>!hasRange(ls))
check('range unsafe nested reset',m=>{m.step.state!.saved=iff(flag('enter'),x('a'),iff(flag('leave'),x('B'),x('saved')))},ls=>!hasRange(ls))
check('range additional unbounded input leaf',m=>{m.inputs.push('other');m.step.state!.saved=iff(flag('enter'),x('a'),iff(flag('leave'),x('other'),x('saved')))},ls=>!hasRange(ls))
check('range zero bound never vacuously proves init',m=>{m.params=[];m.pre=same(n(0),n(0));m.assume=all({op:'<',a:x('a'),b:n(0)},{op:'<',a:x('op'),b:n(3)})},ls=>!hasRange(ls))
check('frame nonempty domain init',m=>{m.maps!.snapshot=1},ls=>!hasFrame(ls))
check('frame reset keeps old domain',m=>{m.step.maps!.snapshot={each:'slot',value:iff(flag('enter'),iff(sourcePos('incoming',x('slot')),n(1),n(0)),cell('snapshot',x('slot')))}},ls=>!hasFrame(ls))
check('frame scalar changes while domain retained',m=>{m.step.state!.saved=iff(flag('enter'),x('a'),iff(flag('insert'),n(1),x('saved')))},ls=>!hasFrame(ls))
check('frame codomain can clear positives',m=>{m.step.maps!.relation={key:pk(x('a'),x('node')),value:iff(flag('insert'),n(0),cell('relation',pk(x('a'),x('node'))))}},ls=>!hasFrame(ls))
check('frame absent source implication',m=>{m.step.flags!.enter=same(x('op'),n(0))},ls=>!hasFrame(ls))
check('frame negative consequent is not lifted',m=>{m.step.flags!.ready={op:'all',key:'member',c:any(not(sourcePos('incoming',x('member'))),same(cell('relation',pk(x('a'),x('member'))),n(0)))}},ls=>!hasFrame(ls))
check('frame mismatched exact domain predicate',m=>{m.step.flags!.ready={op:'all',key:'member',c:any(not(pos('incoming',x('member'))),pos('relation',pk(x('a'),x('member'))))}},ls=>!hasFrame(ls))
const rename=<T>(t:T,names:Record<string,string>):T=>{const go=(v:unknown,registry=false):unknown=>typeof v==='string'?(names[v]??v):Array.isArray(v)?v.map(x=>go(x)):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,a])=>[registry?(names[k]??k):k,go(a,['state','maps','flags','counts','fns'].includes(k))])):v;return go(t) as T}
const names:Record<string,string>={B:'Limit17',a:'Req19',op:'Cmd23',node:'Node29',incoming:'Input31',active:'Mode37',saved:'Stored41',snapshot:'Saved43',relation:'Rel47',ready:'Check53',enter:'Begin59',leave:'End61',insert:'Put67',slot:'Cell71',member:'Key73'}
const inv=Object.fromEntries(Object.entries(names).map(([a,b])=>[b,a])),renamed=rename(toy,names),rg=generated(renamed)
const alpha=(l:Law)=>{const ns=[l.forall,...(l.keys??[])].filter((s):s is string=>!!s);return sha(substC(l.holds,{vars:Object.fromEntries(ns.map((q,i)=>[q,x('$'+i)])),maps:{},flags:{}}))}
need(sha(positive.global.map(alpha).sort())===sha(rg.global.map(l=>alpha(rename(l,inv))).sort()),'alpha rename covariance')


}, 5000)

const toyScan = (): Machine => ({name:'generic scanning snapshot',params:['size'],inputs:[],state:{active:n(0),cursor:n(0)},maps:{members:0,relation:0},step:{flags:{row:{op:'all',key:'other',c:same(get('relation',{op:'add',a:{op:'mul',k:37,a:x('cursor')},b:x('other')}),n(0))},fails:all(same(x('active'),n(1)),same(get('members',x('cursor')),n(1)),not({op:'flag',name:'row'}))},state:{active:x('active'),cursor:{op:'if',c:all(same(x('active'),n(1)),not({op:'flag',name:'fails'})),then:{op:'add',a:x('cursor'),b:n(1)},else:{op:'if',c:same(x('active'),n(0)),then:n(0),else:x('cursor')}}}}})
test('scan candidates are generic, bounded, and reject changed counters and row guards', () => {
  const m=toyScan(), ls=scanPrefixes(m)
  expect(ls).toHaveLength(2)
  const renamed=JSON.parse(JSON.stringify(m).replaceAll('cursor','position').replaceAll('active','enabled').replaceAll('row','predicate').replaceAll('members','participants').replaceAll('relation','links')) as Machine
  // Registry keys are renamed along with uses; no protocol spelling is consulted.
  expect(scanPrefixes(renamed)).toHaveLength(2)
  const bad=toyScan(); bad.step.state!.cursor=n(0); expect(scanPrefixes(bad)).toEqual([])
  const badRow=toyScan(); badRow.step.flags!.fails=all(same(x('active'),n(1)),same(get('members',x('cursor')),n(1)),{op:'flag',name:'row'}); expect(scanPrefixes(badRow)).toEqual([])
  expect(scanPrefixes(m,[ls[0]!])).toEqual([])
  expect(scanPrefixes(m,[ls[1]!])).toEqual([])
  const unrelated:Machine={name:'unrelated',params:[],inputs:[],state:{i:n(0)},step:{state:{i:{op:'add',a:x('i'),b:n(1)}}}};expect(scanPrefixes(unrelated)).toEqual([])
})

for (const renamed of [false,true]) test(`ordinary range/frame filtering and native closure ${renamed?'renamed':'original'}`,()=>{
 const m=renamed?JSON.parse(JSON.stringify(toy).replaceAll('saved','archive').replaceAll('snapshot','storedRows').replaceAll('relation','links')) as Machine:structuredClone(toy)
 const proposals=carryCandidates(m).filter(l=>l.name.startsWith('carry:global-'))
 const accepted=proposals.filter(l=>{scope(m,[l]);return trueSmall(m,[l])})
 expect(accepted.length).toBe(proposals.length)
 const start=performance.now(),result=counted(fullRate,()=>withWall(start+1500,()=>withDeadline(clock()+1500,()=>proveLaws(m,accepted))),true)
 expect(result.proven && result.checked && !!result.proof && checkLaws(m,accepted,result.proof)).toBe(true)
},5000)

const pgKey=(base:number,a:E,b:E):E=>({op:'add',a:{op:'mul',k:base,a},b})
const pgRetain=(map:string,key:E,guard:C,normalized=false):E=>iff(normalized?any(guard,pos(map,key)):any(all(guard,{op:'<=',a:n(0),b:n(0)}),all(not(guard),pos(map,key))),n(1),n(0))
function pointGuardToy(base=7):Machine{
 const j=pgKey(base,x('a'),x('b')),k=pgKey(base*base,x('member'),j)
 return {name:'persistent point guard',params:['size'],inputs:['member','a','b','op'],state:{},maps:{marks:0,permits:0},assume:all({op:'<',a:x('member'),b:x('size')},{op:'<',a:x('a'),b:n(base)},{op:'<',a:x('b'),b:n(base)}),step:{flags:{put:all(same(x('op'),n(0)),pos('permits',j)),grant:same(x('op'),n(1))},maps:{marks:{key:k,value:pgRetain('marks',k,flag('put'))},permits:{key:j,value:pgRetain('permits',j,flag('grant'))}}}}
}
const pointGuards=(m:Machine)=>{const audit:GlobalAudit={rows:[],work:0,exhausted:false},ls=carryCandidates(m,[],audit).filter(l=>l.name.startsWith('carry:point-guard:'));return {ls,audit}}
const pgAlpha=(l:Law)=>{const ns=[l.forall,...(l.keys??[])].filter((s):s is string=>!!s);return substC(l.holds,{vars:Object.fromEntries(ns.map((s,i)=>[s,x('binder'+i)])),maps:{},flags:{}})}

test('point-guard derives exact source coefficients, domains and capture-free tuple',()=>{
 for(const base of [7,11]){
  const m=pointGuardToy(base),{ls,audit}=pointGuards(m);expect(ls).toHaveLength(1);expect(audit.exhausted).toBe(false);expect(audit.work).toBeLessThanOrEqual(8192)
  const l=ls[0]!;scope(m,[l]);expect([l.forall,...l.keys??[]]).toHaveLength(3)
  const body=JSON.stringify(l.holds);expect(body).toContain('"k":'+base);expect(body).toContain('"k":'+base*base);expect(body).toContain('"name":"size"');expect(body).not.toContain('"value":64')
  const normalized=pointGuardToy(base);for(const [map,w]of Object.entries(normalized.step.maps!))if(!('each'in w))w.value=pgRetain(map,w.key,flag(map==='marks'?'put':'grant'),true)
  expect(pointGuards(normalized).ls.map(pgAlpha)).toEqual(ls.map(pgAlpha))
  const collision=pointGuardToy(base);collision.state={carryKey:n(0),carryKeyX:n(0),carryKeyXX:n(0)}
  const cl=pointGuards(collision).ls[0]!;expect(pgAlpha(cl)).toEqual(pgAlpha(l));expect([cl.forall,...cl.keys??[]].every(k=>!(k! in collision.state))).toBe(true)
 }
 const m=pointGuardToy(),rename=(s:string)=>s==='marks'?'observed':s==='permits'?'enabledCells':s==='member'?'agentId':s==='a'?'epochId':s==='b'?'payloadId':s==='size'?'population':s
 const go=(v:unknown,registry=false):unknown=>typeof v==='string'?rename(v):Array.isArray(v)?v.map(x=>go(x)):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,a])=>[registry?rename(k):k,go(a,['state','maps','flags','counts','fns'].includes(k))])):v
 const renamed=go(m) as Machine,back=(v:unknown):unknown=>typeof v==='string'?Object.fromEntries(['marks','permits','member','a','b','size'].map(s=>[rename(s),s]))[v]??v:Array.isArray(v)?v.map(back):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,a])=>[k,back(a)])):v
 expect(back(pgAlpha(pointGuards(renamed).ls[0]!))).toEqual(pgAlpha(pointGuards(m).ls[0]!))
})

test('point-guard refuses missing, disjunctive, resettable, projecting and quantified guards',()=>{
 const no=(change:(m:Machine)=>void)=>{const m=pointGuardToy();change(m);expect(pointGuards(m).ls).toEqual([])}
 no(m=>{m.step.flags!.put=same(x('op'),n(0))})
 no(m=>{m.step.flags!.put=any(m.step.flags!.put!,same(x('op'),n(2)))})
 no(m=>{m.step.maps!.permits!.value=n(0)})
 no(m=>{m.maps!.marks=1})
 no(m=>{m.assume=any(m.assume!,same(x('op'),n(2)))})
 no(m=>{m.step.flags!.put={op:'all',key:'hidden',c:pos('permits',x('hidden'))}})
 no(m=>{m.step.flags!.put=flag('put')})
 no(m=>{const w=m.step.maps!.marks!;if('each'in w)throw Error('point');w.key=x('b');w.value=pgRetain('marks',w.key,flag('put'))})
 no(m=>{const w=m.step.maps!.marks!;w.value=iff(flag('put'),n(1),n(0))})
})

test('point-guard shares unchanged proposal and generation caps',()=>{
 const m=pointGuardToy(),source=m.step.maps!.marks!;delete m.step.maps!.marks;delete m.maps!.marks
 for(let i=0;i<160;i++){const name='marks'+i,w=structuredClone(source);if('each'in w)throw Error('point');w.value=pgRetain(name,w.key,flag('put'));m.maps![name]=0;m.step.maps![name]=w}
 const audit:GlobalAudit={rows:[],work:0,exhausted:false},ls=carryCandidates(m,[],audit)
 expect(ls.length).toBeLessThanOrEqual(128);expect(audit.work).toBeLessThanOrEqual(8192);expect(audit.exhausted||ls.length===128).toBe(true)
})
