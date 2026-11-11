import {strict as assert} from 'node:assert'
import {readFileSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {execFileSync} from 'node:child_process'
const expected=['core/counts.ts','core/field-laws.ts','core/finite-houdini.ts','core/strategy-premises.test.ts','core/strategy-premises.ts','kernel/kernel.ts','research/protocols/ic3syn/strategy-rejections.ts','scripts/test-shards.ts']
export function resolveStrategyConflicts(root:string){
 const git=(...args:string[])=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trimEnd()
 const actual=git('diff','--name-only','--diff-filter=U').split('\n').filter(Boolean)
 assert.deepEqual(actual,expected,'unexpected conflict requires review')
 const records=[]
 for(const path of actual){
  const before=readFileSync(join(root,path),'utf8');let index=0
  let after=before.replace(/<<<<<<< ours\n([\s\S]*?)=======\n([\s\S]*?)>>>>>>> theirs\n/g,(_all,ours:string,theirs:string)=>{
   const i=index++
   if(path==='research/protocols/ic3syn/strategy-rejections.ts')return theirs
   if(path==='core/counts.ts'){
    if(i===0)return ours+theirs
    if(i===1||i===3)return theirs
    if(i===2){assert(theirs.includes('prepareCountStrategyMachine'));return theirs.replace('until, structured)','until, structured, allowFocused)')}
    if(i===4)return ours+theirs.split('\n').filter(line=>!line.includes('const decisions =')).join('\n')
   }
   if(path==='core/field-laws.ts'||path==='core/finite-houdini.ts'||path==='core/strategy-premises.ts'||path==='core/strategy-premises.test.ts'||path==='scripts/test-shards.ts')return ours
   if(path==='kernel/kernel.ts'){
    if(i===0)return theirs+'      kernelMeter.checkSteps += 1\n'
    if(i===1)return theirs+'  kernelMeter.checkSteps += 1\n'
    if(i===2)return theirs.replace('  if (!(countedOkW','  kernelMeter.checkSteps += 1\n  if (!(countedOkW').replace("checkGoalLemmas({name: 'counted', hyps: [...hyps, ...hs]},", "checkGoalLemmas(observeAst({name: 'counted', hyps: [...hyps, ...hs]}),")
   }
   throw Error('unreviewed hunk '+path+':'+i)
  })
  const counts:Record<string,number>={'core/counts.ts':5,'core/field-laws.ts':1,'core/finite-houdini.ts':2,'core/strategy-premises.test.ts':1,'core/strategy-premises.ts':2,'kernel/kernel.ts':3,'research/protocols/ic3syn/strategy-rejections.ts':1,'scripts/test-shards.ts':1}
  assert.equal(index,counts[path]);assert(!after.includes('<<<<<<<'))
  if(path==='core/field-laws.ts'){
   const marker='// A guarded form and the stronger candidate it weakens;'
   const first=after.indexOf(marker),second=after.indexOf(marker,first+marker.length),end=after.indexOf('export function fieldLaws(',second)
   assert(first>=0&&second>first&&end>second)
   assert.equal(after.slice(first,second).trim(),after.slice(second,end).trim(),'only remove identical duplicate declarations')
   after=after.slice(0,second)+after.slice(end)
  }
  if(path==='core/strategy-premises.test.ts')after+=`\n// Lane B's two source tests, retained alongside the stricter mini-pin tests.\ntest('lane B: aliases and scalars stay excluded',()=>{\n const m:Machine={name:'selector',params:[],inputs:[],state:{},step:{}}\n const good:Law={name:'good',holds:same(n(0),n(0))},bad:Law={name:'bad',holds:same(n(0),n(1))}\n const selector=strategyPremiseSelector(m,[good,bad,{...bad,name:'alias'}],[bad])\n expect(selector.find(l=>l.name==='bad')).toBeUndefined();expect(selector.find(l=>l.name==='alias')).toBeUndefined()\n expect(()=>selector.run({bad:[]},()=>1)).toThrow('rejected or unknown');expect(selector.run({},laws=>laws)).toEqual([good])\n})\ntest('lane B: mutation after selection is refused',()=>{\n const m:Machine={name:'selector',params:[],inputs:[],state:{},step:{}}\n const law:Law={name:'good',holds:same(n(0),n(0))},selector=strategyPremiseSelector(m,[law],[])\n law.name='changed';expect(()=>selector.find(()=>true)).toThrow(/changed/)\n})\n`
  if(path==='scripts/test-shards.ts'){
   const theirs=git('show',':3:'+path),pattern=/tests\('([^']+)',\s*(?:'([^']*)'|`([^`]*)`)\)/g
   const groups=new Map<string,string[]>()
   for(const match of theirs.matchAll(pattern))groups.set(match[1]!,[...(groups.get(match[1]!)??[]),...(match[2]??match[3]??'').split(/\s+/).filter(Boolean)])
   const existing=new Map<string,Set<string>>()
   for(const match of after.matchAll(pattern)){const set=existing.get(match[1]!)??new Set<string>();for(const name of (match[2]??match[3]??'').split(/\s+/))set.add(name);existing.set(match[1]!,set)}
   const used=new Set<string>()
   after=after.replace(pattern,(all,path:string)=>{if(used.has(path))return all;used.add(path);const additions=(groups.get(path)??[]).filter(name=>!existing.get(path)?.has(name));return additions.length?all.slice(0,-2)+' '+[...new Set(additions)].join(' ')+all.slice(-2):all})
   const added=[...groups].filter(([path])=>!existing.has(path)).map(([path,names])=>"  ...tests('"+path+"', '"+[...new Set(names)].join(' ')+"'),\n").join('')
   const anchor="  ...tests('research/query', 'goal-pack.test.ts'),"
   assert(after.includes(anchor));after=after.replace(anchor,added+anchor)
  }
  writeFileSync(join(root,path),after);git('add','--',path)
  records.push({path,hunks:index,policy:'retain mini-pin meters and work-clock controls; add strategy semantics and union test rosters'})
 }
 return records
}
