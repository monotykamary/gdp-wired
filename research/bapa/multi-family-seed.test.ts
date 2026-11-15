import {expect,test} from 'bun:test'
import {createHash} from 'node:crypto'
import {mkdtempSync,mkdirSync,readFileSync,writeFileSync,rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import type {Law,Machine} from '../../core/machine.ts'
import {proveCandidateSeeds} from '../../core/candidate-seeds.ts'
import {writeGraphCapsule} from './proof-graph.ts'
import {loadCandidateSeedManifest} from './candidate-seed-manifest.ts'
const sha=(x:Uint8Array)=>createHash('sha256').update(x).digest('hex')
test('multiple leaves remain distinct proposals; even a sealed false candidate is not trusted',()=>{
 const root=mkdtempSync(join(tmpdir(),'seed-pool-')),dir=join(root,'capture');mkdirSync(dir)
 try{
  const machine:Machine={name:'pool fixture',params:[],inputs:[],state:{x:{op:'const',value:0},y:{op:'const',value:0}},step:{}}
  const law=(value:number):Law=>({name:'same historical name',holds:{op:'=',a:{op:'var',name:'x'},b:{op:'const',value}}})
  const identity={protocol:'multi-fixture'}
  // Test input is deliberately not proof authority. A forged verdict cannot
  // make its false candidate survive actual native admission below.
  writeGraphCapsule(join(dir,'graph'),{route:'witness',identity,verdict:{proven:true,checked:true},terms:{terms:[]},proof:{kind:'derived',parents:[0,1].map(value=>({kind:'usual',machine,laws:[law(value)],proof:{trees:{}}})),context:{}}})
  writeFileSync(join(dir,'CAPTURE.json'),JSON.stringify({schema:'final29-native-certificate/v1',complete:true,route:'witness',identity,terms:0,graphManifestSha256:sha(readFileSync(join(dir,'graph','manifest.json')))}))
  const path=join(root,'seed.json');writeFileSync(path,JSON.stringify({schema:'candidate-seed-manifest/v1',protocol:'multi-fixture',capture:'capture',captureSha256:sha(readFileSync(join(dir,'CAPTURE.json'))),bindings:{maps:{},domains:{}}}))
  const seeds=loadCandidateSeedManifest(path,machine)
  expect(seeds.laws).toHaveLength(2);expect(new Set(seeds.laws.map(l=>l.name)).size).toBe(2)
  expect(seeds.audit.laws.map(a=>a.status==='candidate'?a.sourceFamily:undefined)).toEqual([0,1])
  const goal:Law={name:'public y zero',holds:{op:'=',a:{op:'var',name:'y'},b:{op:'const',value:0}}}
  const out=proveCandidateSeeds(machine,[goal],seeds.laws)
  const good=seeds.laws.find(l=>l.holds.op==='='&&l.holds.b.op==='const'&&l.holds.b.value===0)!
  const bad=seeds.laws.find(l=>l.holds.op==='='&&l.holds.b.op==='const'&&l.holds.b.value===1)!
  expect(out.status).toBe('checked');expect(out.kept.map(l=>l.name)).toContain(good.name)
  expect(out.dropped.map(l=>l.name)).toContain(bad.name)
 }finally{rmSync(root,{recursive:true,force:true})}
})
