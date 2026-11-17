import {test,expect} from 'bun:test'
import {mkdtempSync,mkdirSync,writeFileSync,symlinkSync,rmSync,renameSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {configureRoots,sourceGuard} from './workspace.ts'
import {parseRequest,Refusal} from './protocol.ts'
import {createConsultation} from './session.ts'
import {budget,budgetLaws} from '../../research/agent-tools/examples.ts'
import {check,type RuleOut} from '../cli.ts'

const fixture=()=>{const parent=mkdtempSync(join(tmpdir(),'gdp-workspace-')),root=join(parent,'root'),sibling=join(parent,'root-sibling');mkdirSync(root);mkdirSync(sibling);const file=join(root,'counter.py'),outside=join(sibling,'counter.py');writeFileSync(file,'class Counter:\n    def __init__(self):\n        self.count = 0\n');writeFileSync(outside,'secret = 1\n');return {parent,root,sibling,file,outside}}
const refused=(f:()=>unknown,code:string)=>{try{f();throw Error('expected refusal '+code)}catch(e){expect(e).toBeInstanceOf(Refusal);expect((e as Refusal).code).toBe(code)}}

// Generated table of policy cases; no test shells or arbitrary interpreter commands.
for(const kind of ['unconfigured','traversal','sibling-prefix','symlink-escape','directory','URL','relative','oversize','unsupported-language'] as const)test('workspace policy: '+kind,()=>{
  const f=fixture();try{const roots=configureRoots([f.root]);let file=f.file,code='outside-workspace',authority=roots
    switch(kind){
      case 'unconfigured':authority=[];code='workspace-unconfigured';break
      case 'traversal':file=f.root+'/../root-sibling/counter.py';code='invalid-file';break
      case 'sibling-prefix':file=f.outside;break
      case 'symlink-escape':file=join(f.root,'escape.py');symlinkSync(f.outside,file);break
      case 'directory':file=join(f.root,'folder');mkdirSync(file);code='not-regular-file';break
      case 'URL':file='file://'+f.file;code='invalid-file';break
      case 'relative':file='counter.py';code='invalid-file';break
      case 'oversize':writeFileSync(f.file,'x'.repeat(131073));code='source-budget-exceeded';break
      case 'unsupported-language':file=join(f.root,'counter.rb');writeFileSync(file,'class C; end');code='unsupported-source-language';break
    }
    refused(()=>sourceGuard(authority,file),code)
  }finally{rmSync(f.parent,{recursive:true,force:true})}
})

test('protocol control characters are refused without rejecting non-ASCII or emoji',()=>{
  const named=(name:string)=>({subject:budget(),laws:budgetLaws.map(l=>({...l,name}))})
  expect(parseRequest('prove',named('café 承認 😀')).laws?.[0]?.name).toBe('café 承認 😀')
  for(const n of [0,1,9,10,13,31])expect(()=>parseRequest('prove',named('law'+String.fromCharCode(n)))).toThrow(Refusal)
  expect(parseRequest('check',{file:'/tmp/承認😀.py'}).file).toBe('/tmp/承認😀.py')
  for(const n of [0,9,10,31])expect(()=>parseRequest('check',{file:'/tmp/a'+String.fromCharCode(n)+'.py'})).toThrow(Refusal)
})

test('workspace identity, revision and symlink/root replacements fail closed',()=>{
  const f=fixture();try{
    const roots=configureRoots([f.root]),source=sourceGuard(roots,f.file),first=source.receipt()
    expect(first.revision).toMatch(/^[a-f0-9]{64}$/)
    expect(source.receipt().revision).toBe(first.revision)
    writeFileSync(f.file,'changed = True\n');refused(()=>source.receipt(),'source-changed')
    const link=join(f.root,'in-root.py');symlinkSync(f.file,link);const second=sourceGuard(roots,link)
    rmSync(link);symlinkSync(f.outside,link);refused(()=>second.receipt(),'source-changed')
    renameSync(f.root,f.root+'-old');mkdirSync(f.root);writeFileSync(f.file,'count = 0\n')
    refused(()=>sourceGuard(roots,f.file),'workspace-changed')
  }finally{rmSync(f.parent,{recursive:true,force:true})}
})

for(const key of ['root','roots','workspaceRoots','python','module','source','options','mode','ms'])test('check caller cannot poison '+key,()=>refused(()=>parseRequest('check',{file:'/tmp/counter.py',[key]:key==='workspaceRoots'?['/']:'/'}),'unsupported-field'))

test('source integration: default disabled; edited Python/TS preserve real engine unknown/proof distinction',async()=>{
  const f=fixture(),disabled=createConsultation(),enabled=createConsultation({workspaceRoots:[f.root]})
  try{
    const denied=await disabled.call('check',{file:f.file});expect(denied.ok).toBe(false);expect((denied.refusal as {code:string}).code).toBe('workspace-unconfigured')
    const revisions=new Map<string,string>()
    for(const ext of ['py','ts'])for(const version of ['good','good-edit','bad']){
      const broken=version==='bad',cap=version==='good-edit'?8:10
      const file=join(f.root,'counter.'+ext),guard=broken?'this.count < 10':`this.count + amount <= ${cap}`
      const body=ext==='py'?`# gdp: law bounded count: count <= 10\nclass Counter:\n    def __init__(self):\n        self.count = 0\n    def add(self, amount: int) -> None:\n        if ${broken?'self.count < 10':`self.count + amount <= ${cap}`}:\n            self.count += amount\n`:`// gdp: law bounded count: count <= 10\nexport class Counter {\n count = 0;\n add(amount: number) { if (${guard}) this.count += amount; }\n}\n`
      writeFileSync(file,body)
      const result=await enabled.call('check',{file,budget:{work:5000000,apiCalls:64,candidates:1}})
      expect(result.tool).toBe('check')
      expect(result.ok,JSON.stringify(result)).toBe(true)
      if(result.ok){
        expect(['proven','broken','unknown']).toContain(result.label as string)
        const rules=(result.result as {rules:RuleOut[]}).rules
        expect(rules.length).toBeGreaterThan(0)
        expect(rules.every(r=>r.ok),JSON.stringify(rules)).toBe(true)
        const stated=rules.flatMap(r=>r.laws)
        expect(stated.length).toBeGreaterThan(0)
        const bounded=stated.find(l=>l.name==='bounded count')
        expect(bounded).toBeDefined()
        // This release baseline has native law journals for both admitted languages.
        expect(bounded!.translation).toBe('sampled')
        expect(bounded!.verdict).toBe(broken?'broken':'proven')
        expect(result.label).toBe(broken?'broken':'proven')
        if(broken)expect(bounded!.run?.length).toBeGreaterThan(0)
        else expect(bounded!.translationChecks).toBeGreaterThan(0)
        for(const law of rules.flatMap(r=>r.laws)){
          if(law.translation==='unchecked')expect(law.verdict).not.toBe('proven')
          if(law.verdict==='broken')expect(law.run).toBeDefined()
          if(law.verdict==='unknown')expect(law.why).toBeDefined()
        }
        const revision=(result.subject as {revision:string}).revision
        expect(revision).toMatch(/^[a-f0-9]{64}$/)
        if(revisions.has(ext))expect(revision).not.toBe(revisions.get(ext))
        revisions.set(ext,revision)
        expect((result.budget as {coverage:unknown}).coverage).toBeDefined()
        // Protect the ordinary async CLI driver on exactly the same edited native source.
        const ordinary=await check([file],{ms:2000,propose:false})
        expect(ordinary.rules.map(r=>r.ok)).toEqual(rules.map(r=>r.ok))
        expect(ordinary.rules.flatMap(r=>r.laws).map(l=>({name:l.name,verdict:l.verdict,translation:l.translation}))).toEqual(rules.flatMap(r=>r.laws).map(l=>({name:l.name,verdict:l.verdict,translation:l.translation})))
      }else expect(result.refusal).toBeDefined() // Never accept a refusal as proof.
    }
    for(const budget of [{apiCalls:0,work:5000000},{apiCalls:64,work:0}]){
      const denied=await enabled.call('check',{file:f.file,budget});expect(denied.ok).toBe(false)
      expect((denied.refusal as {code:string}).code).toBe(budget.apiCalls===0?'api-budget-exceeded':'work-budget-exceeded')
    }
  }finally{await enabled.close();await disabled.close();rmSync(f.parent,{recursive:true,force:true})}
},180000)
