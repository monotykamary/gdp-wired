import {expect, test} from 'bun:test'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {proveLaws} from '../../kernel/prove.ts'
import {rule, type StepLaw} from '../../core/dsl.ts'
import {extractPython} from '../../core/extract-py.ts'
import {buildLaw, ScalarListQuantifierError} from '../../core/laws.ts'
import type {C, E, Law} from '../../core/machine.ts'
import {duplicatePolicyNames, nestedUniversalAdmission, orderedListFixtures, surfaceFixtures, type OrderedListFixture, type OrderedValue, type SurfaceFixture} from './surface-lowering-fixtures.ts'

type Model = Readonly<{free:Record<string, number>, maps:Record<string, readonly number[]>}>
type ExistsBinding = Readonly<{vars:readonly string[], pos:boolean}>
const domain = [0, 1, 2] as const

// Deliberately independent of core/machine.ts's evaluator. This is a bounded
// executable oracle for this gate's fixture grammar, not a proof of equivalence.
function evalE(e:E, env:Record<string,number>, model:Model):number {
  switch (e.op) {
    case 'const': return e.value
    case 'var': { const value = env[e.name] ?? model.free[e.name]; if (value === undefined) throw new Error('unbound variable '+e.name); return value }
    case 'add': return evalE(e.a, env, model) + evalE(e.b, env, model)
    case 'sub': return Math.max(0, evalE(e.a, env, model) - evalE(e.b, env, model))
    case 'min': return Math.min(evalE(e.a, env, model), evalE(e.b, env, model))
    case 'max': return Math.max(evalE(e.a, env, model), evalE(e.b, env, model))
    case 'mul': return e.k * evalE(e.a, env, model)
    case 'prod': return evalE(e.a, env, model) * evalE(e.b, env, model)
    case 'if': return evalC(e.c, env, model) ? evalE(e.then, env, model) : evalE(e.else, env, model)
    case 'get': return model.maps[e.map]?.[evalE(e.key, env, model)] ?? 0
    case 'tup': { const a=evalE(e.a, env, model), b=evalE(e.b, env, model), s=a+b; return (s*(s+1))/2+b }
    case 'proj': throw new Error('projection is outside this gate fixture grammar')
  }
}
function quantified(names:readonly string[], env:Record<string,number>, model:Model, body:(next:Record<string,number>)=>boolean):boolean {
  const go=(i:number, at:Record<string,number>):boolean => i===names.length ? body(at) : domain.every(value => go(i+1, {...at,[names[i]!]:value}))
  return go(0,env)
}
function evalC(c:C, env:Record<string,number>, model:Model):boolean {
  switch (c.op) {
    case '<': return evalE(c.a,env,model)<evalE(c.b,env,model)
    case '<=': return evalE(c.a,env,model)<=evalE(c.b,env,model)
    case '=': return evalE(c.a,env,model)===evalE(c.b,env,model)
    case 'and': return c.xs.every(x=>evalC(x,env,model))
    case 'or': return c.xs.some(x=>evalC(x,env,model))
    case 'not': return !evalC(c.x,env,model)
    case 'all': return quantified([c.key,...(c.keys??[])],env,model,next=>evalC(c.c,next,model))
    case 'flag': throw new Error('flags are outside this gate fixture grammar')
  }
}
function surfaceMeaning(fixture:SurfaceFixture, model:Model):boolean {
  const bindings=(fixture.source.ex??[]) as readonly ExistsBinding[]
  if (bindings.some(binding=>!binding.pos)) throw new Error('fixture has a negative existential')
  const names=bindings.flatMap(binding=>binding.vars)
  const choose=(i:number, env:Record<string,number>):boolean => i===names.length ? evalC(fixture.source.c,env,model) : domain.some(value=>choose(i+1,{...env,[names[i]!]:value}))
  return choose(0,{})
}
function loweredMeaning(law:Law, model:Model):boolean {
  const choose=(i:number, env:Record<string,number>):boolean => {
    const some=law.some??[]
    if (i<some.length) return domain.some(value=>choose(i+1,{...env,[some[i]!]:value}))
    const keys=law.forall===undefined ? [] : [law.forall,...(law.keys??[])]
    return quantified(keys,env,model,next=>evalC(law.holds,next,model))
  }
  return choose(0,{})
}
function variablesE(e:E, out:Set<string>):void {
  switch(e.op) {
    case 'var': out.add(e.name); return
    case 'const': return
    case 'get': variablesE(e.key,out); return
    case 'if': variablesC(e.c,out); variablesE(e.then,out); variablesE(e.else,out); return
    case 'mul': variablesE(e.a,out); return
    case 'proj': variablesE(e.a,out); return
    case 'add': case 'sub': case 'min': case 'max': case 'prod': case 'tup': variablesE(e.a,out); variablesE(e.b,out)
  }
}
function variablesC(c:C, out:Set<string>):void {
  switch(c.op) {
    case '<': case '<=': case '=': variablesE(c.a,out); variablesE(c.b,out); return
    case 'and': case 'or': c.xs.forEach(x=>variablesC(x,out)); return
    case 'not': variablesC(c.x,out); return
    case 'all': {
      const nested=new Set<string>()
      variablesC(c.c,nested); nested.delete(c.key); c.keys?.forEach(key=>nested.delete(key))
      nested.forEach(name=>out.add(name)); return
    }
    case 'flag': return
  }
}
function freeVariables(c:C):string[] { const out=new Set<string>(); variablesC(c,out); return [...out].sort() }
function loweredFreeVariables(law:Law):string[] {
  const out=new Set(freeVariables(law.holds))
  for (const name of [...(law.some??[]), ...(law.forall===undefined?[]:[law.forall,...(law.keys??[])])]) out.delete(name)
  return [...out].sort()
}
function models(free:readonly string[]):Model[] {
  const mapRows=domain.flatMap(a=>domain.flatMap(b=>domain.map(c=>[a,b,c] as const)))
  const envs=free.reduce<Record<string,number>[]>((rows,name)=>rows.flatMap(row=>domain.map(value=>({...row,[name]:value}))),[{}])
  return envs.flatMap(freeEnv=>mapRows.map(row=>({free:freeEnv,maps:{A:row}})))
}
function assertAgreement(fixture:SurfaceFixture, candidates:readonly Model[]=models(fixture.free)):void {
  for (const model of candidates) expect(loweredMeaning(fixture.lowered,model), fixture.id+' '+JSON.stringify(model)).toBe(surfaceMeaning(fixture,model))
}
function requireUniquePolicyNames(laws:readonly Law[]):void {
  const names=new Set<string>()
  for (const law of laws) { if (names.has(law.name)) throw new Error('duplicate policy name: '+law.name); names.add(law.name) }
}

test('surface meaning agrees with accepted lowered laws on declared bounded fixtures', () => {
  const fixtures=surfaceFixtures()
  expect(fixtures.map(f=>f.id)).toEqual(['universal','exists-forall','integer-aliases','free-bound-collision','label'])
  for (const fixture of fixtures) {
    expect(fixture.lowered.name).toBe(fixture.label) // labels are metadata, not binders
    expect(loweredFreeVariables(fixture.lowered)).toEqual([...fixture.free])
    expect(fixture.lowered.some?.length??0).toBe((fixture.source.ex??[]).flatMap(binding=>(binding as ExistsBinding).vars).length)
    if (fixture.id==='integer-aliases') {
      const aliases=fixture.lowered.some??[], negative=aliases.find(name=>name.endsWith('$neg'))
      expect(aliases).toHaveLength(2)
      expect(negative).toBeDefined()
      expect(aliases).toContain(negative!.slice(0,-4))
    }
    if (fixture.id==='free-bound-collision') expect(fixture.lowered.forall).not.toBe('key$1')
    assertAgreement(fixture)
  }
})

test('nested one-key universals and duplicate policy labels are refused structurally', () => {
  const nested=nestedUniversalAdmission()
  expect(nested.c.op).toBe('all')
  expect(JSON.stringify(nested.c)).toContain('"op":"all"')
  expect(()=>requireUniquePolicyNames(duplicatePolicyNames())).toThrow('duplicate policy name')
})

test('free-variable collection respects each quantifier lexical scope', () => {
  const atom:C={op:'=',a:{op:'var',name:'x'},b:{op:'const',value:0}}
  const scoped:C={op:'and',xs:[atom,{op:'all',key:'x',c:atom}]}
  expect(freeVariables(scoped)).toEqual(['x'])
})

test('a lowered binder capturing a free parameter is detected', () => {
  const fixture=surfaceFixtures().find(f=>f.id==='free-bound-collision')!
  const mutant:Law={name:fixture.label,forall:'key$1',holds:{op:'<=',a:{op:'get',map:'A',key:{op:'var',name:'key$1'}},b:{op:'var',name:'key$1'}}}
  const counterexample:Model={free:{'key$1':1},maps:{A:[1,1,1]}}
  expect(surfaceMeaning(fixture,counterexample)).toBe(true)
  expect(loweredMeaning(mutant,counterexample)).toBe(false)
  expect(()=>assertAgreement({...fixture,lowered:mutant},[counterexample])).toThrow()
})

test('mutant lowering is detected although its substituted lowered tautology proves', () => {
  const fixture=surfaceFixtures().find(f=>f.id==='exists-forall')!
  const key=fixture.lowered.forall
  if (!key) throw new Error('fixture lost universal binder')
  const mutant:Law={name:'mutant drops existential body', forall:key, holds:{op:'=',a:{op:'var',name:key},b:{op:'var',name:key}}}
  const counterexample:Model={free:{},maps:{A:[2,2,2]}}
  expect(surfaceMeaning(fixture,counterexample)).toBe(false)
  expect(loweredMeaning(mutant,counterexample)).toBe(true)
  expect(()=>assertAgreement({...fixture,lowered:mutant},[counterexample])).toThrow()
  const m=rule('mutant proof control').state({s:0}).step(({s})=>({s})).machine
  expect(proveLaws(m,[mutant])).toMatchObject({proven:true,checked:true})
})


type OrderedStepModel = Model
const orderedBound = [0, 1, 2] as const

function scalar(item:OrderedValue):number {
  if (item.kind !== 'scalar') throw new Error('scalar source evaluator received a record')
  return item.value
}
function sameRecord(a:OrderedValue, b:OrderedValue):boolean {
  return a.kind === 'record' && b.kind === 'record' && a.id === b.id
}
/** Independent concrete source semantics for FIFO's pop(0), not core's AST evaluator. */
function orderedSourceMeaning(fixture:OrderedListFixture):boolean {
  return fixture.before.every(o => fixture.before.every(j => {
    const remains = fixture.valueKind === 'scalar'
      ? fixture.after.some(item => scalar(item) === scalar(o))
      : fixture.after.some(item => sameRecord(item,o))
    if (remains || fixture.predicate === 'membership') return remains
    const left=fixture.valueKind === 'scalar' ? scalar(o) : (o.kind === 'record' ? o.rank : (()=>{ throw new Error('record fixture contains scalar') })())
    const right=fixture.valueKind === 'scalar' ? scalar(j) : (j.kind === 'record' ? j.rank : (()=>{ throw new Error('record fixture contains scalar') })())
    return fixture.predicate === 'equality' ? left === right : left <= right
  }))
}
function orderedModel(fixture:OrderedListFixture):OrderedStepModel {
  if (fixture.valueKind !== 'scalar') throw new Error('a refused record fixture has no lowered model')
  // pop(0) removes key zero; the remaining insertion keys are not renumbered.
  const before=orderedBound.map(index=>index<fixture.before.length?1:0)
  const after=orderedBound.map(index=>index>0 && index<fixture.before.length?1:0)
  return {free:{},maps:{'items.has':before,"items.has'":after}}
}
function orderedLoweredMeaning(law:StepLaw, model:OrderedStepModel):boolean {
  const names=[law.forall,...(law.keys??[])].filter((name):name is string=>name!==undefined)
  const at=(i:number, env:Record<string,number>):boolean => i===names.length
    ? (!law.when || !evalC(law.when,{...env,method:1},model) || evalC(law.then,{...env,method:1},model))
    : orderedBound.every(value=>at(i+1,{...env,[names[i]!]:value}))
  return at(0,{})
}
function assertOrderedAgreement(fixture:OrderedListFixture, law:StepLaw):void {
  const model=orderedModel(fixture)
  expect(orderedLoweredMeaning(law,model), fixture.id+' '+JSON.stringify({before:fixture.before,after:fixture.after,law:fixture.law})).toBe(orderedSourceMeaning(fixture))
}
function assertScalarSourceRefusal(fixtures:readonly OrderedListFixture[]):void {
  const first=fixtures[0]
  if (!first) throw new Error('missing ordered scalar fixture')
  const root=mkdtempSync(join(tmpdir(),'gdp-ordered-surface-'))
  try {
    const file=join(root,'fifo.py')
    writeFileSync(file,first.source)
    const extracted=extractPython(file,{entry:'FIFO',check:{runs:2,depth:3,states:4,probes:false}})
    if (!extracted.ok) throw new Error('scalar FIFO extraction refused: '+JSON.stringify(extracted.refusals))
    for (const law of new Set(fixtures.map(fixture=>fixture.law))) {
      expect(()=>buildLaw(extracted,{name:'ordered '+law,expr:law,method:'take'})).toThrow(ScalarListQuantifierError)
    }
  } finally { rmSync(root,{recursive:true,force:true}) }
}

test('generated scalar FIFO source shapes refuse rather than substitute positions', () => {
  const fixtures=orderedListFixtures(), scalarFixtures=fixtures.filter(fixture=>fixture.valueKind==='scalar')
  // Three values and lengths 0..3: 1 + 3 + 9 + 27 sequences, for each predicate.
  expect(scalarFixtures).toHaveLength((1+3+9+27)*3)
  expect(scalarFixtures.some(fixture=>fixture.before.map(scalar).join(',')==='2,1')).toBe(true)
  expect(scalarFixtures.some(fixture=>fixture.before.map(scalar).join(',')==='1,1')).toBe(true)
  expect(scalarFixtures.filter(fixture=>fixture.before.length===3 && new Set(fixture.before.map(scalar)).size===3)).toHaveLength(6*3)
  expect(scalarFixtures.every(fixture=>fixture.status==='refused' && fixture.refusal==='scalar ordered list')).toBe(true)
  assertScalarSourceRefusal(scalarFixtures)
})

test('record identity is represented in the source oracle and its current extractor refusal stays explicit', () => {
  const fixtures=orderedListFixtures().filter(fixture=>fixture.valueKind==='record')
  expect(fixtures).toHaveLength((1+3+9+27)*3)
  const distinct=fixtures.find(fixture=>fixture.predicate==='membership' && fixture.before.map(item=>item.kind==='record'?item.id:'?').join(',')==='a,b')
  const repeated=fixtures.find(fixture=>fixture.predicate==='membership' && fixture.before.map(item=>item.kind==='record'?item.id:'?').join(',')==='a,a')
  if (!distinct || !repeated) throw new Error('missing record identity controls')
  expect(orderedSourceMeaning(distinct)).toBe(false) // a.rank differs from b.rank, and a itself was removed
  expect(orderedSourceMeaning(repeated)).toBe(true)  // the exact same object remains
  const root=mkdtempSync(join(tmpdir(),'gdp-ordered-record-refusal-'))
  try {
    const file=join(root,'fifo.py')
    writeFileSync(file,distinct.source)
    const extracted=extractPython(file,{entry:'FIFO',check:{runs:2,depth:3,states:4,probes:false}})
    expect(extracted.ok).toBe(false)
    if (!extracted.ok) expect(extracted.refusals.some(refusal=>/one object in two places/.test(refusal.what))).toBe(true)
  } finally { rmSync(root,{recursive:true,force:true}) }
})

function positionalMutant(fixture:OrderedListFixture):StepLaw {
  const o={op:'var',name:'oPosition'} as const, j={op:'var',name:'jPosition'} as const, one={op:'const',value:1} as const
  const remains:C={op:'=',a:{op:'get',map:"items.has'",key:o},b:one}
  const body:C=fixture.predicate==='membership' ? remains : {op:'or',xs:[remains,{op:fixture.predicate==='equality'?'=':'<=',a:o,b:j}]}
  const held:C={op:'and',xs:[{op:'=',a:{op:'get',map:'items.has',key:o},b:one},{op:'=',a:{op:'get',map:'items.has',key:j},b:one}]}
  return {name:'positional list-item mutant',forall:'oPosition',keys:['jPosition'],when:{op:'=',a:{op:'var',name:'method'},b:one},then:{op:'or',xs:[{op:'not',x:held},body]}}
}

test('generated value semantics detects positional substitution for membership, equality and ordering',()=>{
  const mismatches={membership:0,equality:0,order:0}
  for(const fixture of orderedListFixtures().filter(f=>f.valueKind==='scalar')) {
    if(orderedSourceMeaning(fixture)!==orderedLoweredMeaning(positionalMutant(fixture),orderedModel(fixture)))mismatches[fixture.predicate]++
  }
  for(const count of Object.values(mismatches))expect(count).toBeGreaterThan(0)
})

test('the oracle detects both the false FIFO minimum and duplicate-value membership mutants',()=>{
  for(const [predicate,values,source] of [['order','2,1',false],['membership','0,0',true]] as const) {
    const fixture=orderedListFixtures().find(candidate=>candidate.valueKind==='scalar' && candidate.predicate===predicate && candidate.before.map(scalar).join(',')===values)
    if(!fixture)throw Error('missing positional mutant witness')
    const mutant=positionalMutant(fixture)
    expect(orderedSourceMeaning(fixture)).toBe(source)
    expect(orderedLoweredMeaning(mutant,orderedModel(fixture))).toBe(!source)
    expect(()=>assertOrderedAgreement(fixture,mutant)).toThrow()
  }
})
