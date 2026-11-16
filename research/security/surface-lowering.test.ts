import {expect, test} from 'bun:test'
import {proveLaws} from '../../kernel/prove.ts'
import {rule} from '../../core/dsl.ts'
import type {C, E, Law} from '../../core/machine.ts'
import {duplicatePolicyNames, nestedUniversalAdmission, surfaceFixtures, type SurfaceFixture} from './surface-lowering-fixtures.ts'

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
    default: variablesE(e.a,out); variablesE(e.b,out)
  }
}
function variablesC(c:C, out:Set<string>):void {
  switch(c.op) {
    case '<': case '<=': case '=': variablesE(c.a,out); variablesE(c.b,out); return
    case 'and': case 'or': c.xs.forEach(x=>variablesC(x,out)); return
    case 'not': variablesC(c.x,out); return
    case 'all': variablesC(c.c,out); out.delete(c.key); c.keys?.forEach(key=>out.delete(key)); return
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
