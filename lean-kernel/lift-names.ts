// Optional output names never select a strategy or supply a proof body.
import {asked} from './axiom-audit.ts'
import {sha256,type LiftTheoremNames} from './lift/source.ts'
export type LiftNamingSurface={familyTheorem:string,sourceProjection:{sourceTheorems:string[]},requiredTheorems:string[],files:Record<string,string>}
export type LiftAliases={family:{name:string,target:string},source:{name:string,target:string}[]}
export function applyLiftTheoremNames<T extends LiftNamingSurface>(project:Record<string,string>,manifest:T,names?:LiftTheoremNames):T&{theoremAliases?:LiftAliases} {
  if(!names)return manifest
  const valid=(name:unknown):name is string=>typeof name==='string'&&/^(?:[A-Za-z_][A-Za-z0-9_']*\.)*[A-Za-z_][A-Za-z0-9_']*$/.test(name)
  const requested=[names.family,...names.source]
  if(names.source.length!==manifest.sourceProjection.sourceTheorems.length||requested.some(n=>!valid(n))||new Set(requested).size!==requested.length)throw Error('invalid output theorem naming contract')
  const aliases:LiftAliases={family:{name:names.family,target:manifest.familyTheorem},source:names.source.map((name,i)=>({name,target:manifest.sourceProjection.sourceTheorems[i]!}))}
  const pairs=[aliases.family,...aliases.source],known=new Set(manifest.requiredTheorems),root=project['BapaProof.lean']
  if(typeof root!=='string'||pairs.some(p=>!valid(p.target)))throw Error('invalid generated theorem interface')
  const additions:string[]=[]
  for(const {name,target}of pairs){
    if(name===target)continue
    // Existing generated aliases must have definitionally equal propositions;
    // merely finding the requested name is not evidence of source equivalence.
    if(known.has(name))additions.push(`example : @${name} = @${target} := rfl`)
    else {additions.push(`abbrev ${name} := @${target}`);known.add(name)}
  }
  const printed=new Set(asked(root))
  for(const name of requested)if(!printed.has(name)){additions.push('#print axioms '+name);printed.add(name)}
  project['BapaProof.lean']=root+'\n'+additions.join('\n')+'\n'
  return {...manifest,familyTheorem:names.family,sourceProjection:{...manifest.sourceProjection,sourceTheorems:[...names.source]},requiredTheorems:[...new Set([...manifest.requiredTheorems,...requested])],files:Object.fromEntries(Object.entries(project).map(([name,text])=>[name,sha256(text)])),theoremAliases:aliases}
}
