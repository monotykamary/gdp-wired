// Counted retained laws are proposals, never caller laws, facts or assumptions.
import type {Law, Machine} from './machine.ts'
import {admitCountedFamily, type Counted} from './counts.ts'
import {searchWall} from './wall.ts'
import {checkCountedLaws} from '../kernel/kernel.ts'
import {clock, counted, fullRate, withDeadline, withWall} from '../kernel/prove.ts'

export type CountedSeedResult =
  | {status:'checked', closure:Counted, kept:Law[], dropped:Law[]}
  | {status:'inconclusive', reason:string}

// The machine is the producer with conservative derived count declarations;
// the caller retains the unchanged source separately for source projection.
// Only public laws are admission targets. Every returned law is checked again
// as one family; no unverified proposal is published as a given.
export function proveCountedCandidateSeeds(machine:Machine, publicLaws:Law[], candidates:Law[], ms:number):CountedSeedResult {
  if (!Number.isFinite(ms) || ms <= 0) return {status:'inconclusive',reason:'invalid budget'}
  const family=[...publicLaws,...candidates], names=new Set(family.map(l=>l.name))
  if(names.size!==family.length || family.some(l=>!l.name)) return {status:'inconclusive',reason:'duplicate or empty law name'}
  try {
    return withWall(searchWall(ms),()=>counted(fullRate,()=>{
      const until=clock()+ms
      return withDeadline(until,()=>{
        const closure=admitCountedFamily(machine,publicLaws,family,new Set(candidates),until)
        if(!closure.proven || !closure.proof) return {status:'inconclusive',reason:closure.why ?? 'counted family not proven'}
        if(closure.m!==machine || !publicLaws.every(l=>closure.laws.includes(l)) || closure.laws.some(l=>!family.includes(l)) || !checkCountedLaws(closure.m,closure.laws,closure.proof))
          return {status:'inconclusive',reason:'counted family custody or kernel check failed'}
        return {status:'checked',closure,kept:candidates.filter(l=>closure.laws.includes(l)),dropped:candidates.filter(l=>!closure.laws.includes(l))}
      })
    },true))
  } catch (error) {
    return {status:'inconclusive',reason:error instanceof Error ? error.message : String(error)}
  }
}
