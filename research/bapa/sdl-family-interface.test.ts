import {expect, test} from 'bun:test'
import {mkdtempSync, readFileSync, rmSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join, resolve} from 'node:path'
import {lift} from '../../lean-kernel/lift.ts'

// Run against the retained input, never against a regenerated/search result:
// SDL_CAPTURE=... bun test research/bapa/sdl-family-interface.test.ts
const capture=process.env.SDL_CAPTURE
test.skipIf(!capture)('SDL family names the exact complete derived checker; semantics remain required',()=>{
  const temp=mkdtempSync(join(tmpdir(),'sdl-family-interface-')),out=join(temp,'project')
  try {
    const result=lift(resolve(capture!),resolve('research/bapa/lift-fixtures/simple_decentralized_lock.json'),out)
    const id='bapa_simple_decentralized_lock'
    expect(result.familyTheorem).toBe('Bapa.SdlConcrete.Checked.family')
    expect(result.theoremAliases?.family.target).toBe(id+'_check')
    expect(result.parts?.familySize).toBe(4)
    expect(result.parts?.primaryObligations).toBe(8)
    expect(result.requiredTheorems).toContain(id+'_semantic_laws')
    expect(result.requiredTheorems).toContain(id+'_proof_eq')
    expect(result.requiredTheorems).toContain(id+'_family_size')
    expect(result.sourceProjection.sourceTheorems).toEqual(['bapa_simple_decentralized_lock_source_law'])
    const defs=readFileSync(join(out,id+'_Defs.lean'),'utf8')
    const family=readFileSync(join(out,id+'_Family.lean'),'utf8')
    expect(defs).toContain('withTransparency .all <| Meta.reduce value')
    expect(defs).toContain(`def ${id}_proof : List SEntry := ${id}_literal% ${id}_derived_proof`)
    expect(family).toContain(`theorem ${id}_proof_eq : ${id}_proof = ${id}_derived_proof := by with_unfolding_all rfl`)
    expect(family).toContain(`theorem ${id}_check : checkSMachine ${id}_target_data.plain ${id}_proof = true := by decide +kernel`)
    expect(family).toContain(`theorem ${id}_family_size : ${id}_proof.length = 4`)
    expect(family).toContain(`theorem ${id}_semantic_laws : ∀ ρ M, SReach ${id}_target_data.plain ρ M → ∀ e ∈ ${id}_proof, e.Holds ρ M`)
    // An alias to the old semantic statement must not masquerade as family.
    expect(readFileSync(join(out,'BapaProof.lean'),'utf8')).toContain(`abbrev Bapa.SdlConcrete.Checked.family := @${id}_check`)
  } finally {rmSync(temp,{recursive:true,force:true})}
},120000)
