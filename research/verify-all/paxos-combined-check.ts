// A separately named, semantically justified proof adaptation; never replaces the original packet.
import {readFileSync,writeFileSync,readdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
const sha=(s:string)=>createHash('sha256').update(s).digest('hex')
for(const args of [['research/verify-all/paxos-law12-alpha.ts','v4'],['research/verify-all/paxos-law20-validate.ts']]){
 const out=spawnSync('bun',args,{encoding:'utf8',timeout:120000,maxBuffer:2000000})
 if(out.status!==0)throw Error('source generation failed '+JSON.stringify({args,status:out.status,stderr:out.stderr}))
 console.log('GENERATOR_RECEIPT',JSON.stringify({args,stdoutSha256:sha(out.stdout),stderr:out.stderr}))
}
const dir='runs/verify-all/paxos-law20-work/original/'
const original=readFileSync(dir+readdirSync(dir).find(f=>f.endsWith('.lean'))!,'utf8')
if(sha(original)!=='e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1')throw Error('original Lean identity mismatch')
const header=original.split('theorem verified_check :')[0]!
const alpha=readFileSync('/tmp/paxos-law12-alpha-v4/alpha-check.lean','utf8'),adapt=readFileSync('runs/verify-all/paxos-law20-work/validate.lean','utf8')
if(!alpha.startsWith(header)||!adapt.startsWith(header))throw Error('different retained definitions')
const bridge=`
-- Exactly one flag-binder alpha conversion and two diagnostic leaf replacements.
-- Laws, machine state/step functions and count declarations are not changed by the leaf adaptation.
def combinedPaxosProof : List CEntry := verified_proof.mapIdx fun i ce =>
  if i = 20 then {ce with step := {ce.step with tree := diagnosticAdaptedTree}} else ce

theorem combined_entries_unchanged :
    combinedPaxosProof.map (·.e) = verified_proof.map (·.e) := by rfl

theorem combined_paxos_check :
    checkCMachine paxos_alpha_machine verified_decls combinedPaxosProof = true := by decide +kernel

theorem combined_original_laws (ρ : Nat → Nat) (M : Nat → Nat → Nat)
    (hr : CReach verified_machine verified_decls ρ M)
    (ce : CEntry) (hce : ce ∈ verified_proof) :
    ce.e.Holds ρ (withCnt verified_decls ρ M) := by
  have ha := (paxos_reach_alpha verified_decls ρ M).mpr hr
  have hs := cmachine_sound paxos_alpha_machine verified_decls combinedPaxosProof combined_paxos_check ρ M ha
  have hm : ce.e ∈ combinedPaxosProof.map (·.e) := by
    rw [combined_entries_unchanged]
    exact List.mem_map.mpr ⟨ce, hce, rfl⟩
  obtain ⟨ce', hce', he⟩ := List.mem_map.mp hm
  simpa only [he] using hs ce' hce'

#print axioms combined_entries_unchanged
#print axioms combined_paxos_check
#print axioms combined_original_laws
`
const out=alpha+adapt.slice(header.length)+bridge
if(/\bsorry\b|\badmit\b|native_decide/.test(out))throw Error('untrusted proof placeholder')
writeFileSync('/tmp/paxos-soundness-combined.lean',out)
console.log('COMBINED_INPUTS',JSON.stringify({originalSha256:sha(original),alphaSha256:sha(alpha),adaptSha256:sha(adapt),combinedSha256:sha(out),changedEntries:[20],changedLeafPaths:['YYYYN','N'],alphaBinder:{flag:72,from:29,to:131},claim:'all original captured entries on original counted-machine reachable states; not the original certificate bytes'}))
