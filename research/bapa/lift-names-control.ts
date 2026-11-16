// Generic naming-only positive/negative Lean control. No protocol or search.
import {mkdirSync,readFileSync,writeFileSync} from 'node:fs'
import {auditLiftLog} from '../../lean-kernel/axiom-audit.ts'
import {join} from 'node:path'
import {applyLiftTheoremNames} from '../../lean-kernel/lift-names.ts'
const out=process.env.SUPERCOMPUTER_OUTPUT_DIR
if(!out)throw Error('run through supercomputer')
const dir=join(out,'alias-control')
if(process.argv.includes('--audit')){
 const required=JSON.parse(readFileSync(join(dir,'EXPECTED.json'),'utf8')) as string[]
 console.log(JSON.stringify(auditLiftLog(readFileSync(join(out,'Good.log'),'utf8'),[readFileSync(join(dir,'Good.lean'),'utf8')],required)))
 process.exit(0)
}
mkdirSync(dir)
const root='theorem canonical_family : True := True.intro\ntheorem canonical_source : False → False := fun h => h\n#print axioms canonical_family\n#print axioms canonical_source\n'
const manifest=()=>({familyTheorem:'canonical_family',sourceProjection:{sourceTheorems:['canonical_source']},requiredTheorems:['canonical_family','canonical_source'],files:{}})
const good={'BapaProof.lean':root}
const first=applyLiftTheoremNames(good,manifest(),{family:'Legacy.Checked.family',source:['legacy_source']})
const named=applyLiftTheoremNames(good,first,{family:"Legacy.Checked.family'",source:["legacy_source'"]})
writeFileSync(join(dir,'EXPECTED.json'),JSON.stringify(named.requiredTheorems))
const bad={'BapaProof.lean':root};applyLiftTheoremNames(bad,manifest(),{family:'canonical_source',source:['canonical_family']})
writeFileSync(join(dir,'lakefile.lean'),'import Lake\nopen Lake DSL\npackage aliascontrol\n')
writeFileSync(join(dir,'lean-toolchain'),'leanprover/lean4:v4.34.0\n')
writeFileSync(join(dir,'Good.lean'),good['BapaProof.lean'])
writeFileSync(join(dir,'Bad.lean'),bad['BapaProof.lean'])
