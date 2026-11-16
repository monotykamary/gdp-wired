import {mkdirSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {liftProject,leanSource} from '../lift/project.ts'
const out=process.argv[2]!
const project=liftProject('',{name:'BapaProof'})
for(const name of ['CertificateBoundErasure','CountedSourceProjection','CountedNoninterference','CountedSourceBridge','SourceInclusion'])project[name+'.lean']=leanSource(name)
project['StructuralWeakening.lean']=leanSource('StructuralWeakening')
project['BapaProof.lean']='import StructuralWeakening\nopen Kern Bapa.StructuralWeakening\nexample (p q r s t : C) : Subsumes (.or (.or p q) r) (.or s (.or q (.or t (.or r p)))) := .orElim (.orElim (.orRight (.orRight (.orRight (.orRight (.refl _))))) (.orRight (.orLeft (.refl _)))) (.orRight (.orRight (.orRight (.orLeft (.refl _)))))\nexample (p q : C) : Subsumes (.not p) (.not (.and p q)) := .neg (.andLeft (.refl _))\n#print axioms Bapa.StructuralWeakening.sound\n#print axioms Bapa.StructuralWeakening.law\n'
const modules=Object.keys(project).filter(n=>n.endsWith('.lean')&&n!=='lakefile.lean').map(n=>n.slice(0,-5))
project['lakefile.lean']='import Lake\nopen Lake DSL\npackage structuraltest\n@[default_target]\nlean_lib StructuralTest where\n  roots := #['+modules.map(n=>'`'+n).join(', ')+']\n'
mkdirSync(out);for(const [name,text]of Object.entries(project))writeFileSync(join(out,name),text)
