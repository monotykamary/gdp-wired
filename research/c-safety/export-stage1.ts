// Stage 1 C safety Lean exporter: runs extractC(..., {safety: true}) on proven
// Stage 1 C programs, independently checks their captured kernel certificates,
// and emits a self-contained Lean 4 project using `decide +kernel` for every
// safety obligation.
//   bun research/c-safety/export-stage1.ts <output-project-dir>
import {mkdirSync, mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'
import {cSafetyArtifactOf, extractC, verifyCSafetyProof} from '../../core/extract-c.ts'
import {kInductionStart, kInductionSteps} from '../../kernel/kernel.ts'
import {leanProject, seedStepProof, smachineToLean} from '../../lean-kernel/emit.ts'

const PROGRAMS: {id: string, file: string, entry?: string, src: string}[] = [
  {
    id: 'c_stage1_ring',
    file: 'ring.c',
    entry: 'ring',
    src: `
      #include <stdint.h>
      struct ring { int head; int slots[8]; };
      void rb_put(struct ring *r, int v) {
        r->slots[r->head] = v;
        r->head = (r->head + 1) % 8;
      }
      int rb_get(struct ring *r, int i) {
        if (i < 0 || i >= 8) return -1;
        return r->slots[i];
      }
    `,
  },
  {
    id: 'c_stage1_lut',
    file: 'lut.c',
    entry: 'lut_state',
    src: `
      #include <stdint.h>
      static const int LUT[4] = {10, 20, 30, 40};
      struct lut_state { int last; };
      int lut_read(struct lut_state *s, int i) {
        if (i < 0 || i >= 4) return 0;
        s->last = LUT[i];
        return s->last;
      }
    `,
  },
]

if (import.meta.main) {
  const outDir = process.argv[2]
  if (!outDir) throw new Error('supply an output project directory')
  const work = mkdtempSync(join(tmpdir(), 'gdp-c-safety-lean-'))
  try {
    const parts: string[] = []
    const theorems: string[] = []
    let usesKind = false
    const summary: {id: string, sites: number, proofKind: string, laws: number, hasFacts: boolean}[] = []
    for (const p of PROGRAMS) {
      const file = join(work, p.file)
      writeFileSync(file, p.src)
      const x = extractC(file, {safety: true, ...(p.entry ? {entry: p.entry} : {})})
      if (!x.ok || !x.safety || x.safety.status !== 'proven')
        throw new Error(`${p.id}: expected proven C safety, got ${x.safety?.status ?? 'none'} (${JSON.stringify(x.refusals)})`)
      const art = cSafetyArtifactOf(x.safety)
      if (!art?.jointProof) throw new Error(`${p.id}: missing captured joint proof artifact`)
      if (!verifyCSafetyProof(art.machine, art.targetLaws, art.jointProof))
        throw new Error(`${p.id}: captured proof failed independent checkLaws/checkKInduction`)
      let body: string
      if (art.jointProof.kind === 'usual') {
        seedStepProof(art.machine, art.jointProof.laws, [], {
          proven: true, checked: true, nodes: 0, leaves: 0,
          proof: {laws: art.jointProof.proof, instances: {}, perStep: {}, trees: {}},
        })
        body = smachineToLean(p.id, art.machine, art.jointProof.laws)
        theorems.push(`${p.id}_laws`)
      } else {
        usesKind = true
        const {assumed, kl, kproof} = art.jointProof
        seedStepProof(art.machine, assumed, kInductionSteps(art.machine, kl), {
          proven: true, checked: true, nodes: 0, leaves: 0, proof: kproof,
        })
        const start = kInductionStart(art.machine, kl, {})
        body = smachineToLean(p.id, art.machine, assumed, {
          kind: {kl, start: {goal: start, tree: kproof.trees[start.name]!, inst: {}}},
        })
        theorems.push(`${p.id}_laws`, `${p.id}_kind_holds`)
      }
      const hasFacts = body.includes(`theorem ${p.id}_facts_hold`)
      if (hasFacts) theorems.push(`${p.id}_facts_hold`)
      if (!body.includes(`theorem ${p.id}_laws`)) throw new Error(`${p.id}: missing ${p.id}_laws in emitted Lean`)
      parts.push(`-- Stage 1 C safety proof: ${p.id}\n${body}`)
      summary.push({
        id: p.id,
        sites: x.safety.issues.length,
        proofKind: art.jointProof.kind,
        laws: art.jointProof.kind === 'usual' ? art.jointProof.laws.length : art.jointProof.assumed.length + 1,
        hasFacts,
      })
    }
    const text = `import History
${usesKind ? 'import KInd\n' : ''}import Sets
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Stage 1 C safety obligations proven by gdp-wired and rechecked in Lean with \`decide +kernel\`. -/

${parts.join('\n\n')}

${theorems.map(t => `#print axioms ${t}`).join('\n')}
`
    mkdirSync(outDir, {recursive: true})
    for (const [name, content] of Object.entries(leanProject(text, {name: 'CSafetyStage1'})))
      writeFileSync(join(outDir, name), content)
    console.log(JSON.stringify({ok: true, outDir, theorems, summary}))
  } finally {
    rmSync(work, {recursive: true, force: true})
  }
}
