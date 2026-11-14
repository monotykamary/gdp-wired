// Small reachable families with hand-built constant contradictions: no prover/search runs.
import {mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {type Law, type Machine, less, n, x} from '../core/machine.ts'
import {type CountCert, type Goal, type Instances, type Path, type Tree, checkCountedLaws, countedObligations, framePath, leafConstraints, mcGoal} from '../kernel/kernel.ts'
import {cmachineToLean, leanProject} from './emit.ts'

export type FamilyCutKind = 'none' | 'frame' | 'mono' | 'linear'
export type FamilyCutFixture = {machine: Machine, laws: Law[], proof: {instances: Record<string, Instances>, certs: Record<string, CountCert>}}
function constantContradiction(goal: Goal, path: Path = new Map()): Tree {
  const rows = leafConstraints(goal, path)
  const index = rows.findIndex(({lin}) => (lin['1'] ?? 0) > 0 && Object.entries(lin).every(([key,value]) => key === '1' || value === 0))
  if (index < 0) throw new Error(`fixture has no constant contradiction: ${goal.name}`)
  return {leaf: [{kind: 'input', index}]}
}
export function familyCutFixture(kind: FamilyCutKind, alpha = false): FamilyCutFixture {
  const machine: Machine = {name: `constant-family-${kind}`, params: [], inputs: [], state: {},
    counts: {C: {j: 'j', key: 'k', below: n(1), body: n(0)}},
    step: alpha ? {flags: {bound: {op: 'all', key: 'g', c: less(x('g'), n(1))}}} : {}}
  const laws: Law[] = [{name: 'constant law', holds: less(n(0),n(1)), ...(alpha ? {forall: 'a', keys: ['g']} : {})}]
  const instances: Record<string, Instances> = {'constant law': {}}
  const certs: Record<string, CountCert> = {}
  for (const obligation of countedObligations(machine, laws, instances)) {
    const step = obligation.goal.name.endsWith(' @step')
    const cert: CountCert = {reads: step ? [['before','C',n(0)],['after','C#',n(0)]] : [], insts: [], tree: {leaf: []}}
    const goal = mcGoal(obligation.goal.hyps, obligation.decls, cert)
    if (!goal) throw new Error('fixture count reads invalid')
    if (step && kind !== 'none') {
      const auxiliary = constantContradiction({name:'zero-body auxiliary',hyps:[less(x('k'),n(1)),less(n(0),n(0))]})
      if (kind === 'frame') cert.frames = [{when:[],post:'after',pre:'before'}]
      if (kind === 'mono') cert.monos = [{when:[],post:'after',pre:'before',tree:auxiliary}]
      if (kind === 'linear') cert.lins = [{when:[],pos:[[1,'after']],neg:[[1,'before']],tree:auxiliary}]
    }
    cert.tree = constantContradiction(goal, framePath(cert.frames ?? [],cert.lemmas ?? [],new Map(),cert.monos ?? [],cert.lins ?? []))
    certs[obligation.goal.name] = cert
  }
  const proof = {instances,certs}
  if (!checkCountedLaws(machine,laws,proof)) throw new Error(`native fixture refused: ${kind}/${alpha}`)
  return {machine,laws,proof}
}
export function brokenFamilyCut(f: FamilyCutFixture): FamilyCutFixture['proof'] {
  const bad = structuredClone(f.proof), step = bad.certs['constant law @step']!
  if (step.frames?.length) step.frames[0]!.pre = 'missing'
  else if (step.monos?.length) step.monos[0]!.tree = {leaf:[]}
  else if (step.lins?.length) step.lins[0]!.tree = {leaf:[]}
  else throw new Error('fixture has no cut')
  if (checkCountedLaws(f.machine,f.laws,bad)) throw new Error('broken cut unexpectedly checks')
  return bad
}
if (import.meta.main) {
  const dir = process.argv[2]
  if (!dir) throw new Error('output directory required')
  mkdirSync(dir,{recursive:true})
  let text = 'import CountMachine\nimport QAlpha\nnamespace Kern\n'
  for (const kind of ['none','frame','mono','linear'] as const) {
    const f = familyCutFixture(kind), id = `family_${kind}`
    text += cmachineToLean(id,f.machine,f.laws,f.proof,kind === 'none' ? [] : [{what:`invalid ${kind} cut`,certs:brokenFamilyCut(f).certs}]) + '\n'
    text += `#print axioms ${id}_laws\n`
  }
  const f = familyCutFixture('frame',true)
  text += cmachineToLean('family_alpha',f.machine,f.laws,f.proof) + '\n#print axioms family_alpha_laws\nend Kern\n'
  for (const [file,source] of Object.entries(leanProject(text))) writeFileSync(join(dir,file),source)
}
