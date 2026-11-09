// Disposable port of Lane E 2047d2be to Lane B's validated range control.
// Production counts.ts is unchanged unless this research script is invoked.
import {readFileSync, writeFileSync} from 'node:fs'
if (process.env.LAB_DISPOSABLE !== '1') throw Error('LAB_DISPOSABLE=1 required')
const path = 'core/counts.ts'
let source = readFileSync(path, 'utf8')
const edits: [string, string][] = [
  ["import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'", "import {preferMemberInclusions} from './count-recovery/member-inclusions.ts'\nimport {independentCountInstances} from './count-focused.ts'\nimport {admitMemberWitnesses,instantiateMemberPremises,memberHints,memberPremiseState,type MemberHint} from './count-recovery/member-premises.ts'"],
  ['at: Instances, ls: Set<string>}>(), isCount', 'at: Instances, ls: Set<string>, wits?: string[]}>(), isCount'],
  ['    const supported = ls.some(l => support.has(l)), modelLaws = supportOrder(ls, caller, support, true)', `    const supported = ls.some(l => support.has(l)), modelLaws = supportOrder(ls, caller, support, true)
    let memberState: ReturnType<typeof memberPremiseState> | undefined
    const members = () => memberState ??= memberPremiseState([m,ls])
    const independent = (before: Instances, next: Instances | undefined, wits: string[] = []) => {
      if(!next)return undefined
      const blocked=[...memberState?.witnesses.values()??[],...cti?.wits??[]]
      return blocked.length?independentCountInstances(m,modelLaws,before,next,[...blocked,...wits]):next
    }`],
  ['models.set(id, {gg, w, at: instances, ls: new Set(ls.map(l => l.name))})', 'models.set(id, {gg, w, at: instances, ls: new Set(ls.map(l => l.name)), wits:[...memberState?.witnesses.values()??[],...cti?.wits??[]]})'],
  ["ptime('mbqi', () => modelInstances(m, modelLaws, at0, cti.gg, cti.w))", "ptime('mbqi', () => independent(at0,modelInstances(m, modelLaws, at0, cti.gg, cti.w)))"],
  ['    const poolCache = new Map<string, {key: string, value: ReturnType<typeof grammarPool>}>()', '    const poolCache = new Map<string, {key: string, value: ReturnType<typeof grammarPool>}>()\n    const memberSources = new Map<string,MemberHint[]>()'],
  ['        selection.previous = full; selection.decls = decls', '        selection.previous = full; selection.decls = decls\n        memberSources.set(goal.name,memberHints(m,decls,c,generation.tick))'],
  ['      const full = pass ? certFor(goal, decls, wide, wide && lazyMode !== \'0\' ? pool : undefined, undefined, structured) : none', `      let full = pass ? certFor(goal, decls, wide, wide && lazyMode !== '0' ? pool : undefined, undefined, structured) : none
      if(pass&&m.inputMaps?.length&&lazyMode!=='0'){
        const proposed=admitMemberWitnesses(m,decls,full,members(),wide?pool:10,generation.tick)
        full=proposed.cert;memberSources.set(goal.name,proposed.hints)
      }`],
  ['        const initial = preferMemberInclusions(m, decls, full, {...full, picks: [], insts: full.insts.slice(0, 10)}, 10, generation.tick)', '        const prefix = {...full, picks: [], insts: full.insts.slice(0, 10)}\n        const initial = memberSources.get(goal.name)?.length ? prefix : preferMemberInclusions(m, decls, full, prefix, 10, generation.tick)'],
  ['      let built = rawBuild()', `      let built = rawBuild()
      if(pass)while(seedCount<64&&clock()<attemptEnd){
        const step=built.at(-1),hints=step&&memberSources.get(step.goal.name)
        if(!step||!hints?.length)break
        const seeded=instantiateMemberPremises(m,ls,at,step.decls,hints,members(),64-seedCount,generation.tick)
        if(!seeded.added.length)break
        at=seeded.at;seedCount+=seeded.added.length
        countsDump.on?.({phase:'member-premises',law:law.name,goal:step.goal.name,pass,added:seeded.added})
        built=rawBuild()
      }`],
  ["ptime('mbqi', () => modelInstances(m, modelLaws, at, step.gg!, q.witness!))", "ptime('mbqi', () => independent(at,modelInstances(m, modelLaws, at, step.gg!, q.witness!),step.c.insts.map(i=>i.wit)))"],
  ["ptime('mbqi', () => modelInstances(m, modelLaws, at, gg, o.witness!))", "ptime('mbqi', () => independent(at,modelInstances(m, modelLaws, at, gg, o.witness!),c.insts.map(i=>i.wit)))"],
]
for (const [before, after] of edits) {
  if (source.split(before).length !== 2) throw Error('non-unique variant anchor: ' + before)
  source = source.replace(before, after)
}
writeFileSync(path, source)
console.log(JSON.stringify({variant: 'lane-e-member-premises', upstream: '2047d2be', edits: edits.length}))
