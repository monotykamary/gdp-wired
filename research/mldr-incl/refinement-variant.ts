// Research-only scheduling controls inside the remote job's private source copy.
import {readFileSync,writeFileSync} from 'node:fs'
const mode=process.argv[2]!,path='core/counts.ts';let source=readFileSync(path,'utf8')
const replace=(old:string,next:string)=>{if(source.split(old).length!==2)throw Error('variant anchor missing or ambiguous');source=source.replace(old,next)}
const fraction=mode.includes('quarter')&&!mode.includes('three')?0.25:mode.includes('three-quarters')?0.75:mode.includes('half')?0.5:undefined
if(fraction!==undefined)replace('while (seedCount < 64 && clock() < until) {',`while (seedCount < 64 && clock() < until && generation.state.work < generation.state.limit * ${fraction}) {`)
if(mode.includes('reselect'))replace('        const keys = ids(full), lazyRoom = selection.chosen.size < selection.cap', '        if (cached?.key !== key) {\n          const previous = chosenView(full, selection.chosen, selection.cap)\n          selection.chosen = new Set(ids(preferMemberInclusions(m, decls, full, previous, selection.cap, generation.tick)))\n        }\n        const keys = ids(full), lazyRoom = selection.chosen.size < selection.cap')
if(mode.includes('early'))replace('    let wide = false','    if (pass) at = completeCountLawInstances(modelLaws, at, ts, l => reads(l.holds, isCount).size > 0, generation.tick).at\n    let wide = false')
writeFileSync(path,source)
console.log(JSON.stringify({researchVariant:mode,refinementFraction:fraction,earlyCompletion:mode.includes('early'),productionLimitUnchanged:true}))
