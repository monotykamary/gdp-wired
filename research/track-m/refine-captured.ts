// One five-second conditional replay, not a claim about the whole invariant set.
import {check} from '../../kernel/kernel.ts'
import {clock, counted, fullRate, fullWork, grow, withWall} from '../../kernel/prove.ts'
import {prepareCaptured} from './replay-setup.ts'
const [file, input, mode = 'flags'] = process.argv.slice(2), {d, goal} = prepareCaptured(file!, input!, mode)
const ms = 5000, t = performance.now(), w = fullWork()
const result = withWall(t + 10000, () => counted(fullRate, () => grow(goal, new Map(), {nodes: 0, until: clock() + ms}), true))
console.log(JSON.stringify({file,mode,hyps:goal.hyps.length,was:d.hyps.length,counted:Math.round((fullWork()-w)/fullRate),wall:Math.round(performance.now()-t),outcome:'tree' in result?'tree':result.stuck,checked:'tree' in result && check(goal,result.tree)}))
