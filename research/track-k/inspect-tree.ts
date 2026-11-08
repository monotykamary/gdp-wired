// Structural inventory only; no checker or prover imports.
import {readFileSync} from 'node:fs'
const {tree} = JSON.parse(readFileSync(process.argv[2]!, 'utf8'))
const groups = new Map<string, {times: number, no: number[], yes: number[]}>()
function visit(t: any): number {
  if ('leaf' in t) return 1
  const no = visit(t.no), yes = visit(t.yes), id = JSON.stringify(t.split)
  const g = groups.get(id) ?? {times: 0, no: [], yes: []}
  g.times++; g.no.push(no); g.yes.push(yes); groups.set(id, g)
  return 1 + no + yes
}
const nodes = visit(tree)
console.log(JSON.stringify({nodes, candidates: [...groups.values()].filter(g => g.times > 1 && g.no.some(n => n > 1)).sort((a,b) => b.times - a.times).map(g => ({times:g.times, minNo:Math.min(...g.no),maxNo:Math.max(...g.no),minYes:Math.min(...g.yes),maxYes:Math.max(...g.yes)}))},null,1))
