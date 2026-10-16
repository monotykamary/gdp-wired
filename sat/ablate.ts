// Before/after for the solver's two optional parts: conflicts (= lemmas) and the best of three wall times.
import {problems} from './bench.ts'
import {solve} from './solver.ts'
const configs = [['neither', {minimize: false, reduce: false}], ['minimize', {minimize: true, reduce: false}], ['reduce', {minimize: false, reduce: true}], ['both', {minimize: true, reduce: true}]] as const
console.log(`| problem | ${configs.map(([n]) => n).join(' | ')} |\n| --- |${configs.map(() => ' --- |').join('')}`)
for (const name of process.argv.slice(2)) {
  const [label, make] = problems.find(([n]) => n.includes(name))!
  const {vars, cnf} = make()
  const cells = configs.map(([, o]) => {
    let best = Infinity, lemmas = 0, lits = 0
    for (let i = 0; i < 3; i++) {
      const t = performance.now(), r = solve(vars, cnf.map(c => [...c]), o)
      best = Math.min(best, performance.now() - t)
      if (r.kind === 'unsat') { const added = r.proof.filter(Array.isArray); lemmas = added.length - 1; lits = added.reduce((s, c) => s + c.length, 0) }
    }
    return `${lemmas} lemmas, ${(lits / lemmas).toFixed(0)} lits avg, ${(best / 1000).toFixed(2)} s`
  })
  console.log(`| ${label} | ${cells.join(' | ')} |`)
}
