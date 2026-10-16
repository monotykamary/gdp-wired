// One benchmark problem, solve only: `bun one-problem.ts "<name part>" [conflict budget]`, TUNE as in bench.ts.
import {problems} from './bench.ts'
import {solve} from './solver.ts'
const [name, make] = problems.find(([n]) => n.includes(process.argv[2]!))!
const {vars, cnf} = make()
const t0 = performance.now()
const r = solve(vars, cnf, {limit: Number(process.argv[3] ?? Infinity), ...(process.env.TUNE ? JSON.parse(process.env.TUNE) : {}), ...(process.env.RESTARTS === 'luby' ? {restarts: 'luby' as const} : {}), drup: false})
console.log(name, r.kind, ((performance.now() - t0) / 1000).toFixed(2) + ' s', r.kind === 'unsat' ? r.proof.length + ' steps' : r.kind === 'unknown' ? r.conflicts : '')
