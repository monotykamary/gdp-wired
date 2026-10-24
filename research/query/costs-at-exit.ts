// A preload: the costs (core/solver.ts's) at exit, on stderr. Research tooling.
import {costs} from '../../core/solver.ts'
process.on('exit', () => console.error(`costs: ${JSON.stringify(costs)}`))
