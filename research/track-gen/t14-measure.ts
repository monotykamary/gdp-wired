// Diagnostic only: total per-process counted work for harnesses without a work column.
import {fullWork} from '../../kernel/prove.ts'
import {work} from '../../core/solver.ts'
const before = fullWork(), scalar = work.n
process.on('exit', () => console.log(`T14_TOTAL_WORK ${JSON.stringify({full: fullWork() - before, work: work.n - scalar})}`))
