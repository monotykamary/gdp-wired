import {diagnostic as d} from './section10-diagnostic.ts'
import {analyzeSection10} from './section10-replay-diagnostic.ts'
const output=process.env.DIAG_OUTPUT;if(!output)throw new Error('DIAG_OUTPUT required')
d.reset(process.argv[3]??'leaf')
await import('./active-source-probe.ts')
analyzeSection10(output)
