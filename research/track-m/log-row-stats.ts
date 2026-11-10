// Diagnostic only: an outer 90s observer may record a >60s failure, never a pass.
import {rowReuseStats,rowReuseStorage} from '../../kernel/prover-rows.ts'
const start=performance.now()
process.on('exit',()=>console.log(JSON.stringify({kind:'row-storage',rowsShared:process.env.GDP_ROWS_SHARED!=='0',wallMs:performance.now()-start,stats:rowReuseStats,storage:rowReuseStorage(),memory:process.memoryUsage()})))
