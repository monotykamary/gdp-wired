// One production run supplies BOTH receipts; do not schedule separate copies unnecessarily.
import {main} from './entry.ts'
await main('both')
