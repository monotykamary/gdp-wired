// Preserve complete research receipts below the remote stdout retention limit.
import {readFileSync} from 'node:fs'
import {basename} from 'node:path'
import {gzipSync} from 'node:zlib'
for(const file of process.argv.slice(2))console.log(JSON.stringify({artifact:basename(file),encoding:'gzip-base64',data:gzipSync(readFileSync(file)).toString('base64')}))
