// File materialization only, after boat has verified the artifact. No tests,
// source generation, solver work, or receipt adjudication runs here.
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {dirname} from 'node:path'
import {gunzipSync} from 'node:zlib'
const [file = 'runs/lane-i/complete-artifact/complete-ast-artifact.log', prefix = 'AST_SOURCE', output = 'research/lane-i/work-meter/recovery/materialized/raw.patch'] = process.argv.slice(2)
const lines = readFileSync(file, 'utf8').split('\n')
const payload = lines.filter(line => line.startsWith(prefix + '_CHUNK ')).map(line => line.split(' ')[2]).join('')
mkdirSync(dirname(output), {recursive: true})
writeFileSync(output, gunzipSync(Buffer.from(payload, 'base64')))
