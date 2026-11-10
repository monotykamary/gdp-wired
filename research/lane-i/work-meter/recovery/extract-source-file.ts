// File materialization only, after boat has verified the artifact. No tests,
// source generation, solver work, or receipt adjudication runs here.
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
const lines = readFileSync('runs/lane-i/complete-artifact/complete-ast-artifact.log', 'utf8').split('\n')
const payload = lines.filter(line => line.startsWith('AST_SOURCE_CHUNK ')).map(line => line.split(' ')[2]).join('')
mkdirSync('research/lane-i/work-meter/recovery/materialized', {recursive: true})
writeFileSync('research/lane-i/work-meter/recovery/materialized/raw.patch', gunzipSync(Buffer.from(payload, 'base64')))
