import {mkdirSync, readFileSync, writeFileSync} from 'node:fs'
import {brotliDecompressSync, gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
const [file, out] = process.argv.slice(2) as [string, string]
mkdirSync(out, {recursive: true})
const source = readFileSync(file, 'utf8'), lines = source.split('\n')
const line = lines.find(l => l.startsWith('PACK64 ') || l.startsWith('PACKBR '))
if (!line) throw new Error('No proof pack in checked replay')
const bytes = Buffer.from(line.slice(7), 'base64')
const json = (line.startsWith('PACKBR ') ? brotliDecompressSync(bytes) : gunzipSync(bytes)).toString()
writeFileSync(`${out}/pack.json`, json + '\n')
const objects = lines.filter(l => l.startsWith('{')).map(l => JSON.parse(l))
const result = objects.find(o => o.file), profile = objects.find(o => o.wallProfile)?.wallProfile
const summary = {sha256: createHash('sha256').update(json).digest('hex'), bytes: json.length, opaqueColumns: [...new Set(json.match(/⟦[0-9]+⟧/g) ?? [])], result: {checked: result?.checked, branches: result?.branches, counted: result?.counted, wall: result?.wall, insts: result?.insts, actionTrees: result?.actionTrees}, profile}
writeFileSync(`${out}/baseline.json`, JSON.stringify(summary, null, 2) + '\n')
console.log(JSON.stringify(summary))
