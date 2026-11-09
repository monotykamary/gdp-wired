// Recover bounded research captures from paired logs. Big packets stay in runs/.
import {readFileSync, mkdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
import {gunzipSync} from 'node:zlib'
const text = readFileSync(process.argv[2]!, 'utf8'), dir = process.argv[3]!
mkdirSync(dir, {recursive: true})
const captures = [...text.matchAll(/T14_CAPTURE_GZIP_BASE64 (\S+)/g)]
if (!captures.length) throw Error('no complete research capture in this receipt')
for (const [i, match] of captures.entries()) {
  const decoded = gunzipSync(Buffer.from(match[1]!, 'base64')), value = JSON.parse(decoded.toString())
  writeFileSync(join(dir, `${i}.json`), decoded)
  console.log(JSON.stringify({path: join(dir, `${i}.json`), roots: value.roots?.length, witnesses: value.witnesses?.length, finiteDrops: value.finiteDrops?.length, family: value.family?.laws?.length}))
}
