// Replay or re-export retained evidence without rerunning the production prover.
import {readFileSync, readdirSync, writeFileSync, mkdtempSync} from 'node:fs'
import {join} from 'node:path'
import {tmpdir} from 'node:os'
import {spawnSync} from 'node:child_process'
const dir = process.argv[2]!, only = process.argv.includes('--export-only'), temp = mkdtempSync(join(tmpdir(), 'verify-recheck-'))
const wanted = process.argv.includes('--only') ? process.argv[process.argv.indexOf('--only')+1] : undefined
for (const log of readdirSync(dir).filter(x => x.endsWith('.log') && (!wanted || x === wanted)).sort()) {
  const text = readFileSync(join(dir, log), 'utf8'), b64 = text.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)
  if (!b64) { console.log(JSON.stringify({log, missingArchive: true})); continue }
  const archive = join(temp, log+'.tar.xz')
  writeFileSync(archive, Buffer.from(b64[1]!, 'base64'))
  const unpack = spawnSync('tar', ['-xJf', archive, '-C', temp], {encoding:'utf8'})
  if (unpack.status !== 0) throw new Error(unpack.stderr)
  const json = readdirSync(temp).find(x => x.endsWith('.json') && !x.endsWith('.result.json') && text.includes(`/tmp/verify-capture/${x}`))!
  if (!json) throw new Error(`no packet: ${log}`)
  const target=join(temp,json.replace(/\.json$/,'.lean'))
  const out = spawnSync('bun', ['research/verify-all/export-captured.ts', join(temp,json), target], {encoding:'utf8', timeout:180000})
  console.log(JSON.stringify({log, exportExit:out.status, stderr:out.stderr.slice(0,2000)})); console.log(out.stdout)
  if (!only && log.startsWith('capture-') && out.status===0) {
    const lean = spawnSync('bash',['research/verify-all/check-lean.sh', target],{encoding:'utf8',timeout:1800000,maxBuffer:2000000})
    console.log(JSON.stringify({log, leanExit:lean.status, stdout:lean.stdout.slice(-3000),stderr:lean.stderr.slice(-3000)}))
  }
}
