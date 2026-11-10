import {readFileSync} from 'node:fs'
import {gunzipSync} from 'node:zlib'
import {createHash} from 'node:crypto'
import {stripVTControlCharacters} from 'node:util'
const prefix = (text: string, tag: string) => text.split('\n').filter(line => line.startsWith(tag + ' ')).map(line => JSON.parse(line.slice(tag.length + 1)))
for (const mode of ['plain', 'zero', 'double', 'random']) {
  const text = readFileSync(`meter-results/kernel-meter-${mode}.log`, 'utf8')
  for (const row of prefix(text, 'GENERATOR_CHECK')) {
    const trace = stripVTControlCharacters(gunzipSync(Buffer.from(row.traceGzipBase64, 'base64')).toString())
    if (row.label === 'targeted') {
      const preloads = prefix(trace, 'KERNEL_METER_PRELOAD'), hooks = prefix(trace, 'KERNEL_METER_MUTATION')
      const cases = trace.split('\n').filter(line => line.startsWith('(pass) ') || line.startsWith('(skip) ')).map(line => line.replace(/ \[[0-9.]+m?s\]$/, '')).sort()
      console.log('METER_TEST_DIAG ' + JSON.stringify({mode, exit: row.exit, preloads: preloads.length, hookReceipts: hooks.length, exercisedReceipts: hooks.filter(h => h.exercised).length, lastHook: hooks.at(-1), pass: trace.match(/\b(\d+) pass\b/)?.[1], fail: trace.match(/\b(\d+) fail\b/)?.[1], caseHash: createHash('sha256').update(JSON.stringify(cases)).digest('hex')}))
    } else if (row.exit !== 0) console.log('METER_FAILURE_DIAG ' + JSON.stringify({mode, label: row.label, exit: row.exit, trace: trace.slice(-16000)}))
  }
}
