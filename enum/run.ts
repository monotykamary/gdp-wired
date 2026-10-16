import {argument, required, runPage} from '../vendor/handwired/lab/json-search/gpu/chrome.ts'
import page from './page.html'
import type {EnumConfig} from './page.ts'
const ks = require('fs').readFileSync('js.jsonl', 'utf8').trim().split('\n').map((line: string) => JSON.parse(line)).map((r: any) => ({k: r.k, reachable: r.reachable, violations: r.violations}))
const config: EnumConfig = {ks, salt: Math.floor(Math.random() * 1e9), warmupMs: 200, sampleMs: 1000, minimumSamples: 10, maximumSamples: 100, cpuWarmupMs: 0, cpuSampleMs: 0, cpuSamples: 1}
await runPage({page, config, label: 'enumeration', profile: required('--profile'), out: required('--out'), port: 4433, devToolsPort: 9433, timeoutMs: 1800_000,
  chromePath: argument('--chrome') ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome'})
