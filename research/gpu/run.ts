// Opens page.html in a fresh headless Chrome with WebGPU (the json-search lab's driver) and writes what it posts.
//   bun research/gpu/run.ts --profile <new folder> --out <file.json> [--counts 1000,10000,100000,1000000] [--projects 2048]
import {argument, numbers, required, runPage} from '../../vendor/handwired/lab/json-search/gpu/chrome.ts'
import page from './page.html'
import type {PageConfig} from './page.ts'

const config: PageConfig = {
  counts: numbers(argument('--counts') ?? '1000,10000,100000,1000000'),
  projects: Number(argument('--projects') ?? 2048),
  teams: Number(argument('--teams') ?? 512),
  domains: Number(argument('--domains') ?? 200),
  salt: Number(argument('--salt') ?? Math.floor(Math.random() * 1e9)),
  jsLimit: Number(argument('--js-limit') ?? 100_000),
  warmupMs: 200, sampleMs: 1000, minimumSamples: 10, maximumSamples: 100,
  cpuWarmupMs: 0, cpuSampleMs: 0, cpuSamples: 3,
}

await runPage({
  page, config, label: 'access audit', profile: required('--profile'), out: required('--out'),
  port: Number(argument('--port') ?? 4431), devToolsPort: Number(argument('--devtools-port') ?? 9431),
  timeoutMs: 1800 * 1000,
  chromePath: argument('--chrome') ?? '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
})
