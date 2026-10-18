// The suite without a browser: Dawn's node bindings (the `webgpu` npm package) as navigator.gpu, on Vulkan.
// Usage: bun dawn-run.ts --config '<json>' --out result.json   ($DAWN_MODULE: where the package is, default 'webgpu')
import {writeFileSync} from 'node:fs'
import {type Job, runSuite} from './suite.ts'

const arg = (name: string, fallback?: string) => { const i = process.argv.indexOf(name); return i === -1 ? fallback : process.argv[i + 1] }
const config = JSON.parse(arg('--config', '{"jobs":[]}')!) as {jobs: Job[]}, out = arg('--out', 'result.json')!
const dawn = await import(process.env.DAWN_MODULE ?? 'webgpu') as {create: (flags: string[]) => GPU, globals: Record<string, unknown>}
Object.assign(globalThis, dawn.globals)
Object.defineProperty(globalThis.navigator, 'gpu', {value: dawn.create(process.platform === 'linux' ? ['backend=vulkan'] : []), configurable: true})
const report: Record<string, unknown> = {startedAt: new Date().toISOString(), runtime: `bun ${Bun.version} + Dawn (webgpu npm)`}
const write = async () => writeFileSync(out, JSON.stringify(report, null, 1))
try {
  await runSuite(config.jobs, report, line => console.log(line), write)
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  console.log(`error: ${String(error)}`)
}
report['finishedAt'] = new Date().toISOString()
await write()
process.exit(0) // Dawn's instance keeps the event loop alive
