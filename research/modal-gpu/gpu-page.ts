// The suite in a browser page (Chrome's WebGPU), configured from /config; see suite.ts. driver.ts serves it.
import {type Job, runSuite} from './suite.ts'

const report: Record<string, unknown> = {startedAt: new Date().toISOString(), userAgent: navigator.userAgent}
const post = (done: boolean) => fetch('/result', {method: 'POST', body: JSON.stringify({...report, done})})
try {
  const config = await (await fetch('/config')).json() as {jobs: Job[]}
  await runSuite(config.jobs, report, line => console.log(line), () => post(false))
} catch (error) {
  report['error'] = String(error instanceof Error ? error.stack : error)
  console.log(`error: ${String(error)}`)
}
await post(true)
