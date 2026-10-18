// A Linux stand-in for Handwired's runPage (lab/json-search/gpu/chrome.ts, which reads macOS sysctl and
// memory_pressure): serves gpu-page.html, starts headless Chrome with WebGPU on Vulkan, prints the page's console, and
// writes what the page posts to --out. Usage: bun driver.ts --config '<json>' --out result.json [--chrome path]
import {writeFileSync} from 'node:fs'
import page from './gpu-page.html'

const arg = (name: string, fallback?: string) => { const i = process.argv.indexOf(name); return i === -1 ? fallback : process.argv[i + 1] }
const config = JSON.parse(arg('--config', '{"jobs":[]}')!), out = arg('--out', 'result.json')!
const chromePath = arg('--chrome', '/usr/bin/google-chrome')!, timeoutMs = Number(arg('--timeout', '780000'))
let latest: unknown
let finish = () => {}
const finished = new Promise<void>(resolve => { finish = resolve })
const server = Bun.serve({
  port: 4437, hostname: '127.0.0.1', development: false,
  routes: {
    '/bundled': page,
    '/': async request => {
      const bundled = await fetch(new URL('/bundled', request.url))
      return new Response(bundled.body, {headers: {'content-type': 'text/html;charset=utf-8', 'cross-origin-opener-policy': 'same-origin', 'cross-origin-embedder-policy': 'require-corp'}})
    },
    '/config': () => Response.json(config),
    '/result': {POST: async request => { latest = await request.json(); writeFileSync(out, JSON.stringify(latest, null, 1)); if ((latest as {done?: boolean}).done) finish(); return new Response('ok') }},
  },
})
const flags = ['--headless=new', '--no-sandbox', '--enable-unsafe-webgpu', '--enable-webgpu-developer-features', '--enable-features=Vulkan,VulkanFromANGLE',
  '--use-angle=vulkan', '--use-vulkan=native', '--disable-vulkan-surface', '--ignore-gpu-blocklist', '--disable-gpu-sandbox', '--disable-dev-shm-usage',
  '--remote-debugging-port=9437', '--user-data-dir=/tmp/chrome-profile', '--no-first-run', '--disable-background-timer-throttling', '--disable-renderer-backgrounding']
const chrome = Bun.spawn([chromePath, ...flags, 'about:blank'], {stdout: 'ignore', stderr: Bun.file('/tmp/chrome.log')})
const hard = setTimeout(() => { console.log('timed out'); chrome.kill('SIGKILL'); process.exit(2) }, timeoutMs)
try {
  let version: {Browser: string} | undefined
  for (let i = 0; i < 600 && !version; i++) {
    try { version = await (await fetch('http://127.0.0.1:9437/json/version')).json() as {Browser: string} } catch { if (chrome.exitCode !== null) throw new Error(`Chrome exited ${chrome.exitCode}`); await Bun.sleep(100) }
  }
  if (!version) throw new Error('no DevTools answer in 60 s')
  console.log(version.Browser)
  const target = await (await fetch(`http://127.0.0.1:9437/json/new?${encodeURIComponent(server.url.href)}`, {method: 'PUT'})).json() as {webSocketDebuggerUrl: string}
  const socket = new WebSocket(target.webSocketDebuggerUrl)
  await new Promise((resolve, reject) => { socket.onopen = resolve; socket.onerror = reject })
  socket.onmessage = event => {
    const m = JSON.parse(String(event.data)) as {method?: string, params?: {args?: {value?: unknown, description?: string}[], exceptionDetails?: unknown}}
    if (m.method === 'Runtime.consoleAPICalled') console.log(`[page] ${m.params!.args!.map(a => typeof a.value === 'string' ? a.value : JSON.stringify(a.value ?? a.description)).join(' ')}`)
    else if (m.method === 'Runtime.exceptionThrown') console.log(`[page exception] ${JSON.stringify(m.params!.exceptionDetails)}`)
  }
  socket.send(JSON.stringify({id: 1, method: 'Runtime.enable', params: {}}))
  await finished
  socket.close()
} finally {
  clearTimeout(hard)
  chrome.kill('SIGTERM')
  await Promise.race([chrome.exited, Bun.sleep(5000)])
  if (chrome.exitCode === null) chrome.kill('SIGKILL')
  await server.stop(true)
}
