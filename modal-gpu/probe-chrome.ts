// Tries Chrome flag sets until one gives a hardware WebGPU adapter: each launch opens a tiny page that posts
// navigator.gpu.requestAdapter()'s info. Usage: bun probe-chrome.ts
const html = `<!doctype html><script type="module">
const a = navigator.gpu ? await navigator.gpu.requestAdapter({powerPreference: 'high-performance'}) : null
await fetch('/r', {method: 'POST', body: JSON.stringify(a ? {vendor: a.info.vendor, architecture: a.info.architecture, description: a.info.description, device: a.info.device, isFallback: a.info.isFallbackAdapter, maxBuf: a.limits.maxStorageBufferBindingSize} : {none: !navigator.gpu ? 'no navigator.gpu' : 'null adapter'})})
</script>`
let got: (v: unknown) => void = () => {}
const server = Bun.serve({port: 4438, hostname: '127.0.0.1', fetch: async req => {
  const u = new URL(req.url)
  if (u.pathname === '/r') { got(await req.json()); return new Response('ok') }
  return new Response(html, {headers: {'content-type': 'text/html'}})
}})
const base = ['--headless=new', '--no-sandbox', '--enable-unsafe-webgpu', '--ignore-gpu-blocklist', '--disable-dev-shm-usage', '--no-first-run', '--user-data-dir=/tmp/probe-profile']
const sets: Record<string, string[]> = {
  'vulkan-feature': ['--enable-features=Vulkan'],
  'vulkan+angle': ['--enable-features=Vulkan', '--use-angle=vulkan'],
  'vulkan+angle+nosurface': ['--enable-features=Vulkan', '--use-angle=vulkan', '--disable-vulkan-surface'],
  'vulkan+gl-angle-vulkan+ozone-headless': ['--enable-features=Vulkan', '--use-gl=angle', '--use-angle=vulkan', '--ozone-platform=headless'],
  'vulkan+egl': ['--enable-features=Vulkan', '--use-gl=egl'],
  'vulkan+angle-swiftshader-gl': ['--enable-features=Vulkan', '--use-angle=swiftshader'],
  'default-webgpu-only': [],
}
for (const [name, extra] of Object.entries(sets)) {
  Bun.spawnSync(['rm', '-rf', '/tmp/probe-profile'])
  const result = new Promise(resolve => { got = resolve; setTimeout(() => resolve({timeout: true}), 20000) })
  const chrome = Bun.spawn(['/usr/bin/google-chrome', ...base, ...extra, '--disable-gpu-sandbox', server.url.href], {stdout: 'ignore', stderr: Bun.file(`/tmp/probe-${name}.log`)})
  const r = await result
  console.log(`${name.padEnd(40)} ${JSON.stringify(r)}`)
  chrome.kill('SIGKILL'); await chrome.exited
  Bun.spawnSync(['pkill', '-KILL', '-f', 'probe-profile'])
}
server.stop(true)
