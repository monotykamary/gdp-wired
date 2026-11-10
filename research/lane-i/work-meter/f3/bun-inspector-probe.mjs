import {fileURLToPath} from 'node:url'
const child = Bun.spawn([process.execPath, '--inspect=127.0.0.1:9339', fileURLToPath(new URL('./bun-inspector-child.mjs', import.meta.url))], {stdout: 'pipe', stderr: 'pipe'})
let socket, entered = false, ended = false, stack = [], beforeReturn = false, requested = false, serial = 0
const errors = [], messages = []
const send = method => { if (socket?.readyState === WebSocket.OPEN) socket.send(JSON.stringify({id: ++serial, method, params: {}})) }
const request = () => { if (entered && !requested && socket?.readyState === WebSocket.OPEN) { requested = true; send('Debugger.pause') } }
const timer = setTimeout(() => { console.log('BUN_INSPECTOR_GUARD ' + JSON.stringify({entered, ended, requested, stack, errors, messages})); socket?.close(); child.kill('SIGTERM') }, 10000)
const hardTimer = setTimeout(() => child.kill('SIGKILL'), 12000)
async function read(stream, kind) {
  let text = ''
  const reader = stream.getReader(), decoder = new TextDecoder()
  for (;;) {
    const {done, value} = await reader.read(); if (done) break
    const chunk = decoder.decode(value, {stream: true}); text += chunk
    console.log('BUN_INSPECTOR_STREAM ' + JSON.stringify({kind, chunk}))
    if (kind === 'stdout') {
      if (text.includes('LOOP_ENTER')) { entered = true; request() }
      if (text.includes('LOOP_DONE')) { ended = true; socket?.close() }
    } else if (!socket) {
      const url = /ws:\/\/127\.0\.0\.1:9339\/[A-Za-z0-9_-]+/.exec(text)?.[0]
      if (url) {
        socket = new WebSocket(url)
        socket.addEventListener('open', () => {
          if (process.env.BUN_INSPECTOR_HANDSHAKE === '1') { send('Inspector.enable'); send('Runtime.enable') }
          send('Debugger.enable')
          if (process.env.BUN_INSPECTOR_HANDSHAKE === '1') send('Inspector.initialized')
          request()
        })
        socket.addEventListener('message', event => {
          const message = JSON.parse(String(event.data))
          messages.push({method: message.method, id: message.id, error: message.error})
          if (message.error) errors.push(message.error)
          if (message.method === 'Debugger.paused') {
            stack = message.params?.callFrames?.map(frame => ({functionName: frame.functionName, location: frame.location, url: frame.url})) ?? []
            beforeReturn = !ended
            send('Debugger.resume')
          }
        })
        socket.addEventListener('error', event => errors.push(JSON.stringify({type: event.type})))
      }
    }
  }
  return text
}
try {
  const stdout = read(child.stdout, 'stdout'), stderr = read(child.stderr, 'stderr')
  const exit = await child.exited
  const output = await stdout, diagnostic = await stderr
  const matched = stack.some(frame => frame.functionName === 'mainThreadSilentLoop')
  console.log('BUN_EXTERNAL_INSPECTOR_CAPABILITY ' + JSON.stringify({runtime: process.versions.bun, handshake: process.env.BUN_INSPECTOR_HANDSHAKE === '1', exit, entered, ended, requested, beforeReturn, matched, stack, errors, messages, stdout: output, inspectorOpened: !!socket, stderrTail: diagnostic.slice(-1500), scope: 'owned synthetic blocking-loop capability only; no solver, no F3/W claim'}))
  if (exit !== 0 || !matched || !beforeReturn) process.exitCode = 1
} finally { clearTimeout(timer); clearTimeout(hardTimer); socket?.close(); if (child.exitCode === null) { child.kill('SIGTERM'); await child.exited } }
