// Audit-only preload. The original harness file is unchanged. Wrappers only observe return objects.
import {readFileSync, writeFileSync} from 'node:fs'
const captured: {verdict?: any, good?: any, counted?: any, wrappers: string[]} = {wrappers: []}
;(globalThis as any).__verifyObserve = (kind: string, args: any[], out: any) => {
  if (kind === 'proveRule') captured.verdict = {machine: args[0].machine, laws: args[1], out}
  else if (out.proven && out.checked && out.proof) captured.good = {machine: out.machine ?? args[0], laws: out.laws ?? args[1], proof: out.proof, kind}
}
Bun.plugin({name: 'verify-all-observe-returns', setup(build) {
  build.onLoad({filter: /\/(core\/dsl|kernel\/prove)\.ts$/}, ({path}) => {
    let contents = readFileSync(path, 'utf8')
    const names = path.endsWith('/core/dsl.ts') ? ['proveRule'] : ['proveLaws', 'proveSetFast']
    for (const name of names) {
      const anchor = `export function ${name}(`
      if (contents.split(anchor).length !== 2) throw new Error(`nonunique wrapper anchor ${path}:${name}`)
      contents = contents.replace(anchor, `function verifyOriginal_${name}(`)
      contents += `\nexport function ${name}(...args: Parameters<typeof verifyOriginal_${name}>): ReturnType<typeof verifyOriginal_${name}> { const out = verifyOriginal_${name}(...args); (globalThis as any).__verifyObserve('${name}', args, out); return out }\n`
      captured.wrappers.push(`${path}:${name}`)
    }
    return {contents, loader: 'ts'}
  })
}})
const {countsDump} = await import('../../core/counts.ts')
countsDump.on = (x: any) => { if (x.phase === 'closed-family') captured.counted = x }
const log = console.log
console.log = (...args: any[]) => {
  log(...args)
  if (typeof args[0] !== 'string') return
  let row: any
  try { row = JSON.parse(args[0]) } catch { return }
  if (!row.id || !captured.verdict) return
  const file = process.env.VERIFY_CAPTURE
  if (!file) throw new Error('VERIFY_CAPTURE required')
  const text = JSON.stringify({row, ...captured}, (_key, x) => x instanceof Map ? {__map: [...x]} : x instanceof Set ? {__set: [...x]} : x)
  writeFileSync(file, text)
  log(JSON.stringify({capture: file, bytes: text.length, checked: captured.verdict.out.checked, kind: captured.counted ? 'counted' : captured.good?.kind ?? null}))
}
