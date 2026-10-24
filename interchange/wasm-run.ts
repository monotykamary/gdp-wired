// Runs gdp-wired-check.wasm on one document under a WASI host (node:wasi, in node or bun): the document's file as the
// module's standard input, its report written to standard output. Exit code as the module's (0: every claim accepted).
//   node interchange/wasm-run.ts <module.wasm> <file.json>      (or bun)
import {closeSync, openSync, readFileSync} from 'node:fs'
import {WASI} from 'node:wasi'

const [wasmPath, file] = process.argv.slice(2)
if (!wasmPath || !file) { console.error('usage: wasm-run <module.wasm> <file.json>'); process.exit(2) }
const stdin = openSync(file, 'r')
const wasi = new WASI({version: 'preview1', args: ['gdp-wired-check'], env: {}, stdin, stdout: 1, stderr: 2, returnOnExit: true})
const mod = await WebAssembly.compile(readFileSync(wasmPath))
const inst = await WebAssembly.instantiate(mod, {wasi_snapshot_preview1: wasi.wasiImport} as WebAssembly.Imports)
let code = 0
try { code = wasi.start(inst) ?? 0 } catch { code = 1 }
closeSync(stdin)
process.exit(code)
