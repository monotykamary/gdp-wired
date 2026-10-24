// gdp-wired-check as a WebAssembly module (built by interchange/build.ts with Javy: QuickJS and this bundle in one
// module, WASI preview 1): one document on standard input, its report as JSON on standard output, the same checkDocument
// the CLI runs, over the same trusted files. Exit code: 0 when every claim is accepted, 1 otherwise.
import {checkDocument} from './check.ts'

type IO = {readSync: (fd: number, buf: Uint8Array) => number, writeSync: (fd: number, buf: Uint8Array) => number}
declare const Javy: Partial<IO> & {IO?: IO}
// (Javy's stream builtins: Javy.IO in its releases since 2, Javy itself in some)
const io: IO = Javy.IO ?? (Javy as IO)
const chunks: Uint8Array[] = []
let size = 0
for (;;) {
  const buf = new Uint8Array(1 << 16), n = io.readSync(0, buf)
  if (n <= 0) break
  chunks.push(buf.subarray(0, n)); size += n
}
const all = new Uint8Array(size)
let at = 0
for (const c of chunks) { all.set(c, at); at += c.length }
let report
try { report = checkDocument(JSON.parse(new TextDecoder().decode(all))) } catch (e) { report = {accepted: false, claims: [], malformed: `not JSON: ${e instanceof Error ? e.message : String(e)}`} }
io.writeSync(1, new TextEncoder().encode(`${JSON.stringify(report)}\n`))
if (!report.accepted) throw new Error('refused')
