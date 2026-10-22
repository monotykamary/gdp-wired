// Z3 as the outside oracle the drivers check the table's answers with (and solve guards with when sampling): one
// interactive process (`z3 -in`), commands written to it, each answer read back up to an echoed marker. $Z3 names the
// binary (default `z3`).
import type {Subprocess} from 'bun'
import {appendFileSync} from 'node:fs'

export class Z3 {
  private p: Subprocess<'pipe', 'pipe', 'pipe'>
  private buf = ''
  private reader: ReadableStreamDefaultReader<Uint8Array>
  private dec = new TextDecoder()
  calls = 0
  errors = 0
  ms = 0
  constructor(timeoutMs = 5000) {
    this.p = Bun.spawn([process.env.Z3 ?? 'z3', '-in', '-smt2'], {stdin: 'pipe', stdout: 'pipe', stderr: 'pipe'})
    this.reader = this.p.stdout.getReader()
    this.send(`(set-option :print-success false)\n(set-option :timeout ${timeoutMs})\n(set-option :model.completion true)`)
  }
  send(text: string): void { if (process.env.Z3_LOG) appendFileSync(`${process.env.Z3_LOG}.${this.p.pid}`, text + '\n'); void this.p.stdin.write(text + '\n') }
  // everything z3 prints until the marker
  async ask(text: string): Promise<string> {
    const t0 = performance.now()
    this.calls++
    const mark = `@@${this.calls}@@`
    this.send(`${text}\n(echo "${mark}")`)
    void this.p.stdin.flush()
    for (;;) {
      const i = this.buf.indexOf(mark)
      if (i >= 0) {
        let out = this.buf.slice(0, i)
        this.buf = this.buf.slice(i + mark.length).replace(/^\s*\n/, '')
        this.ms += performance.now() - t0
        // an error z3 printed (for this command or one sent before it): reported on stderr, left out of the answer
        const errs = out.match(/^\(error "(?:[^"]|"")*"\)\s*$/gm)
        if (errs) { this.errors += errs.length; if (this.errors <= 5) console.error(`z3: ${errs.join(' ').slice(0, 600)}`); out = out.replace(/^\(error "(?:[^"]|"")*"\)\s*$/gm, '') }
        return out.trim()
      }
      const {value, done} = await this.reader.read()
      if (done) throw new Error(`z3 exited: ${this.buf.slice(-300)}`)
      this.buf += this.dec.decode(value)
    }
  }
  async check(assumptions = ''): Promise<'sat' | 'unsat' | 'unknown'> {
    const out = await this.ask(assumptions ? `(check-sat-assuming (${assumptions}))` : '(check-sat)')
    const w = out.split('\n').map(s => s.trim()).filter(Boolean).at(-1)
    if (w === 'sat' || w === 'unsat' || w === 'unknown') return w
    if (/error/.test(out)) throw new Error(`z3: ${out.slice(0, 400)}`)
    return 'unknown'
  }
  kill(): void { try { this.p.kill() } catch { /* gone */ } }
}

// S-expressions (z3's answers, and the inputs' text)
export type Sx = string | Sx[]
export function parseSx(text: string): Sx[] {
  const out: Sx[] = [], stack: Sx[][] = [out]
  for (const m of text.matchAll(/\s+|;[^\n]*|\(|\)|\|[^|]*\||"(?:[^"]|"")*"|[^\s()|;"]+/g)) {
    const t = m[0]
    if (/^\s|^;/.test(t)) continue
    if (t === '(') { const l: Sx[] = []; stack.at(-1)!.push(l); stack.push(l) } else if (t === ')') { if (stack.length > 1) stack.pop() } else stack.at(-1)!.push(t.startsWith('|') ? t.slice(1, -1) : t)
  }
  return out
}
const SIMPLE = /^(:?[A-Za-z_~!@$%^&*+=<>.?/-][A-Za-z0-9_~!@$%^&*+=<>.?/-]*|\d+(\.\d+)?|#x[0-9a-fA-F]+|#b[01]+|"(?:[^"]|"")*")$/
export const sym = (s: string): string => (SIMPLE.test(s) ? s : `|${s}|`)
export const show = (s: Sx): string => (typeof s === 'string' ? sym(s) : `(${s.map(show).join(' ')})`)
// a value z3 printed: 5, (- 5), true, false
export function value(s: Sx): bigint | boolean {
  if (s === 'true') return true
  if (s === 'false') return false
  if (typeof s === 'string') return BigInt(s)
  if (s[0] === '-' && s.length === 2) return -(value(s[1]!) as bigint)
  throw new Error(`a value ${show(s)}`)
}
// (get-value (t1 t2 ...)) → the values, in order
export async function getValues(z: Z3, terms: string[]): Promise<(bigint | boolean)[]> {
  if (!terms.length) return []
  const out = parseSx(await z.ask(`(get-value (${terms.join(' ')}))`))[0]
  if (!Array.isArray(out)) throw new Error('get-value')
  return out.map(p => value((p as Sx[])[1]!))
}
