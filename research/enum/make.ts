// Writes k<K>.bend (GPU: batch!) and k<K>-cpu.bend for a number of atoms K, 11..31, and prints the expected output.
const k = Number(process.argv[2])
const mask = (bits: number) => (bits >= 32 ? 0xffffffff : 2 ** bits - 1)
const e = (0x55555555 & mask(k)) >>> 0, t = (0x49249249 & mask(k - 2)) >>> 0, top = 2 ** (k - 1)
const fill = (bang: string) => require('fs').readFileSync('template.bend', 'utf8').replace('@BANG@', bang).replace('@D@', String(k - 10)).replace('@E@', String(e)).replace('@T@', String(t)).replace('@TOP@', String(top))
require('fs').writeFileSync(`k${k}.bend`, fill('!'))
require('fs').writeFileSync(`k${k}-cpu.bend`, fill(''))
// The same count in plain JavaScript, timed.
const started = performance.now()
let r = 0, v = 0
for (let w = 0; w < 2 ** k; w++) {
  const reach = ((w >>> 1) & e & ~w) === 0 ? 1 : 0
  const c = w & (w >>> 1) & ~(w >>> 2) & t
  const c2 = (c & ~1) | (c & 1 & (w & top ? 1 : 0))
  r += reach
  v += reach & (c !== 0 ? 1 : 0) & (c2 === 0 ? 1 : 0)
}
const ms = performance.now() - started
console.log(JSON.stringify({k, reachable: r, violations: v, expected: ((Math.imul(r >>> 0, 2654435761) ^ v) >>> 0), jsMs: Math.round(ms * 10) / 10}))
export {}
