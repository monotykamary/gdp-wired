// Writes one Lean file per benchmark (bv_decide), for wall-time comparison with bench.ts. `bun lean-probes.ts <dir>`
import {mkdirSync, writeFileSync} from 'node:fs'
const dir = process.argv[2] ?? 'lean-probes'
mkdirSync(dir, {recursive: true})
// Lean's defaults (a 10 s SAT timeout, recursion depth 512) are raised so every probe runs to an answer.
const head = 'import Std.Tactic.BVDecide\nset_option maxRecDepth 100000\n'
// a × b by shift-and-add, spelled out so the normalizer sees additions of shifted, masked copies, not a multiplication.
const shiftAdd = (w: number, a: string, b: string) => Array.from({length: w}, (_, i) => `(if ${b}.getLsbD ${i} then ${a} <<< ${i} else 0#${w})`).join(' + ')
const php = (p: number, h: number) => {
  const x = (i: number, j: number) => `x${i}_${j}`
  const vars = Array.from({length: p}, (_, i) => Array.from({length: h}, (_, j) => x(i, j))).flat()
  const some = Array.from({length: p}, (_, i) => `(${Array.from({length: h}, (_, j) => x(i, j)).join(' || ')})`)
  const apart: string[] = []
  for (let j = 0; j < h; j++) for (let a = 0; a < p; a++) for (let b = a + 1; b < p; b++) apart.push(`(!${x(a, j)} || !${x(b, j)})`)
  return `theorem php (${vars.join(' ')} : Bool) : (${[...some, ...apart].join(' && ')}) = false := by bv_decide`
}
const probes: Record<string, string> = {
  empty: '',
  add_comm32: 'theorem t (a b : BitVec 32) : a + b = b + a := by bv_decide',
  add_assoc16: 'theorem t (a b c : BitVec 16) : (a + b) + c = a + (b + c) := by bv_decide',
  ult_trans32: 'theorem t (a b c : BitVec 32) : a < b → b < c → a < c := by bv_decide',
  ...Object.fromEntries([6, 8, 10, 12, 16].flatMap(w => [
    [`mul_comm${w}`, `theorem t (a b : BitVec ${w}) : a * b = b * a := by bv_decide`],
    [`mul_comm${w}_shiftadd`, `theorem t (a b : BitVec ${w}) : ${shiftAdd(w, 'a', 'b')} = ${shiftAdd(w, 'b', 'a')} := by bv_decide`],
  ])),
  php76: php(7, 6), php87: php(8, 7), php98: php(9, 8), php109: php(10, 9),
}
for (const [name, body] of Object.entries(probes)) writeFileSync(`${dir}/${name}.lean`, head + body.replace(/by bv_decide$/, 'by bv_decide (timeout := 600)') + '\n')
console.log(Object.keys(probes).join(' '))
