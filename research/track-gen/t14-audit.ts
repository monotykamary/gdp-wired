// Research-only finite witness audit. A rejected default-zero completion is NOT
// a proof that every completion is impossible; the report explicitly separates
// that from a concrete, replayed relative CTI.
import {readFileSync} from 'node:fs'
import {type Law, type Machine, type Request, type State, interpret} from '../../core/machine.ts'
import {finiteEvaluator} from '../../core/finite-houdini.ts'
import {keyValue} from '../../kernel/prove.ts'
import {symbolicStutter} from './t14-stutter.ts'
const input = JSON.parse(readFileSync(process.argv[2]!, 'utf8'))
const prior = input.beforeFinite
if (!prior?.machine) throw Error('missing pre-Houdini family')
const machine = prior.machine as Machine, generated = [...prior.caller, ...prior.candidates] as Law[]
const gp1 = generated.filter(l => !l.name.startsWith('count cubes:') || /never CV\[x\] is 0 and 1 <=/.test(l.name))
const test = finiteEvaluator(machine), run = interpret(machine)
const rows = input.witnesses.map((r: any) => {
  const w: Record<string, number> = r.witness
  const params = Object.fromEntries(machine.params.map(k => [k, w[k] ?? 0]))
  const st: State = {scalars: Object.fromEntries(Object.keys(machine.state).map(k => [k, w[k] ?? 0])), maps: Object.fromEntries(Object.keys(machine.maps ?? {}).map(k => [k, new Map<number, number>()]))}
  const request: Request = Object.fromEntries(machine.inputs.map(k => [k, w[k] ?? 0]))
  for (const k of machine.inputMaps ?? []) request[k] = new Map<number, number>()
  const cells: string[] = [], unreadable: string[] = []
  for (const [name, value] of Object.entries(w)) {
    const br = name.indexOf('['), mp = name.slice(0, br)
    if (br < 0 || !name.endsWith(']') || (!(mp in st.maps) && !(request[mp] instanceof Map))) continue
    const key = keyValue(name, w)
    if (key === undefined) { unreadable.push(name); continue }
    if (mp in st.maps) st.maps[mp]!.set(key, value)
    else (request[mp] as Map<number, number>).set(key, value)
    cells.push(name)
  }
  const missingScalars = [...machine.params, ...Object.keys(machine.state), ...machine.inputs].filter(k => !(k in w))
  const pre = gp1.map(law => ({law: law.name, truth: test(law, params, st)}))
  let postViolation: boolean | undefined, enabled = false, error: string | undefined
  const law = generated.find(l => l.name === r.law)
  try { const post = run.step(params, st, request); enabled = true; if (law) postViolation = test(law, params, post) === false } catch (e) { error = String(e) }
  const stutter = symbolicStutter(machine, w)
  const genuine = pre.every(p => p.truth === true) && enabled && postViolation === true
  if (genuine && stutter.unchanged) throw Error(`inconsistent stutter audit for ${r.law}`)
  return {law: r.law, pass: r.pass, params, scalar: st.scalars, cells, missingScalars, unreadable, phase: r.phase, stutter, classification: genuine ? 'concrete relative CTI against generated Gp1' : stutter.unchanged ? 'symbolic identity transition: no completion can be a relative CTI' : 'default-zero completion does not establish a relative CTI', preFailures: pre.filter(p => p.truth !== true), enabled, postViolation, error}
})
console.log(JSON.stringify({scope: 'concrete default-zero completion; not an exhaustive completion search or an unbounded proof', gp1Laws: gp1.length, witnesses: rows}, null, 2))
