// The Go front end's check (core/extract-go.ts): the rule an extraction prints is run beside the Go code it was read
// from, and any difference refuses the extraction. The code runs as it ships: its package built by the Go toolchain in
// its own module (its go.mod, its dependencies), with a generated harness beside it that makes the object, sets it to
// a state, calls the methods with the requests given, recovers panics, and prints every state as JSON; `go build
// -cover` counts the blocks the requests reached. The requests are core/extract-check.ts's (runs from the start, steps
// from drawn states, steps from the prover's counterexamples), drawn on the rule's side and sent to the code in one
// batch; the rule runs through its interpreter and its generated JavaScript, and every state, map cell, list, result
// and refusal is compared, and the fields the rule leaves out are asked to be unchanged.
import {type Rule, type StepLaw, no, proveSteps, type Kind} from './dsl.ts'
import {type Request, type State, seeded} from './machine.ts'
import {allowed} from './watch.ts'
import type {Arg, Model, Var} from './extract-read.ts'
import * as I from './extract-ir.ts'
import type {B, K, N} from './extract-ir.ts'
import type {Sorts} from './extract-print.ts'
import {type Evidence, type Snap, condAt, conditionsOf, constantsOf, draw, kindOfVar, ruleSnap, ruleState, sameSnap, showSnap} from './extract-check.ts'
import {type GoOptions, type GoPkg, type GoRead, type TT, node} from './extract-go.ts'

export type GoLeaf = {name: string, path: string[], kind: 'int' | 'bool' | 'str' | 'big' | 'bignil' | 'map' | 'mapnil' | 'list' | 'frame', t: number, go: string}
export type GoCheckOptions = {runs?: number, depth?: number, states?: number, seed?: number, bound?: number, probes?: boolean, keep?: string}
export type GoEvidence = Evidence & {unmakeable: number, buildMs: number, runMs: number, blocks?: {file: string, from: number, to: number, hit: boolean}[]}
type Raw = number | boolean | string
type FS = {existsSync: (p: string) => boolean, mkdirSync: (p: string, o?: unknown) => void, readFileSync: (p: string, e: string) => string, writeFileSync: (p: string, s: string) => void, rmSync: (p: string, o?: unknown) => void, mkdtempSync: (p: string) => string}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}

// --- the harness ------------------------------------------------------------------------------------------------------
// Go source beside the package: a state set from JSON and read back as JSON, leaf by leaf; each method called with its
// arguments made from JSON; a panic recovered; the left-out fields compared before and after.
function harness(pkg: GoPkg, read: GoRead, m: Model, discard: boolean): {code: string, imports: Set<string>} {
  const T = (t: number): TT => pkg.ttab[t] ?? {k: 'invalid'}
  const imports = new Set(['encoding/json', 'fmt', 'os', 'reflect', 'strconv', 'math/big'])
  const qual = (t: number) => { const x = T(t); if (x.pkg && !x.own && x.pkg !== '') imports.add(x.pkg) }
  const acc = (path: string[]) => `o.${path.join('.')}`
  const get: string[] = [], set: string[] = []
  const intGet = (e: string, t: number) => (T(t).signed === false ? `strconv.FormatUint(uint64(${e}), 10)` : `strconv.FormatInt(int64(${e}), 10)`)
  const intSet = (dst: string, raw: string, t: number) => {
    qual(t)
    const bits = T(t).bits ?? 64, fn = T(t).signed === false ? 'gdpUint' : 'gdpInt'
    return `if gv, ok := ${fn}(${raw}, ${bits}); ok { ${dst} = ${T(t).go}(gv) } else { return fmt.Errorf("%s outside its type", ${JSON.stringify(dst)}) }`
  }
  for (const l of read.leaves) {
    const a = acc(l.path), k = JSON.stringify(l.name)
    switch (l.kind) {
      case 'int': get.push(`s[${k}] = ${intGet(a, l.t)}`); set.push(`if r, ok := s[${k}]; ok { ${intSet(a, 'r', l.t)} }`); break
      case 'bool': get.push(`s[${k}] = ${a}`); set.push(`if r, ok := s[${k}]; ok { if err := json.Unmarshal(r, &${a}); err != nil { return err } }`); break
      case 'str': get.push(`s[${k}] = ${a}`); set.push(`if r, ok := s[${k}]; ok { if err := json.Unmarshal(r, &${a}); err != nil { return err } }`); break
      case 'big': {
        const nk = JSON.stringify(`${l.name}_nil`)
        get.push(`if ${a} == nil { s[${k}] = "0"; s[${nk}] = true } else { s[${k}] = ${a}.String(); s[${nk}] = false }`)
        set.push(`{ var isNil bool; if r, ok := s[${nk}]; ok { json.Unmarshal(r, &isNil) }; if isNil { ${a} = nil } else if r, ok := s[${k}]; ok { var t string; json.Unmarshal(r, &t); z, ok := new(big.Int).SetString(t, 10); if !ok { return fmt.Errorf("bad big") }; ${a} = z } }`)
        break
      }
      case 'map': {
        const d = m.maps.find(x => x.name === l.name)!, mt = T(l.t), kt = mt.key!, vt = mt.elem!, nk = JSON.stringify(`${l.name}_nil`)
        qual(l.t)
        const keyOut = T(kt).k === 'int' ? intGet('key', kt) : 'string(key)'
        const cellOut = d.scalar ? (T(vt).k === 'int' ? `map[string]any{"value": ${intGet('val', vt)}}` : 'map[string]any{"value": val}')
          : `map[string]any{${d.fields.map(f => { const ft = T(vt).fields!.find(g => g.name === f.name)!.t; return `${JSON.stringify(f.name)}: ${T(ft).k === 'int' ? intGet(`val.${f.name}`, ft) : `val.${f.name}`}` }).join(', ')}}`
        get.push(`{ s[${nk}] = ${a} == nil; cells := map[string]any{}; for key, val := range ${a} { cells[${keyOut}] = ${cellOut} }; s[${k}] = cells }`)
        const keyIn = T(kt).k === 'int' ? `var key ${T(kt).go}; ${intSet('key', 'json.RawMessage(strconv.Quote(ks))', kt)}` : `key := ${T(kt).go}(ks)`
        const cellIn = d.scalar ? (T(vt).k === 'int' ? `var val ${T(vt).go}; ${intSet('val', 'c["value"]', vt)}` : `var val ${T(vt).go}; json.Unmarshal(c["value"], &val)`)
          : `var val ${T(vt).go}; ${d.fields.map(f => { const ft = T(vt).fields!.find(g => g.name === f.name)!.t; return T(ft).k === 'int' ? intSet(`val.${f.name}`, `c[${JSON.stringify(f.name)}]`, ft) : `json.Unmarshal(c[${JSON.stringify(f.name)}], &val.${f.name})` }).join('; ')}`
        set.push(`{ var isNil bool; if r, ok := s[${nk}]; ok { json.Unmarshal(r, &isNil) }; var cells map[string]map[string]json.RawMessage; if r, ok := s[${k}]; ok { json.Unmarshal(r, &cells) }; if isNil { ${a} = nil; if len(cells) > 0 { return fmt.Errorf("a nil map with keys") } } else { ${a} = ${T(l.t).go}{}; for ks, c := range cells { ${keyIn}; ${cellIn}; ${a}[key] = val } } }`)
        break
      }
      case 'list': {
        const et = T(l.t).elem!
        qual(l.t)
        get.push(`{ xs := []any{}; for _, x := range ${a} { xs = append(xs, ${T(et).k === 'int' ? intGet('x', et) : 'x'}) }; s[${k}] = xs }`)
        set.push(`if r, ok := s[${k}]; ok { var xs []json.RawMessage; json.Unmarshal(r, &xs); ${a} = nil; for _, x := range xs { var v ${T(et).go}; ${T(et).k === 'int' ? intSet('v', 'x', et) : 'json.Unmarshal(x, &v)'}; ${a} = append(${a}, v) } }`)
        break
      }
      // A big.Int's nil flag and a map's are set with their values; a left-out field is compared, not set.
      case 'bignil': case 'mapnil': case 'frame': break
    }
  }
  const frames = read.leaves.filter(l => l.kind === 'frame')
  // The methods: their arguments made from JSON (a struct the caller gives: a fresh one with the fields given).
  const calls: string[] = []
  for (const meth of read.methods) {
    const lines: string[] = []
    meth.params.forEach((pa, i) => {
      const t = T(pa.t), raw = `a[${i}]`
      if (pa.arg.k === 'input') {
        if (t.k === 'int') { lines.push(`var a${i} ${t.go}`); lines.push(intSet(`a${i}`, raw, pa.t).replace('return fmt.Errorf', 'return nil, fmt.Errorf')) }
        else if (t.k === 'ptr') lines.push(`a${i}, ok${i} := new(big.Int).SetString(gdpStr(${raw}), 10); if !ok${i} { return nil, fmt.Errorf("bad big") }`)
        else { lines.push(`var a${i} ${t.go}`); lines.push(`if err := json.Unmarshal(${raw}, &a${i}); err != nil { return nil, err }`) }
      } else if (pa.arg.k === 'rec') {
        const st = T(t.elem!)
        lines.push(`a${i} := &${st.go}{}`)
        lines.push(`var f${i} map[string]json.RawMessage; json.Unmarshal(${raw}, &f${i})`)
        for (const [f] of pa.arg.fields) {
          const ft = st.fields!.find(g => g.name === f)!.t, fx = T(ft)
          if (fx.k === 'int') lines.push(`if r, ok := f${i}[${JSON.stringify(f)}]; ok { ${intSet(`a${i}.${f}`, 'r', ft).replace('return fmt.Errorf', 'return nil, fmt.Errorf')} }`)
          else if (fx.k === 'ptr') lines.push(`if r, ok := f${i}[${JSON.stringify(f)}]; ok { z, ok := new(big.Int).SetString(gdpStr(r), 10); if !ok { return nil, fmt.Errorf("bad big") }; a${i}.${f} = z }`)
          else lines.push(`if r, ok := f${i}[${JSON.stringify(f)}]; ok { json.Unmarshal(r, &a${i}.${f}) }`)
        }
      }
    })
    const argList = meth.params.map((_, i) => `a${i}`).join(', ')
    const kept = meth.results.filter((_, i) => !(meth.err && i === meth.results.length - 1))
    const outs = [...kept.map((_, i) => `r${i}`), ...(meth.err ? ['err'] : [])]
    const recv = meth.ptr ? 'o' : '(*o)'
    const invoke = outs.length ? `${outs.join(', ')} := ${recv}.${meth.name}(${argList})` : `${recv}.${meth.name}(${argList})`
    const keptOut = kept.length ? (T(kept[0]!).k === 'int' ? `res.Out = ${intGet('r0', kept[0]!)}; res.HasOut = true` : 'res.Out = r0; res.HasOut = true') : ''
    calls.push(`case ${JSON.stringify(meth.name)}:\n\t\t${lines.join('\n\t\t')}\n\t\treturn func(res *gdpRes) { ${invoke}; ${keptOut}${meth.err ? '; if err != nil { res.Err = err.Error() }' : ''} }, nil`)
  }
  const code = `// Generated by gdp-wired's Go check (core/extract-go-check.ts): the package's code is called as it is.
package ${pkg.package}

import (
${[...imports].sort().map(p => `\t${JSON.stringify(p)}`).join('\n')}
)

type gdpStep struct {
	M string            \`json:"m"\`
	A []json.RawMessage \`json:"a"\`
}
type gdpEp struct {
	From  map[string]json.RawMessage \`json:"from"\`
	Steps []gdpStep                  \`json:"steps"\`
}
type gdpRes struct {
	State  map[string]any \`json:"state,omitempty"\`
	Out    any            \`json:"out,omitempty"\`
	HasOut bool           \`json:"hasOut,omitempty"\`
	Err    string         \`json:"err,omitempty"\`
	Panic  string         \`json:"panic,omitempty"\`
	Bad    string         \`json:"bad,omitempty"\`
	Frame  string         \`json:"frame,omitempty"\`
}

var _ = reflect.DeepEqual
var _ = big.NewInt
var _ = strconv.Itoa

func gdpInt(r json.RawMessage, bits int) (int64, bool) {
	v, err := strconv.ParseInt(gdpStr(r), 10, bits)
	return v, err == nil
}
func gdpUint(r json.RawMessage, bits int) (uint64, bool) {
	v, err := strconv.ParseUint(gdpStr(r), 10, bits)
	return v, err == nil
}
func gdpStr(r json.RawMessage) string {
	var s string
	if json.Unmarshal(r, &s) == nil {
		return s
	}
	return string(r)
}
func gdpGet(o *${read.entry}) map[string]any {
	s := map[string]any{}
	${get.join('\n\t')}
	return s
}
func gdpSet(o *${read.entry}, s map[string]json.RawMessage) error {
	${set.join('\n\t')}
	return nil
}
func gdpFrame(o *${read.entry}) []any {
	return []any{${frames.map(l => acc(l.path)).join(', ')}}
}

var gdpFrameNames = []string{${frames.map(l => JSON.stringify(l.path.join('.'))).join(', ')}}

func gdpCall(o *${read.entry}, m string, a []json.RawMessage) (func(*gdpRes), error) {
	switch m {
	${calls.join('\n\t')}
	}
	return nil, fmt.Errorf("no method %s", m)
}
func gdpRoundTrip(o *${read.entry}) map[string]json.RawMessage {
	b, _ := json.Marshal(gdpGet(o))
	var s map[string]json.RawMessage
	json.Unmarshal(b, &s)
	return s
}
func gdpRun(o *${read.entry}, st gdpStep) (res gdpRes) {
	call, err := gdpCall(o, st.M, st.A)
	if err != nil {
		res.Bad = err.Error()
		return
	}
	before := gdpFrame(o)
	pre := gdpRoundTrip(o)
	func() {
		defer func() {
			if r := recover(); r != nil {
				res.Panic = fmt.Sprint(r)
			}
		}()
		call(&res)
	}()
	after := gdpFrame(o)
	for i := range before {
		if !reflect.DeepEqual(before[i], after[i]) {
			res.Frame = gdpFrameNames[i]
		}
	}
	if ${discard ? 'true' : 'false'} && (res.Err != "" || res.Panic != "") {
		gdpSet(o, pre)
	}
	res.State = gdpGet(o)
	return
}

// GdpHarnessMain runs the episodes in the file in and writes their results to the file out.
func GdpHarnessMain(in, out string) {
	b, err := os.ReadFile(in)
	if err != nil {
		panic(err)
	}
	var eps []gdpEp
	if err := json.Unmarshal(b, &eps); err != nil {
		panic(err)
	}
	all := [][]gdpRes{}
	for _, ep := range eps {
		o := new(${read.entry})
		rs := []gdpRes{}
		if ep.From != nil {
			if err := gdpSet(o, ep.From); err != nil {
				all = append(all, []gdpRes{{Bad: "state: " + err.Error()}})
				continue
			}
		}
		for _, st := range ep.Steps {
			rs = append(rs, gdpRun(o, st))
		}
		all = append(all, rs)
	}
	ob, _ := json.Marshal(all)
	if err := os.WriteFile(out, ob, 0o644); err != nil {
		panic(err)
	}
}
`
  return {code, imports}
}

// --- the module the package is in -------------------------------------------------------------------------------------
function moduleOf(dir: string): {root: string, path: string, module: string} {
  const fs = node<FS>('node:fs')
  let d = dir.replace(/\/$/, '')
  const parts: string[] = []
  for (;;) {
    if (fs.existsSync(`${d}/go.mod`)) {
      const mod = /^module\s+(\S+)/m.exec(fs.readFileSync(`${d}/go.mod`, 'utf8'))?.[1]
      if (!mod) throw new Error(`${d}/go.mod names no module`)
      return {root: d, path: [mod, ...parts].join('/'), module: mod}
    }
    const up = d.split('/').slice(0, -1).join('/')
    if (!up || up === d) throw new Error(`no go.mod above ${dir}`)
    parts.unshift(d.split('/').pop()!)
    d = up
  }
}
const goEnv = () => ({...(globalThis as {process?: {env?: Record<string, string>}}).process?.env, GOFLAGS: '-mod=mod -buildvcs=false', GOWORK: 'off'})

// --- the check --------------------------------------------------------------------------------------------------------
type Outcome = {k: 'ok', st: State, snap: Snap, out?: Raw} | {k: 'refused', why: string, edge: boolean} | {k: 'outside', why: string}
type PlanStep = {e: Model['events'][number], inputs: Record<string, Raw>, raw: Record<string, Raw>, before: Snap, o: Outcome, where: string}
type Episode = {from?: Snap, steps: PlanStep[]}
export function checkGo(dir: string, pkg: GoPkg, read: GoRead, r: Rule, sorts: Sorts, gopts: GoOptions): GoEvidence {
  const opts = gopts.check ?? {}, m = read.model
  const t0 = performance.now(), rand = seeded((opts.seed ?? 7) >>> 0 || 1), bound = opts.bound ?? 12
  const interp = r.interpreter(), gen = r.compiled(), machine = r.machine
  const ev: GoEvidence = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, unmakeable: 0, buildMs: 0, runMs: 0}
  const fail = (what: string): GoEvidence => { ev.mismatch = what; ev.ms = Math.round(performance.now() - t0); return ev }
  const consts = constantsOf(m), strs = ['a', 'b', 'c', '']
  const ranges = rangesOf(m, read, pkg)
  const ps = r.encodeParams({} as never)
  const edges = edgeConditions(m, read)
  // A drawn number within its variable's type (a value of the type is all the code can hold); a quarter of them at
  // the type's own edges (where Go wraps).
  const fit = (x: Raw, name: string): Raw => {
    if (typeof x !== 'number') return x
    const rg = ranges.get(name)
    if (!rg) return x
    if (rand(4) === 0 && rg[1] < Number.MAX_SAFE_INTEGER) { const e = [rg[0], rg[0] + 1, rg[1] - 1, rg[1]]; return e[rand(4)]! }
    const [lo, hi] = rg
    if (x >= lo && x <= hi) return x
    if (Number.isFinite(hi) && Number.isFinite(lo)) return lo + (((x - lo) % (hi - lo + 1)) + (hi - lo + 1)) % (hi - lo + 1)
    return x < lo ? lo : x
  }
  // --- the rule's side, step by step
  const ruleInputs = (inputs: Record<string, Raw>, e: Model['events'][number]): Record<string, Raw> => {
    const used = new Set<string>()
    const walk = (a: Arg) => { if (a.k === 'input') used.add(a.name); else if (a.k === 'rec') a.fields.forEach(([, x]) => walk(x)) }
    e.args.forEach(walk)
    return Object.fromEntries(m.inputs.map(v => [v.name, v.name in e.select ? e.select[v.name]! : used.has(v.name) ? inputs[v.name]! : v.sort.k === 'num' ? 0 : v.sort.k === 'bool' ? false : v.sort.k === 'choice' ? v.sort.values[0]! : '']))
  }
  const ruleStep = (st: State, before: Snap, raw: Record<string, Raw>): Outcome | string => {
    let enc: Request
    try { enc = r.encodeInput(raw as never, {} as never) } catch (x) { return {k: 'refused', why: `outside the input's kind (${(x as Error).message})`, edge: false} }
    try {
      if (!allowed(machine, interp, ps, st, enc)) return {k: 'refused', why: 'the assumption', edge: edges.some(c => evalB(c, before, raw))}
      const s1 = interp.step(ps, st, enc), s2 = gen.step(ps, gen.fork(st), enc)
      if (JSON.stringify(r.decode(s2)) !== JSON.stringify(r.decode(s1))) return `the rule's interpreter and its generated JavaScript differ (${JSON.stringify(r.decode(s1))} against ${JSON.stringify(r.decode(s2))})`
      ev.compiledAgreed++
      const snap = ruleSnap(r, m, s1, sorts), d = r.decode(s1), res = m.results?.[e0(raw)] as {k: string, name: string} | undefined
      return {k: 'ok', st: s1, snap, ...(res?.k === 'scalar' ? {out: d[res.name] as Raw} : {})}
    } catch (x) {
      const msg = (x as Error).message
      return /2\^53|safe integer/.test(msg) ? {k: 'outside', why: msg} : {k: 'refused', why: msg, edge: false}
    }
  }
  const e0 = (raw: Record<string, Raw>) => String(raw[m.event!])
  const drawRequest = (st: Snap) => {
    const e = m.events[rand(m.events.length)]!, near = [...consts, ...Object.values(st.leaves).filter((x): x is number => typeof x === 'number')], inputs: Record<string, Raw> = {}
    const keys = Object.values(st.maps).flatMap(c => Object.keys(c))
    for (const v of m.inputs) {
      if (v.name in e.select) { inputs[v.name] = e.select[v.name]!; continue }
      // A number outside its type now and then (the rule must refuse what the code can't be given).
      const x = draw(v.sort, sorts, v.name, rand, near, bound, [...strs, ...keys])
      inputs[v.name] = rand(8) === 0 ? x : fit(x, v.name)
    }
    return {e, inputs}
  }
  const plan: Episode[] = []
  const runs = opts.runs ?? 200, depth = opts.depth ?? 12
  for (let run = 0; run < runs; run++) {
    let st = interp.init(ps), snap = ruleSnap(r, m, st, sorts)
    const steps: PlanStep[] = []
    for (let d = 0; d < depth; d++) {
      const {e, inputs} = drawRequest(snap), raw = ruleInputs(inputs, e), o = ruleStep(st, snap, raw)
      if (typeof o === 'string') return fail(`run ${run + 1}, request ${d + 1}: ${o}`)
      steps.push({e, inputs, raw, before: snap, o, where: `run ${run + 1}, request ${d + 1}`})
      // Past the safe integers, or past a type's range where the rule refuses and Go wraps, the two part by design.
      if (o.k === 'outside' || (o.k === 'refused' && o.edge)) break
      if (o.k === 'ok') { st = o.st; snap = o.snap }
    }
    plan.push({steps})
  }
  // Single steps from drawn states, every value of each leaf's type.
  const drawSnap = (): Snap => {
    const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}, lists: Record<string, Raw[]> = {}
    for (const v of m.state) {
      if (m.outputs.includes(v.name)) continue
      let x = draw(v.sort, sorts, v.name, rand, consts, bound, strs)
      if (typeof x === 'number' && sorts.get(v.name) === 'nat' && x < 0) x = -x
      if (typeof x === 'number' && Math.abs(x) > Number.MAX_SAFE_INTEGER / 4) x = rand(bound)
      leaves[v.name] = fit(x, v.name)
    }
    // A nil *big.Int holds 0 (the rule's encoding of it); a nil map no key.
    for (const l of read.leaves) if (l.kind === 'big' && leaves[`${l.name}_nil`] === true) leaves[l.name] = 0
    for (const d of m.maps) {
      const cells: Snap['maps'][string] = {}
      if (leaves[`${d.name}_nil`] !== true) for (let i = rand(4); i > 0; i--) {
        const key = d.key === 'str' ? strs[rand(3)]! : String(rand(4))
        cells[key] = Object.fromEntries(d.fields.map(f => { let x = draw(f.sort, sorts, `${d.name}.${f.name}`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.${f.name}`) === 'nat') x = Math.abs(x); return [f.name, fit(x, `${d.name}.${f.name}`)] }))
      }
      maps[d.name] = cells
    }
    for (const d of m.lists ?? []) { const f = d.fields[0]!; lists[d.name] = Array.from({length: rand(4)}, () => { let x = draw(f.sort, sorts, `${d.name}.$item`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.$item`) === 'nat') x = Math.abs(x); return fit(x, `${d.name}.$item`) }) }
    return {leaves, maps, ...(m.lists?.length ? {lists} : {})}
  }
  const single = (snap: Snap, inputs: Record<string, Raw>, e: Model['events'][number], where: string): string | undefined => {
    const st = ruleState(interp.init(ps), snap, m, sorts), raw = ruleInputs(inputs, e), o = ruleStep(st, snap, raw)
    if (typeof o === 'string') return `${where}: ${o}`
    plan.push({from: snap, steps: [{e, inputs, raw, before: snap, o, where}]})
    return undefined
  }
  for (let i = 0; i < (opts.states ?? 400); i++) {
    const snap = drawSnap(), {e, inputs} = drawRequest(snap)
    const bad = single(snap, inputs, e, `drawn state ${i + 1}`)
    if (bad) return fail(bad)
  }
  // Steps from the prover's counterexamples: each condition of the step, refuted as "never holds".
  if (opts.probes !== false) {
    for (const [i, c] of conditionsOf(m).entries()) {
      ev.probes.conditions++
      let law: StepLaw
      try { law = r.stepLaw(`probe ${i + 1}`, () => no, env => condAt(c, env as Record<string, unknown>)) } catch { continue }
      const v = proveSteps(r as never, [], [law], {search: false})
      if (v.proven || !v.witness) continue
      ev.probes.witnesses++
      const w = v.witness, inputs: Record<string, Raw> = {}, leaves: Record<string, Raw> = {}
      let ok = true
      const dec = (vv: Var, k: Kind<unknown>, at: Record<string, Raw>) => { try { at[vv.name] = k.decode(vv.name, Object.fromEntries(k.vars(vv.name).map(part => [part, w[part] ?? 0]))) as Raw } catch { ok = false } }
      for (const vv of m.inputs) dec(vv, kindOfVar(vv, sorts), inputs)
      for (const vv of m.state) if (!m.outputs.includes(vv.name)) dec(vv, kindOfVar(vv, sorts), leaves)
      if (!ok) continue
      for (const l of read.leaves) if (l.kind === 'big' && leaves[`${l.name}_nil`] === true) leaves[l.name] = 0
      const e = m.events.find(x => Object.entries(x.select).every(([n, val]) => inputs[n] === val)) ?? m.events[0]!
      const bad = single({leaves, maps: Object.fromEntries(m.maps.map(d => [d.name, {}])), ...(m.lists?.length ? {lists: Object.fromEntries(m.lists.map(d => [d.name, []]))} : {})}, inputs, e, `the prover's witness for ${JSON.stringify(c).replace(/"op":/g, '').slice(0, 120)}`)
      ev.probes.steps++
      if (bad) return fail(bad)
    }
  }
  // --- the code's side: one batch through the harness
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os')
  const mod = moduleOf(dir), work = fs.mkdtempSync(`${os.tmpdir()}/gdp-gocheck-`)
  const hfile = `${dir.replace(/\/$/, '')}/zz_gdp_harness_gen.go`, mainDir = `${mod.root}/gdpharness_${Date.now().toString(36)}`
  const {code} = harness(pkg, read, m, gopts.onError === 'discard')
  const importPath = mod.path
  const b0 = performance.now()
  try {
    fs.writeFileSync(hfile, code)
    fs.mkdirSync(mainDir, {recursive: true})
    fs.writeFileSync(`${mainDir}/main.go`, `package main\n\nimport (\n\t"os"\n\n\tpkg ${JSON.stringify(importPath)}\n)\n\nfunc main() { pkg.GdpHarnessMain(os.Args[1], os.Args[2]) }\n`)
    if (opts.keep) { fs.mkdirSync(opts.keep, {recursive: true}); fs.writeFileSync(`${opts.keep}/harness.go`, code) }
    try {
      // The harness's own package in -coverpkg too: the counters are written only where main is instrumented.
      cp.execFileSync('go', ['build', '-cover', `-coverpkg=${importPath},${mod.module}/${mainDir.split('/').pop()}`, '-o', `${work}/harness`, `./${mainDir.split('/').pop()}`], {cwd: mod.root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: goEnv(), maxBuffer: 1 << 26})
    } catch (x) {
      const err = String((x as {stderr?: string}).stderr ?? (x as Error).message)
      return fail(`the package doesn't build with the check's harness: ${err.split('\n').filter(Boolean).slice(0, 6).join(' | ')}`)
    }
    ev.buildMs = Math.round(performance.now() - b0)
    // The episodes as the harness reads them: each request's arguments in its parameters' order.
    const argJson = (a: Arg, inputs: Record<string, Raw>): unknown => (a.k === 'input' ? (typeof inputs[a.name] === 'number' ? String(inputs[a.name]) : inputs[a.name]) : a.k === 'rec' ? Object.fromEntries(a.fields.map(([f, x]) => [f, argJson(x, inputs)])) : null)
    const snapJson = (s: Snap): Record<string, unknown> => {
      const out: Record<string, unknown> = {}
      for (const [k, v] of Object.entries(s.leaves)) out[k] = typeof v === 'number' ? String(v) : v
      for (const [k, cells] of Object.entries(s.maps)) out[k] = Object.fromEntries(Object.entries(cells).map(([key, c]) => [key, Object.fromEntries(Object.entries(c).map(([f, x]) => [f, typeof x === 'number' ? String(x) : x]))]))
      for (const [k, xs] of Object.entries(s.lists ?? {})) out[k] = xs.map(x => (typeof x === 'number' ? String(x) : x))
      return out
    }
    const eps = plan.map(p => ({from: p.from ? snapJson(p.from) : null, steps: p.steps.map(s => ({m: s.e.call, a: s.e.args.map(a => argJson(a, s.inputs))}))}))
    fs.writeFileSync(`${work}/in.json`, JSON.stringify(eps))
    fs.mkdirSync(`${work}/cov`, {recursive: true})
    const r0 = performance.now()
    try {
      cp.execFileSync(`${work}/harness`, [`${work}/in.json`, `${work}/out.json`], {encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: {...goEnv(), GOCOVERDIR: `${work}/cov`}, maxBuffer: 1 << 26, timeout: 600_000})
    } catch (x) { return fail(`the harness failed: ${String((x as {stderr?: string}).stderr ?? (x as Error).message).slice(0, 400)}`) }
    ev.runMs = Math.round(performance.now() - r0)
    const results = JSON.parse(fs.readFileSync(`${work}/out.json`, 'utf8')) as {state?: Record<string, unknown>, out?: unknown, hasOut?: boolean, err?: string, panic?: string, bad?: string, frame?: string}[][]
    // --- compared, step by step
    const toSnap = (s: Record<string, unknown>): {snap?: Snap, outside?: string} => {
      const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}, lists: Record<string, Raw[]> = {}
      const num = (x: unknown, at: string): number | string => { const n = Number(x); return Number.isSafeInteger(n) && String(n) === String(x) ? n : `${at} is ${String(x)}` }
      for (const v of m.state) {
        if (m.outputs.includes(v.name)) continue
        const x = s[v.name]
        if (v.sort.k === 'num') { const n = num(x, v.name); if (typeof n === 'string') return {outside: n}; leaves[v.name] = n } else leaves[v.name] = x as Raw
      }
      for (const d of m.maps) {
        const cells: Snap['maps'][string] = {}
        for (const [k, c] of Object.entries((s[d.name] ?? {}) as Record<string, Record<string, unknown>>)) {
          const cell: Record<string, Raw> = {}
          for (const f of d.fields) { const x = c[f.name]; if (f.sort.k === 'num') { const n = num(x, `${d.name}[${k}].${f.name}`); if (typeof n === 'string') return {outside: n}; cell[f.name] = n } else cell[f.name] = x as Raw }
          cells[k] = cell
        }
        maps[d.name] = cells
      }
      for (const d of m.lists ?? []) {
        const xs: Raw[] = []
        for (const x of (s[d.name] ?? []) as unknown[]) { if (d.fields[0]!.sort.k === 'num') { const n = num(x, d.name); if (typeof n === 'string') return {outside: n}; xs.push(n) } else xs.push(x as Raw) }
        lists[d.name] = xs
      }
      return {snap: {leaves, maps, ...(m.lists?.length ? {lists} : {})}}
    }
    for (const [i, p] of plan.entries()) {
      const rs = results[i] ?? []
      if (p.from) ev.fromStates++; else ev.runs++
      // A drawn state Go can't hold (a value outside its type): no state of the code is that one.
      if (p.from && rs.length === 1 && rs[0]!.bad?.startsWith('state: ')) { ev.unmakeable++; continue }
      for (const [j, s] of p.steps.entries()) {
        const c = rs[j]
        ev.requests++
        if (!c) return fail(`${s.where}: the harness gave no result`)
        const req = `${s.e.call}(${s.e.args.map(a => JSON.stringify(argJson(a, s.inputs))).join(', ')})`, from = `from ${showSnap(s.before)}`
        if (c.bad) {
          if (s.o.k === 'refused') { ev.unmakeable++; continue }
          return fail(`${s.where}: ${req} ${from}: the code can't be given it (${c.bad}), the rule takes it`)
        }
        if (c.frame) return fail(`${s.where}: ${req} ${from}: the code changes ${c.frame}, a field the rule leaves out`)
        const failed = c.err !== undefined || c.panic !== undefined
        const got = c.state ? toSnap(c.state) : {outside: 'no state'}
        if (s.o.k === 'outside' || (s.o.k === 'refused' && s.o.edge)) {
          // Where the rule's numbers stop (2^53) or Go wraps past a type the rule refuses: counted apart.
          if (failed) { ev.refusedBoth++; continue }
          if (got.outside) { ev.outside++; continue }
          ev.edge++; ev.edgeSample ??= `${req} ${from}`
          continue
        }
        if (s.o.k === 'refused') {
          if (!failed) return fail(`${s.where}: ${req} ${from}: the rule refuses it (${s.o.why}), the code doesn't`)
          if (gopts.onError !== 'discard') {
            if (got.outside) return fail(`${s.where}: ${req} ${from}: the code fails (${c.err ?? c.panic}) and its state is outside the safe integers`)
            const d = sameSnap(got.snap!, s.before)
            if (d) return fail(`${s.where}: ${req} ${from}: the code fails (${c.err ?? c.panic}) after changing the object: ${d}`)
          }
          ev.refusedBoth++
          continue
        }
        if (failed) return fail(`${s.where}: ${req} ${from}: the code fails (${c.err ? `error: ${c.err}` : `panic: ${c.panic}`}), the rule takes the step`)
        if (got.outside) return fail(`${s.where}: ${req} ${from}: the code leaves the safe integers (${got.outside}) where the rule takes the step`)
        const diff = sameSnap(got.snap!, s.o.snap)
        if (diff) return fail(`${s.where}: ${req} ${from}: ${diff}`)
        const res = m.results?.[s.e.call] as {k: string, name: string} | undefined
        if (res) {
          const want = s.o.out, have = typeof c.out === 'string' && typeof want === 'number' ? Number(c.out) : c.out
          if (have !== want) return fail(`${s.where}: ${req} ${from}: ${s.e.call} returns ${JSON.stringify(c.out)}, the rule's ${res.name} is ${JSON.stringify(want)}`)
        }
      }
    }
    // The blocks of the code the step reads that the requests reached.
    try {
      cp.execFileSync('go', ['tool', 'covdata', 'textfmt', `-i=${work}/cov`, `-o=${work}/cov.txt`], {cwd: mod.root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: goEnv()})
      const blocks = new Map<string, {file: string, from: number, to: number, hit: boolean}>()
      for (const line of fs.readFileSync(`${work}/cov.txt`, 'utf8').split('\n').slice(1)) {
        const mm = /^(.*):(\d+)\.\d+,(\d+)\.\d+ \d+ (\d+)$/.exec(line)
        if (!mm) continue
        const file = mm[1]!.split('/').pop()!, from = Number(mm[2]), to = Number(mm[3]), n = Number(mm[4])
        if (!read.spans.some(([f, a, b]) => f === file && from >= a && to <= b)) continue
        const k = `${file}:${mm[2]}-${mm[3]}:${line.split(' ')[0]}`
        const prev = blocks.get(k)
        blocks.set(k, {file, from, to, hit: (prev?.hit ?? false) || n > 0})
      }
      ev.coverage = {arms: blocks.size, hit: [...blocks.values()].filter(b => b.hit).length, missed: [...blocks.values()].filter(b => !b.hit).map(b => `the block at ${b.file}:${b.from}-${b.to}`)}
    } catch { /* coverage is evidence, not the check */ }
  } finally {
    try { fs.rmSync(hfile) } catch { /* gone */ }
    try { fs.rmSync(mainDir, {recursive: true, force: true}) } catch { /* gone */ }
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
  ev.ms = Math.round(performance.now() - t0)
  return ev
}

// Each fixed-width number's range, by the rule's name (inputs, state, map fields, list items).
function rangesOf(m: Model, read: GoRead, pkg: GoPkg): Map<string, [number, number]> {
  const out = new Map<string, [number, number]>()
  const rg = (t: number): [number, number] | undefined => {
    const x = pkg.ttab[t]
    if (x?.k !== 'int') return undefined
    const bits = x.bits ?? 64
    if (bits >= 64) return x.signed === false ? [0, Number.MAX_SAFE_INTEGER] : [-Number.MAX_SAFE_INTEGER, Number.MAX_SAFE_INTEGER]
    return x.signed === false ? [0, 2 ** bits - 1] : [-(2 ** (bits - 1)), 2 ** (bits - 1) - 1]
  }
  for (const l of read.leaves) { const r = l.kind === 'int' ? rg(l.t) : undefined; if (r) out.set(l.name, r) }
  for (const meth of read.methods) for (const pa of meth.params) {
    if (pa.arg.k === 'input') { const r = rg(pa.t); if (r) out.set(pa.arg.name, r) }
    if (pa.arg.k === 'rec') {
      const st = pkg.ttab[pkg.ttab[pa.t]!.elem!]!
      for (const [f, a] of pa.arg.fields) { const ft = st.fields?.find(g => g.name === f)?.t; const r = ft !== undefined ? rg(ft) : undefined; if (r && a.k === 'input') out.set(a.name, r) }
    }
  }
  for (const d of m.maps) {
    const l = read.leaves.find(x => x.name === d.name && x.kind === 'map')
    if (!l) continue
    const mt = pkg.ttab[l.t]!, vt = pkg.ttab[mt.elem!]!
    for (const f of d.fields) { const r = rg(vt.k === 'struct' ? vt.fields!.find(g => g.name === f.name)!.t : mt.elem!); if (r) out.set(`${d.name}.${f.name}`, r) }
  }
  for (const d of m.lists ?? []) { const l = read.leaves.find(x => x.name === d.name && x.kind === 'list'); const r = l ? rg(pkg.ttab[l.t]!.elem!) : undefined; if (r) out.set(`${d.name}.$item`, r) }
  return out
}
// The refusals that are where the rule's numbers stop and Go's go on (a uint64 below 0, which Go wraps).
function edgeConditions(m: Model, read: GoRead): B[] { void m; return read.edges }

// A condition at a state and a request (the snapshot's leaves, map cells and list items; the request's inputs).
function evalB(c: B, s: Snap, inputs: Record<string, Raw>): boolean {
  const env = (n: string): Raw | undefined => (n in inputs ? inputs[n] : s.leaves[n] ?? (n.endsWith('_len') ? s.lists?.[n.slice(0, -4)]?.length : undefined))
  const key = (k: K): Raw => (k.op === 'num' ? n(k.e) : k.op === 'svar' ? env(k.name) as Raw : k.op === 'slit' ? k.value : b(k.c) ? key(k.a) : key(k.b))
  const cell = (map: string, k: K, field: string): Raw => {
    if (field === '$item') return s.lists?.[map]?.[Number(key(k))] ?? 0
    const c = s.maps[map]?.[String(key(k))]
    if (field === 'has') return !!c
    return c?.[field] ?? 0
  }
  function n(e: N): number {
    switch (e.op) {
      case 'var': return Number(env(e.name) ?? 0)
      case 'const': return e.v
      case 'add': return n(e.a) + n(e.b)
      case 'sub': return n(e.a) - n(e.b)
      case 'neg': return -n(e.a)
      case 'mulk': return e.k * n(e.a)
      case 'mul': return n(e.a) * n(e.b)
      case 'min': return Math.min(n(e.a), n(e.b))
      case 'max': return Math.max(n(e.a), n(e.b))
      case 'divk': return Math.floor(n(e.a) / e.k)
      case 'modk': return ((n(e.a) % e.k) + e.k) % e.k
      case 'ite': return b(e.c) ? n(e.a) : n(e.b)
      case 'cell': return Number(cell(e.map, e.key, e.field))
    }
  }
  function b(x: B): boolean {
    switch (x.op) {
      case 'const': return x.v
      case 'var': return env(x.name) === true
      case 'cmp': return x.rel === '<' ? n(x.a) < n(x.b) : x.rel === '<=' ? n(x.a) <= n(x.b) : n(x.a) === n(x.b)
      case 'and': return x.xs.every(b)
      case 'or': return x.xs.some(b)
      case 'not': return !b(x.x)
      case 'ite': return b(x.c) ? b(x.a) : b(x.b)
      case 'is': return (x.l.op === 'var' ? env(x.l.name) : x.l.op === 'lit' ? x.l.value : undefined) === x.value
      case 'leq': return false
      case 'keq': return key(x.a) === key(x.b)
      case 'cell': return cell(x.map, x.key, x.field) === true
    }
  }
  return b(c)
}
void I
