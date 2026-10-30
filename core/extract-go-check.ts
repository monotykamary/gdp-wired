// The Go front end's check (core/extract-go.ts): the rule an extraction prints is run beside the Go code it was read
// from, and any difference refuses the extraction. The code runs as it ships: its package built by the Go toolchain in
// its own module (its go.mod, its dependencies), with a generated harness beside it that makes the object, sets it to
// a state, calls the methods with the requests given, recovers panics, and prints every state as JSON; `go build
// -cover` counts the blocks the requests reached. The requests are core/extract-check.ts's (runs from the start, steps
// from drawn states, steps from the prover's counterexamples), drawn on the rule's side and sent to the code in one
// batch; the rule runs through its interpreter and its generated JavaScript, and every state, map cell, list, result
// and refusal is compared, and the fields the rule leaves out are asked to be unchanged.
import type {Rule} from './dsl.ts'
import type {Rand} from './machine.ts'
import type {Arg, Model} from './extract-read.ts'
import type {B} from './extract-ir.ts'
import type {Sorts} from './extract-print.ts'
import {type CodeSide, type Coverage, type Evidence, Outside, type Snap, constantsOf, draw, drive, evalTerm} from './extract-check.ts'
import {stubbed} from './extract-step.ts'
import {type GoOptions, type GoPkg, type GoRead, type TT, node} from './extract-go.ts'

export type GoLeaf = {name: string, path: string[], kind: 'int' | 'bool' | 'str' | 'big' | 'bignil' | 'map' | 'mapnil' | 'list' | 'frame', t: number, go: string}
export type GoCheckOptions = {runs?: number, depth?: number, states?: number, seed?: number, bound?: number, probes?: boolean, keep?: string}
export type GoEvidence = Evidence & {buildMs: number, runMs: number}
type Raw = number | boolean | string
type FS = {existsSync: (p: string) => boolean, mkdirSync: (p: string, o?: unknown) => void, readFileSync: (p: string, e: string) => string, writeFileSync: (p: string, s: string) => void, rmSync: (p: string, o?: unknown) => void, mkdtempSync: (p: string) => string,
  openSync: (p: string, f: string) => number, closeSync: (fd: number) => void, readSync: (fd: number, b: Uint8Array, o: number, n: number, at: null) => number, writeSync: (fd: number, s: string) => number}
type CP = {execFileSync: (f: string, a: string[], o: Record<string, unknown>) => string}

// --- the harness ------------------------------------------------------------------------------------------------------
// Go source beside the package: a state set from JSON and read back as JSON, leaf by leaf; each method called with its
// arguments made from JSON; a panic recovered; the left-out fields compared before and after.
function harness(pkg: GoPkg, read: GoRead, m: Model, discard: boolean): {code: string, imports: Set<string>} {
  const T = (t: number): TT => pkg.ttab[t] ?? {k: 'invalid'}
  const imports = new Set(['bufio', 'encoding/json', 'fmt', 'os', 'reflect', 'strconv', 'math/big'])
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
      if (pa.arg.k === 'lit' && pa.arg.value === 'context') { imports.add('context'); lines.push(`var a${i} context.Context = context.Background()`) } else if (pa.arg.k === 'input') {
        if (t.k === 'int') { lines.push(`var a${i} ${t.go}`); lines.push(intSet(`a${i}`, raw, pa.t).replace('return fmt.Errorf', 'return nil, fmt.Errorf')) }
        else if (t.k === 'ptr') lines.push(`a${i}, ok${i} := new(big.Int).SetString(gdpStr(${raw}), 10); if !ok${i} { return nil, fmt.Errorf("bad big") }`)
        else { lines.push(`var a${i} ${t.go}`); lines.push(`if err := json.Unmarshal(${raw}, &a${i}); err != nil { return nil, err }`) }
      } else if (pa.arg.k === 'rec') {
        // (a pointer to a struct the caller gives, or a struct given by value)
        const byValue = t.k !== 'ptr', st = byValue ? t : T(t.elem!)
        qual(byValue ? pa.t : t.elem!)
        lines.push(`a${i} := ${byValue ? '' : '&'}${st.go}{}`)
        lines.push(`var f${i} map[string]json.RawMessage; json.Unmarshal(${raw}, &f${i})`)
        for (const [f] of pa.arg.fields) {
          const ft = (st.fields ?? st.xfields)!.find(g => g.name === f)!.t, fx = T(ft)
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
${[...imports].sort().map(p => `\t${p.split('/')[0]!.includes('.') ? `${p.replace(/[^A-Za-z0-9]/g, '_').replace(/^/, 'gdp_')} ` : ''}${JSON.stringify(p)}`).join('\n')}
)

type gdpStep struct {
	M string            \`json:"m"\`
	A []json.RawMessage \`json:"a"\`
}
type gdpCmd struct {
	Op    string                     \`json:"op"\`
	ID    int                        \`json:"id"\`
	State map[string]json.RawMessage \`json:"state"\`
	M     string                     \`json:"m"\`
	A     []json.RawMessage          \`json:"a"\`
	Answers map[string]json.RawMessage \`json:"answers"\`
}
${read.answers?.length ? `
// The stub point of an answered call, by the callee's name (each call rewritten to it in the package's copy, the
// callee and its arguments still evaluated): the request's input for it, the zero value where it is none.
var gdpAnswers map[string]json.RawMessage

func gdpAnswer[T any](name string, _ ...any) T {
	var v T
	var a struct {
		In json.RawMessage \`json:"in"\`
	}
	if json.Unmarshal(gdpAnswers[name], &a) != nil || len(a.In) == 0 {
		return v
	}
	var s string
	if json.Unmarshal(a.In, &s) == nil {
		if p, ok := any(&v).(*string); ok {
			*p = s
		} else {
			json.Unmarshal([]byte(s), &v)
		}
		return v
	}
	json.Unmarshal(a.In, &v)
	return v
}
` : ''}
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

// GdpHarnessMain answers the requests read from the named pipe in, a JSON line each, on the named pipe out.
func GdpHarnessMain(in, out string) {
	inf, err := os.Open(in)
	if err != nil {
		panic(err)
	}
	outf, err := os.OpenFile(out, os.O_WRONLY, 0)
	if err != nil {
		panic(err)
	}
	rd, wr := bufio.NewReaderSize(inf, 1<<20), bufio.NewWriter(outf)
	objs := map[int]*${read.entry}{}
	for {
		line, err := rd.ReadBytes('\\n')
		if err != nil {
			break
		}
		var c gdpCmd
		var res any
		if err := json.Unmarshal(line, &c); err != nil {
			panic(err)
		}
		switch c.Op {
		case "new":
			objs[len(objs)+1] = new(${read.entry})
			res = map[string]any{"id": len(objs)}
		case "at":
			o := new(${read.entry})
			if err := gdpSet(o, c.State); err != nil {
				res = map[string]any{"bad": err.Error()}
			} else {
				objs[len(objs)+1] = o
				res = map[string]any{"id": len(objs)}
			}
		case "get":
			res = map[string]any{"state": gdpGet(objs[c.ID])}
		case "call":
			${read.answers?.length ? 'gdpAnswers = c.Answers\n\t\t\t' : ''}res = gdpRun(objs[c.ID], gdpStep{M: c.M, A: c.A})
		}
		b, _ := json.Marshal(res)
		wr.Write(b)
		wr.WriteByte('\\n')
		wr.Flush()
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
// core/extract-check.ts's `drive`, with the Go code's side: the harness built once and spoken to through two named
// pipes, a JSON line a request (make an object, set it to a state, read it, call a method on it).
export function checkGo(dir: string, pkg: GoPkg, read: GoRead, r: Rule, sorts: Sorts, gopts: GoOptions): GoEvidence {
  const opts = gopts.check ?? {}, m = read.model
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process'), os = node<{tmpdir: () => string}>('node:os')
  const mod = moduleOf(dir), work = fs.mkdtempSync(`${os.tmpdir()}/gdp-gocheck-`)
  const hfile = `${dir.replace(/\/$/, '')}/zz_gdp_harness_gen.go`, mainDir = `${mod.root}/gdpharness_${Date.now().toString(36)}`
  const {code} = harness(pkg, read, m, gopts.onError === 'discard')
  const importPath = mod.path, empty = {runs: 0, requests: 0, fromStates: 0, probes: {conditions: 0, witnesses: 0, steps: 0}, refusedBoth: 0, outside: 0, edge: 0, compiledAgreed: 0, coverage: {arms: 0, hit: 0, missed: []}, ms: 0, buildMs: 0, runMs: 0}
  const b0 = performance.now()
  try {
    fs.writeFileSync(hfile, code)
    fs.mkdirSync(mainDir, {recursive: true})
    fs.writeFileSync(`${mainDir}/main.go`, `package main\n\nimport (\n\t"os"\n\n\tpkg ${JSON.stringify(importPath)}\n)\n\nfunc main() { pkg.GdpHarnessMain(os.Args[1], os.Args[2]) }\n`)
    if (opts.keep) { fs.mkdirSync(opts.keep, {recursive: true}); fs.writeFileSync(`${opts.keep}/harness.go`, code) }
    // (each answered call rewritten to the harness's answer in a copy of its file, the build told by an overlay)
    const over: Record<string, string> = {}
    for (const [f, t] of stubbed(read as never, f => fs.readFileSync(`${dir}/${f}`, 'utf8'), (a, _i, t) => `gdpAnswer[${a.ty}](${JSON.stringify(a.key)}, ${t.slice(0, t.indexOf('('))}, ${t.slice(t.indexOf('(') + 1)}`)) { const o = node<{resolve: (...p: string[]) => string}>('node:path').resolve(dir, f); fs.writeFileSync(`${work}/${f}`, t); over[o] = over[node<{realpathSync: (p: string) => string}>('node:fs').realpathSync(o)] = `${work}/${f}` }
    if (Object.keys(over).length) fs.writeFileSync(`${work}/overlay.json`, JSON.stringify({Replace: over}))
    try {
      // The harness's own package in -coverpkg too: the counters are written only where main is instrumented.
      // (a rewritten copy isn't instrumented with -cover, which reads the files as they are: no arms counted then)
      cp.execFileSync('go', ['build', ...(fs.existsSync(`${work}/overlay.json`) ? [`-overlay=${work}/overlay.json`] : ['-cover', `-coverpkg=${importPath},${mod.module}/${mainDir.split('/').pop()}`]), '-o', `${work}/harness`, `./${mainDir.split('/').pop()}`], {cwd: mod.root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: goEnv(), maxBuffer: 1 << 26})
    } catch (x) {
      const err = String((x as {stderr?: string}).stderr ?? (x as Error).message)
      return {...empty, mismatch: `the package doesn't build with the check's harness: ${err.split('\n').filter(Boolean).slice(0, 6).join(' | ')}`}
    }
    const buildMs = Math.round(performance.now() - b0)
    fs.mkdirSync(`${work}/cov`, {recursive: true})
    // The blocks of the code the step reads that the requests reached (the harness's counters, written as it exits).
    const count = (): Coverage => {
      try {
        cp.execFileSync('go', ['tool', 'covdata', 'textfmt', `-i=${work}/cov`, `-o=${work}/cov.txt`], {cwd: mod.root, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'], env: goEnv()})
        const blocks = new Map<string, {file: string, from: number, to: number, hit: boolean}>()
        for (const l of fs.readFileSync(`${work}/cov.txt`, 'utf8').split('\n').slice(1)) {
          const mm = /^(.*):(\d+)\.\d+,(\d+)\.\d+ \d+ (\d+)$/.exec(l)
          if (!mm) continue
          const file = mm[1]!.split('/').pop()!, from = Number(mm[2]), to = Number(mm[3]), n = Number(mm[4])
          if (!read.spans.some(([f, a, b]) => f === file && from >= a && to <= b)) continue
          const k = `${file}:${mm[2]}-${mm[3]}:${l.split(' ')[0]}`
          blocks.set(k, {file, from, to, hit: (blocks.get(k)?.hit ?? false) || n > 0})
        }
        return {arms: blocks.size, hit: [...blocks.values()].filter(b => b.hit).length, missed: [...blocks.values()].filter(b => !b.hit).map(b => `the block at ${b.file}:${b.from}-${b.to}`)}
      } catch { return {arms: 0, hit: 0, missed: []} }
    }
    return {...speak(work, `${work}/harness`, {...goEnv(), GOCOVERDIR: `${work}/cov`}, pkg, read, r, sorts, opts, count), buildMs}
  } finally {
    try { fs.rmSync(hfile) } catch { /* gone */ }
    try { fs.rmSync(mainDir, {recursive: true, force: true}) } catch { /* gone */ }
    try { fs.rmSync(work, {recursive: true, force: true}) } catch { /* gone */ }
  }
}

// The code's side of core/extract-check.ts's `drive`, for a harness built in the code's language (Go's, C's): the
// harness spoken to through two named pipes in `work`, a JSON line a request (make an object, set it to a state, read
// it, call a method on it), every state compared; `count` reads the coverage after the harness exits.
export function speak(work: string, bin: string, env: Record<string, string | undefined> | undefined, pkg: GoPkg, read: GoRead, r: Rule, sorts: Sorts, opts: GoCheckOptions, count: () => Coverage): Evidence & {runMs: number} {
  const m = read.model, bound = opts.bound ?? 12
  const fs = node<FS>('node:fs'), cp = node<CP>('node:child_process')
  let child: {kill: () => void} | undefined, wi = -1, ro = -1
  try {
    cp.execFileSync('mkfifo', [`${work}/in`, `${work}/out`], {})
    child = node<{spawn: (f: string, a: string[], o: Record<string, unknown>) => {kill: () => void}}>('node:child_process').spawn(bin, [`${work}/in`, `${work}/out`], {stdio: 'ignore', env})
    wi = fs.openSync(`${work}/in`, 'w'); ro = fs.openSync(`${work}/out`, 'r')
    const buf = new Uint8Array(1 << 20), dec = new TextDecoder()
    let pend = ''
    const line = (): string | undefined => {
      for (;;) {
        const k = pend.indexOf('\n')
        if (k >= 0) { const l = pend.slice(0, k); pend = pend.slice(k + 1); return l }
        const n = fs.readSync(ro, buf, 0, buf.length, null)
        if (n === 0) return undefined
        pend += dec.decode(buf.subarray(0, n), {stream: true})
      }
    }
    const ask = (cmd: Record<string, unknown>): Record<string, unknown> => {
      fs.writeSync(wi, `${JSON.stringify(cmd)}\n`)
      const l = line()
      if (l === undefined) throw new Error('the harness stopped')
      return JSON.parse(l) as Record<string, unknown>
    }
    // A state from the harness as a snapshot (a number past the safe integers: the code leaves the rule's numbers).
    const toSnap = (s: Record<string, unknown>): Snap => {
      const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}, lists: Record<string, Raw[]> = {}
      const num = (x: unknown, at: string): number => { const n = Number(x); if (Number.isSafeInteger(n) && String(n) === String(x)) return n; throw new Outside(`${at} is ${String(x)}`) }
      for (const v of m.state) if (!m.outputs.includes(v.name)) leaves[v.name] = v.sort.k === 'num' ? num(s[v.name], v.name) : s[v.name] as Raw
      for (const d of m.maps) maps[d.name] = Object.fromEntries(Object.entries((s[d.name] ?? {}) as Record<string, Record<string, unknown>>).map(([k, c]) => [k, Object.fromEntries(d.fields.map(f => [f.name, f.sort.k === 'num' ? num(c[f.name], `${d.name}[${k}].${f.name}`) : c[f.name] as Raw]))]))
      for (const d of m.lists ?? []) lists[d.name] = ((s[d.name] ?? []) as unknown[]).map(x => (d.fields[0]!.sort.k === 'num' ? num(x, d.name) : x as Raw))
      return {leaves, maps, ...(m.lists?.length ? {lists} : {})}
    }
    const snapJson = (s: Snap): Record<string, unknown> => {
      const out: Record<string, unknown> = {}
      const j = (x: Raw) => (typeof x === 'number' ? String(x) : x)
      for (const [k, v] of Object.entries(s.leaves)) out[k] = j(v)
      for (const [k, cells] of Object.entries(s.maps)) out[k] = Object.fromEntries(Object.entries(cells).map(([key, c]) => [key, Object.fromEntries(Object.entries(c).map(([f, x]) => [f, j(x)]))]))
      for (const [k, xs] of Object.entries(s.lists ?? {})) out[k] = xs.map(j)
      return out
    }
    const ctorArgs = (params: Record<string, Raw>) => (read.ctor ? {a: read.ctor.map(pa => argJson(pa.arg, params))} : {})
    const argJson = (a: Arg, inputs: Record<string, Raw>): unknown => (a.k === 'input' ? (typeof inputs[a.name] === 'number' ? String(inputs[a.name]) : inputs[a.name]) : a.k === 'rec' ? Object.fromEntries(a.fields.map(([f, x]) => [f, argJson(x, inputs)])) : null)
    // A drawn number within its variable's type (a value of the type is all the code can hold); a quarter of them at
    // the type's own edges (where Go wraps).
    const ranges = rangesOf(m, read, pkg), consts = constantsOf(m), strs = ['a', 'b', 'c', '']
    // (a natural, by its type or as the caller states, drawn at 0 or above)
    const fit = (x: Raw, name: string, rand: Rand): Raw => { const y = fit0(x, name, rand); return typeof y === 'number' && y < 0 && sorts.get(name) === 'nat' ? Math.min(-y, ranges.get(name)?.[1] ?? -y) : y }
    const fit0 = (x: Raw, name: string, rand: Rand): Raw => {
      if (typeof x !== 'number') return x
      const rg = ranges.get(name)
      if (!rg) return x
      if (rand(4) === 0 && rg[1] < Number.MAX_SAFE_INTEGER) { const e = [rg[0], rg[0] + 1, rg[1] - 1, rg[1]]; return e[rand(4)]! }
      const [lo, hi] = rg
      if (x >= lo && x <= hi) return x
      if (Number.isFinite(hi) && Number.isFinite(lo)) return lo + (((x - lo) % (hi - lo + 1)) + (hi - lo + 1)) % (hi - lo + 1)
      return x < lo ? lo : x
    }
    // A nil *big.Int holds 0 (the rule's encoding of it).
    // (and a fixed array, C's, holds its length's items: a state made without them holds zeros)
    const normalize = (s: Snap): Snap => {
      for (const l of read.leaves) if (l.kind === 'big' && s.leaves[`${l.name}_nil`] === true) s.leaves[l.name] = 0
      for (const d of m.lists ?? []) if (d.len !== undefined) { const xs = s.lists?.[d.name] ?? []; s.lists = {...s.lists, [d.name]: Array.from({length: d.len}, (_, i) => xs[i] ?? (d.fields[0]!.sort.k === 'bool' ? false : 0))} }
      return s
    }
    let coverage: Coverage | undefined
    const r0 = performance.now()
    const side: CodeSide = {
      // (a constructor's arguments, C++'s: the rule's parameters)
      make: params => { const res = ask({op: 'new', ...ctorArgs(params)}); return res.bad ? {ok: false, error: `the code can't be made with it (${res.bad as string})`} : {ok: true, value: res.id} },
      at: (s, params) => { const res = ask({op: 'at', state: snapJson(s), ...ctorArgs(params)}); return res.bad ? undefined : res.id },
      snapOf: self => toSnap(ask({op: 'get', id: self}).state as Record<string, unknown>),
      call: (self, e, args) => {
        // (the answers' values: the event's last argument, each one within its type or the request is outside)
        let answers: Record<string, unknown> | undefined
        if (read.answers?.length) {
          const v = args.pop() as Record<string, Raw>
          answers = Object.fromEntries(read.answers.map(a => { const x = v[a.inputs.name] ?? 0; if (a.fit && a.range && (Number(x) < a.range[0] || Number(x) > a.range[1])) throw new Outside(`${a.key} answers ${String(x)}, outside its type`); return [a.key, a.inputs.none && v[a.inputs.none] === true ? {none: true} : {in: x}] }))
        }
        const res = ask({op: 'call', id: self, m: e.call, a: args, ...(answers ? {answers} : {})}) as {out?: unknown, hasOut?: boolean, err?: string, panic?: string, bad?: string, frame?: string}
        if (res.frame) throw new Error(`the code changes ${res.frame}, a field the rule leaves out`)
        if (res.bad) return {ok: false, error: `the code can't be given it (${res.bad})`}
        if (res.err !== undefined || res.panic !== undefined) return {ok: false, error: res.err !== undefined ? `error: ${res.err}` : `panic: ${res.panic}`}
        return {ok: true, value: typeof res.out === 'string' && /^-?\d+$/.test(res.out) && m.results?.[e.call] && m.state.find(v => v.name === (m.results![e.call] as {name: string}).name)?.sort.k === 'num' ? Number(res.out) : res.out}
      },
      args: (inputs, e) => e.args.map(a => argJson(a, inputs)),
      setNow: () => {},
      coverage: () => (coverage ??= closeAndCount()),
      input: (v, x, rand) => { const y = rand(8) === 0 ? x : fit(x, v.name, rand); return typeof y === 'number' && y < 0 && sorts.get(v.name) === 'nat' ? -y : y },
      drawSnap: rand => {
        const leaves: Record<string, Raw> = {}, maps: Snap['maps'] = {}, lists: Record<string, Raw[]> = {}
        for (const v of m.state) {
          if (m.outputs.includes(v.name)) continue
          let x = draw(v.sort, sorts, v.name, rand, consts, bound, strs)
          if (typeof x === 'number' && sorts.get(v.name) === 'nat' && x < 0) x = -x
          if (typeof x === 'number' && Math.abs(x) > Number.MAX_SAFE_INTEGER / 4) x = rand(bound)
          leaves[v.name] = fit(x, v.name, rand)
        }
        normalize({leaves, maps})
        for (const d of m.maps) {
          const cells: Snap['maps'][string] = {}
          if (leaves[`${d.name}_nil`] !== true) for (let i = rand(4); i > 0; i--) {
            const key = d.key === 'str' ? strs[rand(3)]! : String(rand(4))
            cells[key] = Object.fromEntries(d.fields.map(f => { let x = draw(f.sort, sorts, `${d.name}.${f.name}`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.${f.name}`) === 'nat') x = Math.abs(x); return [f.name, fit(x, `${d.name}.${f.name}`, rand)] }))
          }
          maps[d.name] = cells
        }
        for (const d of m.lists ?? []) { const f = d.fields[0]!; lists[d.name] = Array.from({length: d.len ?? rand(4)}, () => { let x = draw(f.sort, sorts, `${d.name}.$item`, rand, consts, bound, strs); if (typeof x === 'number' && sorts.get(`${d.name}.$item`) === 'nat') x = Math.abs(x); return fit(x, `${d.name}.$item`, rand) }) }
        return {leaves, maps, ...(m.lists?.length ? {lists} : {})}
      },
      normalize,
      edge: (s, raw) => read.edges.some(c => evalB(c, s, raw)),
    }
    // The harness told to stop: its counters written as it exits.
    function closeAndCount(): Coverage {
      fs.closeSync(wi); wi = -1
      while (line() !== undefined) { /* to its end */ }
      fs.closeSync(ro); ro = -1
      return count()
    }
    const ev = drive(m, r, sorts, side, opts)
    return {...ev, runMs: Math.round(performance.now() - r0)}
  } finally {
    if (wi >= 0) try { fs.closeSync(wi) } catch { /* closed */ }
    if (ro >= 0) try { fs.closeSync(ro) } catch { /* closed */ }
    try { child?.kill() } catch { /* gone */ }
  }
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
  for (const pa of read.ctor ?? []) { const r = rg(pa.t); if (r && pa.arg.k === 'input') out.set(pa.arg.name, r) }
  for (const meth of read.methods) for (const pa of meth.params) {
    if (pa.arg.k === 'input') { const r = rg(pa.t); if (r) out.set(pa.arg.name, r) }
    if (pa.arg.k === 'rec') {
      const pt = pkg.ttab[pa.t]!, st = pt.k === 'ptr' ? pkg.ttab[pt.elem!]! : pt
      for (const [f, a] of pa.arg.fields) { const ft = (st.fields ?? st.xfields)?.find(g => g.name === f)?.t; const r = ft !== undefined ? rg(ft) : undefined; if (r && a.k === 'input') out.set(a.name, r) }
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

// A condition at a state and a request: core/extract-check.ts's evaluator, the snapshot's cells and items beside it.
const evalB = (c: B, s: Snap, inputs: Record<string, Raw>): boolean => {
  const env: Record<string, Raw> = {...s.leaves, ...Object.fromEntries(Object.entries(s.lists ?? {}).map(([k, xs]) => [`${k}_len`, xs.length])), ...inputs}
  return evalTerm(c, env, (map, key, field) => (field === '$item' ? s.lists?.[map]?.[Number(key)] ?? 0 : field === 'has' ? !!s.maps[map]?.[String(key)] : s.maps[map]?.[String(key)]?.[field] ?? 0)) === true
}
