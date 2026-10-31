// Mutation testing for the trusted base (kernel.ts, core/check.ts): each mutant changes one operator, constant or
// quantifier at one place; the battery (fast tests first, the kernel fuzz last) must fail on it. A mutant that survives
// is a change nothing notices: a blind spot in the tests (or an equivalent mutant, which the report lets a reader judge).
//   bun mutants.ts list                 the mutants, numbered
//   bun mutants.ts run <from> <to>      runs the battery on mutants from..to-1 (in this checkout: run it in a container)
//   bun mutants.ts ids <a,b,...>        runs the battery on those mutants
//   bun mutants.ts baseline             the battery on the unmutated code, which must pass
//   bun mutants.ts equivalent           the mutants MUTANTS.md lists as equivalent, and its entries that match none
// supercomputer/mutants.json fans the run out on Modal, one container per batch.
import {readFileSync, writeFileSync} from 'node:fs'
import {resolve} from 'node:path'

const root = resolve(import.meta.dir, '..')
const targets = ['kernel/kernel.ts', 'core/check.ts']
// [pattern, replacement]: binary operators keep their spaces, so generics and arrows aren't touched.
const operators: [RegExp, string][] = [
  [/ <= /g, ' < '], [/ < /g, ' <= '], [/ >= /g, ' > '], [/ > /g, ' >= '],
  [/ === /g, ' !== '], [/ !== /g, ' === '], [/ && /g, ' || '], [/ \|\| /g, ' && '],
  [/\.every\(/g, '.some('], [/\.some\(/g, '.every('], [/\btrue\b/g, 'false'], [/\bfalse\b/g, 'true'],
  [/ \+ 1\b/g, ''], [/ - 1\b/g, ''], [/\bk\(1\)/g, 'k(0)'], [/\bk\(0\)/g, 'k(1)'], [/ > 0\b/g, ' >= 0'],
  [/Math\.ceil/g, 'Math.floor'], [/!\(/g, '('], [/\.\.\.pre, /g, ''], [/\.slice\(0, -1\)/g, ''],
]
type Mutant = {id: number, file: string, line: number, from: string, to: string, at: number, length: number}

export function mutants(): Mutant[] {
  const out: Mutant[] = []
  for (const file of targets) {
    const text = readFileSync(resolve(root, file), 'utf8')
    let offset = 0
    for (const [i, line] of text.split('\n').entries()) {
      const code = line.replace(/\/\/.*$/, '') // comments aren't code
      if (!code.trim().startsWith('import ')) for (const [pattern, to] of operators) {
        for (const m of code.matchAll(pattern)) out.push({id: out.length, file, line: i + 1, from: m[0], to, at: offset + m.index, length: m[0].length})
      }
      offset += line.length + 1
    }
  }
  return out
}

// The equivalent mutants, as MUTANTS.md lists them (its ```equivalent block): `file | function | snippet | from -> to |
// why`, one per line. A mutant is listed when its file is the entry's, the top-level declaration it sits in is the
// function, and its operator lies inside the snippet where the snippet occurs on its line; a run's row carries the why
// (`equivalent`), so a report can set it apart. Anchored by name and text, the list survives edits that move lines.
type Equivalent = {file: string, fn: string, snippet: string, from: string, to: string, why: string}
export function equivalents(): Equivalent[] {
  const block = /```equivalent\n([\s\S]*?)```/.exec(readFileSync(resolve(root, 'kernel/MUTANTS.md'), 'utf8'))?.[1] ?? ''
  return block.split('\n').filter(l => l.trim()).map(l => {
    const [file, fn, snippet, change, why] = l.split(' | ').map(x => x.trim()), [from, to] = change!.split(' -> ').map(x => JSON.parse(x) as string)
    return {file: file!, fn: fn!, snippet: JSON.parse(snippet!) as string, from: from!, to: to!, why: why!}
  })
}
const declared = /^(?:export )?(?:async )?(?:function|const|let|type) ([A-Za-z_$][\w$]*)/
export function equivalentOf(m: Mutant, list = equivalents()): Equivalent | undefined {
  const text = readFileSync(resolve(root, m.file), 'utf8'), lines = text.split('\n'), start = text.lastIndexOf('\n', m.at - 1) + 1, line = lines[m.line - 1]!
  let fn: string | undefined
  for (let i = m.line - 1; i >= 0 && !fn; i--) fn = declared.exec(lines[i]!)?.[1]
  return list.find(e => e.file === m.file && e.fn === fn && e.from === m.from && e.to === m.to && [...line.matchAll(new RegExp(e.snippet.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g'))]
    .some(x => x.index <= m.at - start && m.at - start + m.length <= x.index + e.snippet.length))
}

// Fast and pointed first; the kernel fuzz last. Each is a bun test (exit 0 = pass) with a time limit; a mutant that makes
// a test hang is caught too.
const battery: {name: string, cwd: string, cmd: string[], env?: Record<string, string>, ms: number}[] = [
  {name: 'counts', cwd: 'kernel', cmd: ['bun', 'test', 'count.test.ts'], ms: 120_000},
  {name: 'countmachine', cwd: 'kernel', cmd: ['bun', 'test', 'countmachine.test.ts'], ms: 180_000},
  {name: 'refusals', cwd: 'kernel', cmd: ['bun', 'test', 'refusals.test.ts'], ms: 60_000},
  {name: 'tamper', cwd: 'kernel', cmd: ['bun', 'test', 'tamper.test.ts'], ms: 120_000},
  {name: 'dsl', cwd: 'core', cmd: ['bun', 'test', 'dsl.test.ts'], ms: 120_000},
  {name: 'conformance', cwd: 'core', cmd: ['bun', 'test', 'conformance.test.ts'], env: {FUZZ_SEED: '1'}, ms: 180_000},
  {name: 'examples', cwd: 'examples', cmd: ['bun', 'test', 'examples.test.ts'], env: {DOMAIN: 'finance'}, ms: 180_000},
  {name: 'runtime', cwd: 'core', cmd: ['bun', 'test', 'runtime.test.ts'], ms: 180_000},
  {name: 'history', cwd: 'kernel', cmd: ['bun', 'test', 'history.test.ts'], ms: 240_000},
  {name: 'steplaw', cwd: 'kernel', cmd: ['bun', 'test', 'steplaw.test.ts'], ms: 240_000},
  {name: 'compose', cwd: 'core', cmd: ['bun', 'test', 'compose.test.ts'], ms: 120_000},
  {name: 'sets', cwd: 'kernel', cmd: ['bun', 'test', 'sets.test.ts'], ms: 240_000},
  {name: 'functions', cwd: 'core', cmd: ['bun', 'test', 'functions.test.ts'], ms: 120_000},
  {name: 'quantifiers', cwd: 'core', cmd: ['bun', 'test', 'quantifiers.test.ts'], ms: 180_000},
  {name: 'keyterms', cwd: 'core', cmd: ['bun', 'test', 'keyterms.test.ts'], ms: 120_000},
  {name: 'liveness', cwd: 'core', cmd: ['bun', 'test', 'liveness.test.ts'], ms: 120_000},
  {name: 'lists', cwd: 'core', cmd: ['bun', 'test', 'lists.test.ts'], ms: 300_000},
  {name: 'sums', cwd: 'core', cmd: ['bun', 'test', 'sums.test.ts'], ms: 120_000},
  {name: 'rationals', cwd: 'core', cmd: ['bun', 'test', 'rationals.test.ts'], ms: 120_000},
  {name: 'pairs', cwd: 'core', cmd: ['bun', 'test', 'pairs.test.ts'], ms: 120_000},
  {name: 'nonterm', cwd: 'core', cmd: ['bun', 'test', 'nonterm.test.ts'], ms: 300_000},
  {name: 'kernel fuzz', cwd: 'kernel', cmd: ['bun', 'test', 'kernel.test.ts'], env: {FUZZ_SCALE: '0.5'}, ms: 400_000},
]
// MUTANT_BATTERY=a,b: only those tests (by name), for a run over one check's mutants.
const only = process.env.MUTANT_BATTERY?.split(',')
function runBattery(): {killedBy?: string, ms: number} {
  const t0 = performance.now()
  for (const b of only ? battery.filter(x => only.includes(x.name)) : battery) {
    const p = Bun.spawnSync(b.cmd, {cwd: resolve(root, b.cwd), env: {...process.env, ...b.env}, timeout: b.ms, stdout: 'ignore', stderr: 'ignore'})
    if (p.exitCode !== 0) return {killedBy: p.exitCode === null ? `${b.name} (timeout)` : b.name, ms: Math.round(performance.now() - t0)}
  }
  return {ms: Math.round(performance.now() - t0)}
}

const [cmd, a, b] = process.argv.slice(2)
if (cmd === 'list') for (const m of mutants()) console.log(`${m.id}\t${m.file}:${m.line}\t${JSON.stringify(m.from)} -> ${JSON.stringify(m.to)}`)
else if (cmd === 'baseline') console.log(JSON.stringify({baseline: runBattery()}))
else if (cmd === 'ids') {
  const all = mutants(), ids = new Set((a ?? '').split(',').map(Number))
  for (const m of all.filter(mm => ids.has(mm.id))) {
    const path = resolve(root, m.file), original = readFileSync(path, 'utf8'), eq = equivalentOf(m)
    writeFileSync(path, original.slice(0, m.at) + m.to + original.slice(m.at + m.length))
    try { console.log(JSON.stringify({...m, ...runBattery(), ...(eq ? {equivalent: eq.why} : {})})) } finally { writeFileSync(path, original) }
  }
} else if (cmd === 'run') {
  const all = mutants(), from = Number(a), to = Math.min(Number(b), all.length)
  for (const m of all.slice(from, to)) {
    const path = resolve(root, m.file), original = readFileSync(path, 'utf8'), eq = equivalentOf(m)
    writeFileSync(path, original.slice(0, m.at) + m.to + original.slice(m.at + m.length))
    try { console.log(JSON.stringify({...m, ...runBattery(), ...(eq ? {equivalent: eq.why} : {})})) } finally { writeFileSync(path, original) }
  }
} else if (cmd === 'equivalent') {
  const list = equivalents(), hit = new Set<Equivalent>()
  for (const m of mutants()) { const e = equivalentOf(m, list); if (e) { hit.add(e); console.log(`${m.id}\t${m.file}:${m.line}\t${JSON.stringify(m.from)} -> ${JSON.stringify(m.to)}\t${e.why}`) } }
  for (const e of list.filter(x => !hit.has(x))) console.log(`unmatched: ${e.file} | ${e.fn} | ${JSON.stringify(e.snippet)}`)
} else console.log('usage: bun mutants.ts list | run <from> <to> | ids <a,b,...> | baseline | equivalent')
