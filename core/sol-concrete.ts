// Untrusted Solidity entry preparation. Compile original sources plus, only when needed, a new concrete entry.
// Never remove `abstract`, change an inherited body, or synthesize an implementation of an abstract function.
import type {Compiled, SolOptions} from './extract-sol.ts'
import {Refusal} from './extract-read.ts'
import {node} from './extract-step.ts'

type Ast = Compiled['ast'] extends Map<number, infer A> ? A : never
type Compiler = (file: string, options: SolOptions, extra?: Record<string, string>) => Compiled
type FS = {readFileSync(p: string, encoding: string): string, existsSync(p: string): boolean, readdirSync(p: string, options: {withFileTypes: true}): {name: string, isDirectory(): boolean, isFile(): boolean}[]}
type Path = {resolve(...p: string[]): string, dirname(p: string): string, relative(a: string, b: string): string, basename(p: string): string}
export type SolidityHarness = {
  kind: 'repository' | 'constructor' | 'library'
  target: {source: string, contract: string}
  source: string, entry: string
  constructors: string[], overrides: string[], addedMethods: string[], notes: string[]
  // An extra source unit, not a replacement for any original source. Undefined for repository harnesses.
  generatedSource?: string
}
export class SolidityHarnessRefusal extends Refusal {
  constructor(cause: Refusal, readonly harness: SolidityHarness) { super(cause.where, cause.what) }
}
const contracts = (c: Compiled): Ast[] => [...c.ast.values()].flatMap(a => (a.nodes as Ast[]).filter(n => n.nodeType === 'ContractDefinition'))
const source = (c: Compiled, n: Ast): string => c.paths.get(Number(n.src.split(':')[2]))!
const text = (c: Compiled, n: Ast): string => { const [at, size, id] = n.src.split(':').map(Number); return new TextDecoder().decode(new TextEncoder().encode(c.text.get(id!)!).slice(at, at! + size!)) }
const ctor = (n: Ast): Ast | undefined => (n.nodes as Ast[]).find(n => n.nodeType === 'FunctionDefinition' && n.kind === 'constructor')
const signature = (f: Ast): string => `${f.name}(${(f.parameters.parameters as Ast[]).map(p => p.typeDescriptions.typeString).join(',')})`
const chain = (c: Compiled, n: Ast): Ast[] => { const ds = contracts(c); return (n.linearizedBaseContracts as number[]).map(id => ds.find(d => d.id === id)!) }
function mentions(n: unknown, id: number): boolean {
  if (Array.isArray(n)) return n.some(v => mentions(v, id))
  if (!n || typeof n !== 'object') return false
  const a = n as Ast
  return a.referencedDeclaration === id || Object.values(a).some(v => v && typeof v === 'object' && mentions(v, id))
}
function matches(c: Compiled, candidate: Ast, targetSource: string, targetName: string, library: boolean): boolean {
  const target = contracts(c).find(n => source(c, n) === targetSource && n.name === targetName)
  if (!target) return false
  const bases = chain(c, candidate)
  return library ? bases.some(n => mentions(n.nodes, target.id)) : bases.some(n => n.id === target.id)
}
function describe(c: Compiled, entry: Ast, targetSource: string, targetName: string, kind: SolidityHarness['kind'], generatedSource?: string): SolidityHarness {
  const bases = chain(c, entry), inherited = new Set<string>(), overrides: string[] = [], addedMethods: string[] = []
  for (const b of [...bases].reverse()) for (const f of b.nodes as Ast[]) {
    if (f.nodeType !== 'FunctionDefinition' || f.kind !== 'function') continue
    const s = signature(f)
    if (inherited.has(s) && f.body) overrides.push(`${b.name}.${s} (${source(c, b)})`)
    if (b.id === entry.id && f.body && ['public', 'external'].includes(f.visibility) && !inherited.has(s)) addedMethods.push(s)
    inherited.add(s)
  }
  const constructors = bases.flatMap(b => { const f = ctor(b); return f ? [`${b.name}: ${text(c, f)}`] : [] })
  const h: SolidityHarness = {kind, target: {source: targetSource, contract: targetName}, source: source(c, entry), entry: entry.name,
    constructors, overrides, addedMethods, ...(generatedSource === undefined ? {} : {generatedSource}), notes: []}
  h.notes = [
    `Solidity concrete harness (${kind}): ${h.source}:${h.entry} for ${targetSource}:${targetName}; the original source units and function bodies are unchanged`,
    'harness scope: laws and replay concern this concrete deployment, not every possible subclass or caller of the abstract contract or library',
    'harness constructor arguments are rule parameters, subject to the original constructor guards; constructors execute as written (listed in extraction.harness.constructors)',
    `harness overrides: ${overrides.length ? overrides.join('; ') : 'none'}; additional public entry points: ${addedMethods.length ? addedMethods.join('; ') : 'none'}`,
    ...(kind === 'constructor' ? ['synthetic subclass: only a constructor forwarding the missing base-constructor arguments; no function implementation or override is invented'] : []),
    ...(kind === 'library' ? ['synthetic library caller: only forwarding functions for internal library functions; no storage context, linked library, or external-call behavior is invented'] : []),
  ]
  return h
}

// The ordinary concrete-contract path is unchanged. An explicit harness can also bind a concrete base.
export function concreteSolidity(file: string, o: SolOptions, original: Compiled, compile: Compiler): Compiled {
  if (original.harness || o.harness === false) return original
  const mode = o.harness
  if (mode !== undefined && mode !== 'auto' && (!mode || typeof mode !== 'object' || typeof mode.file !== 'string' || !mode.file || (mode.entry !== undefined && (typeof mode.entry !== 'string' || !mode.entry)))) {
    throw new Refusal(file, 'harness must be auto, false, or {file, entry?}')
  }
  const all = contracts(original), own = all.filter(n => source(original, n) === original.paths.get(original.main))
  const wanted = typeof o.entry === 'string' ? all.filter(n => n.name === o.entry) : own
  if (wanted.length !== 1) return original // The normal reader diagnoses ambiguous/missing entries.
  const target = wanted[0]!, explicit = typeof o.harness === 'object' ? o.harness : undefined
  if (!explicit && target.contractKind === 'contract' && !target.abstract) return original
  if (target.contractKind === 'interface') throw new Refusal(file, `${target.name}: an interface has no inherited implementation to make concrete`)
  const fs = node<FS>('node:fs'), path = node<Path>('node:path'), root = path.resolve(o.root ?? path.dirname(file))
  const targetSource = source(original, target), library = target.contractKind === 'library'
  const adopt = (c: Compiled, entry: Ast, kind: SolidityHarness['kind'], generatedSource?: string): Compiled => {
    const h = describe(c, entry, targetSource, target.name, kind, generatedSource)
    return {...c, harness: h}
  }
  const usable = (c: Compiled): Ast[] => contracts(c).filter(n => n.contractKind === 'contract' && !n.abstract && matches(c, n, targetSource, target.name, library))
  if (explicit) {
    const p = path.resolve(root, explicit.file), c = compile(p, {...o, root}), candidates = usable(c).filter(n => !explicit.entry || n.name === explicit.entry)
    if (candidates.length !== 1) throw new Refusal(file, `harness ${explicit.file}${explicit.entry ? `:${explicit.entry}` : ''}: expected one concrete ${library ? 'caller of' : 'subclass of'} ${target.name}, found ${candidates.length}`)
    return adopt(c, candidates[0]!, 'repository')
  }
  // Search source, not a hand-maintained project/name allowlist. solc, not text matching, establishes inheritance.
  const files: string[] = [], escaped = target.name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), token = new RegExp(`\\b${escaped}\\b`)
  let count = 0
  const walk = (dir: string) => {
    for (const d of fs.readdirSync(dir, {withFileTypes: true}).sort((a, b) => a.name.localeCompare(b.name))) {
      if (d.name.startsWith('.') || ['node_modules', 'vendor', 'out', 'cache', 'artifacts', 'runs'].includes(d.name)) continue
      const p = path.resolve(dir, d.name)
      if (d.isDirectory()) walk(p)
      else if (d.isFile() && d.name.endsWith('.sol')) {
        if (++count > 4096) throw new Refusal(file, 'harness search exceeds 4096 Solidity sources; state harness: {file, entry}')
        if (p !== path.resolve(file) && token.test(fs.readFileSync(p, 'utf8'))) files.push(p)
      }
    }
  }
  walk(root)
  if (files.length > 64) throw new Refusal(file, `${target.name}: more than 64 possible harness sources; state harness: {file, entry}`)
  const found: {c: Compiled, entry: Ast}[] = []
  for (const p of files) {
    let c: Compiled
    try { c = compile(p, {...o, root}) } catch (e) { if (e instanceof Refusal) continue; throw e }
    for (const entry of usable(c)) if (source(c, entry) === c.paths.get(c.main)) found.push({c, entry})
  }
  const preferred = found.filter(({entry}) => entry.name === `${target.name}Mock` || entry.name === `${target.name}Harness` || entry.name === `${target.name}Test`)
  const candidates = preferred.length ? preferred : found
  if (candidates.length === 1) return adopt(candidates[0]!.c, candidates[0]!.entry, 'repository')
  if (candidates.length > 1) throw new Refusal(file, `${target.name}: several concrete repository harnesses (${candidates.map(({c, entry}) => `${source(c, entry)}:${entry.name}`).join(', ')}); state harness: {file, entry}`)

  // New source unit only. Names cannot collide with source units or contracts already in the compilation.
  let entry = `GDPConcrete_${target.name}`, unit = '__gdp_concrete.sol'
  while (all.some(n => n.name === entry)) entry += '_'
  while ([...original.paths.values()].includes(unit) || fs.existsSync(path.resolve(root, unit))) unit = `_${unit}`
  const imports = new Set([targetSource]), params: string[] = [], forwards: string[] = []
  let body: string, methods: string[] | undefined
  const param = (p: Ast, i: number): string => {
    if (p.storageLocation === 'storage') throw new Refusal(file, `${target.name}: a library storage parameter needs an explicit caller/storage harness`)
    return `${text(original, p.typeName)}${p.storageLocation && p.storageLocation !== 'default' ? ` ${p.storageLocation}` : ''} __gdp_arg${i}`
  }
  if (library) {
    const fns = (target.nodes as Ast[]).filter(n => n.nodeType === 'FunctionDefinition' && n.kind === 'function' && n.visibility !== 'private' && (!o.methods || o.methods.includes(n.name)))
    if (!fns.length) throw new Refusal(file, `${target.name}: no library function selected for a concrete caller`)
    for (const f of fns) if (f.visibility !== 'internal') throw new Refusal(file, `${target.name}.${f.name}: a public/external library call needs a deployed, linked library harness`)
    body = fns.map(f => {
      const ps = f.parameters.parameters as Ast[], rs = f.returnParameters.parameters as Ast[]
      const ret = rs.length ? ` returns (${rs.map((p, i) => param(p, i).replace(/ __gdp_arg\d+$/, '')).join(', ')})` : ''
      return `function ${f.name}(${ps.map(param).join(', ')}) external ${['view', 'pure'].includes(f.stateMutability) ? f.stateMutability : ''}${ret} { ${rs.length ? 'return ' : ''}${target.name}.${f.name}(${ps.map((_, i) => `__gdp_arg${i}`).join(', ')}); }`
    }).join('\n')
    methods = fns.map(f => f.name)
  } else {
    const bases = chain(original, target), bound = new Set<number>()
    for (const b of bases) {
      for (const s of b.baseContracts as Ast[]) if (s.arguments !== null && s.arguments !== undefined) bound.add(s.baseName.referencedDeclaration)
      for (const m of (ctor(b)?.modifiers ?? []) as Ast[]) if (bases.some(b => b.id === m.modifierName.referencedDeclaration)) bound.add(m.modifierName.referencedDeclaration)
    }
    const seen = new Set<string>(), missing: string[] = []
    for (const b of bases) for (const f of b.nodes as Ast[]) {
      if (f.nodeType !== 'FunctionDefinition' || f.kind === 'constructor') continue
      const sig = signature(f)
      if (!seen.has(sig) && !f.body) missing.push(sig)
      seen.add(sig)
    }
    if (missing.length && target.fullyImplemented !== true) throw new Refusal(file, `${target.name}: abstract functions remain (${missing.join(', ')}); a constructor-only harness cannot invent their bodies (state a repository harness)`)
    for (const b of bases) {
      const f = ctor(b), ps = (f?.parameters.parameters ?? []) as Ast[]
      if (!ps.length || bound.has(b.id)) continue
      imports.add(source(original, b))
      const names = ps.map(p => { const i = params.length; params.push(param(p, i)); return `__gdp_arg${i}` })
      forwards.push(`${b.name}(${names.join(', ')})`)
    }
    const payable = ctor(target)?.stateMutability === 'payable' ? ' payable' : ''
    body = `constructor(${params.join(', ')})${payable} ${forwards.join(' ')} {}`
  }
  const generated = `// Generated concrete entry; every original source unit is unchanged.\n${[...imports].map(p => `import ${JSON.stringify(p)};`).join('\n')}\ncontract ${entry}${library ? '' : ` is ${target.name}`} {\n${body}\n}\n`
  const c = compile(file, {...o, root}, {[unit]: generated}), selected = contracts(c).find(n => n.name === entry && source(c, n) === unit)
  if (!selected || selected.abstract) throw new Refusal(file, `${target.name}: the constructor-only harness is not concrete`)
  const out = adopt({...c, main: Number(selected.src.split(':')[2])}, selected, library ? 'library' : 'constructor', generated)
  return {...out, harnessMethods: methods}
}
