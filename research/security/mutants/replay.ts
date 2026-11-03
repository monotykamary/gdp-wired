import ts from 'typescript'
import {readFileSync} from 'node:fs'
import {pathToFileURL} from 'node:url'
import {parse} from '../../../core/laws.ts'

type Expr = ReturnType<typeof parse>
type Scope = Record<string, unknown>
export type Call = {method: string, args: Scope}
export type Replay = {ok: boolean, broken: boolean, steps: unknown[], why?: string}

// Two real objects: A receives every call, B receives only the selected owner's calls.
// Compare observations after each call by that owner, not merely the final maps.
export async function replayIsolation(file: string, entry: string, expr: string, lines: string[], owner: unknown): Promise<Replay> {
  try {
    const policy = /^isolated by ([A-Za-z_]\w*) seeing result$/.exec(expr)
    if (!policy || !['string', 'number'].includes(typeof owner) || !/^B is \d+ \(run b takes only B's calls\)$/.test(lines[0] ?? '')) throw new Error('unsupported isolation witness or missing concrete owner')
    const requests = lines.slice(1)
    const selected = requests.filter(line => parseCall(line).args[policy[1]!] === owner)
    const a = await replayClass(file, entry, 'true', requests)
    const b = await replayClass(file, entry, 'true', selected)
    if (!a.ok || !b.ok) return {ok: false, broken: false, steps: [], why: a.why ?? b.why}
    type Step = {call: Call, before: Scope, after: Scope}
    const observationsA = (a.steps as Step[]).filter(s => s.call.args[policy[1]!] === owner)
    const observationsB = b.steps as Step[]
    if (observationsA.length !== observationsB.length) throw new Error('owner projections do not align')
    const observed = (value: unknown): unknown => {
      if (typeof value === 'number' && !Number.isSafeInteger(value)) throw new Error('unsafe numeric observation')
      if (value !== undefined && value !== null && !['number', 'string', 'boolean'].includes(typeof value)) throw new Error('non-scalar observation outside replay subset')
      return value
    }
    const broken = observationsA.some((step, i) => observed(step.after.result) !== observed(observationsB[i]!.after.result))
    return {ok: true, broken, steps: [{owner, all: a.steps, onlyOwner: b.steps}]}
  } catch (e) { return {ok: false, broken: false, steps: [], why: e instanceof Error ? e.message : String(e)} }
}
const boolean = (x: unknown): boolean => { if (typeof x !== 'boolean') throw new Error('policy expected a boolean'); return x }
const number = (x: unknown): number => { if (typeof x !== 'number' || !Number.isSafeInteger(x)) throw new Error('policy expected a safe integer'); return x }

// A deliberately small, independent concrete interpreter, not a proof-model evaluator.
// Unsupported syntax is a replay refusal, never evidence of a kill or of safety.
export function holds(expr: string, before: Scope, after: Scope): boolean {
  const value = (x: Expr, scope: Scope, bound: Scope = {}): unknown => {
    switch (x.k) {
      case 'num': case 'bool': return x.v
      case 'str': if (x.holes?.length) throw new Error('template policy outside replay subset'); return x.v
      case 'null': return null
      case 'path': {
        let v: unknown
        if (Object.hasOwn(bound, x.head)) v = bound[x.head]
        else if (Object.hasOwn(scope, x.head)) v = scope[x.head]
        else throw new Error(`unknown policy name ${x.head}`)
        for (const s of x.segs) {
          if ('call' in s) throw new Error('policy calls outside replay subset')
          const key = 'f' in s ? s.f : value(s.i, scope, bound)
          if (v instanceof Map) {
            if (!v.has(key)) throw new Error('policy read of absent map cell')
            const cell: unknown = v.get(key)
            v = cell !== null && typeof cell === 'object' ? cell : {value: cell}
          } else {
            if (v === null || typeof v !== 'object' || typeof key !== 'string' || !Object.hasOwn(v, key)) throw new Error('unknown policy field')
            v = (v as Scope)[key]
          }
        }
        return v
      }
      case 'old': return value(x.x, before, bound)
      case 'un': return x.op === 'not' ? !boolean(value(x.x, scope, bound)) : number(-number(value(x.x, scope, bound)))
      case 'forall': {
        const map = value(x.over, scope, bound)
        if (!(map instanceof Map)) throw new Error('forall replay requires a map')
        return [...map.keys()].every(k => boolean(value(x.body, scope, {...bound, [x.v]: k})))
      }
      case 'bin': {
        const a = value(x.a, scope, bound)
        if (x.op === '&&') return boolean(a) && boolean(value(x.b, scope, bound))
        if (x.op === '||') return boolean(a) || boolean(value(x.b, scope, bound))
        if (x.op === '=>') return !boolean(a) || boolean(value(x.b, scope, bound))
        const b = value(x.b, scope, bound)
        switch (x.op) {
          case '==': return a === b
          case '!=': return a !== b
          case '<': return number(a) < number(b)
          case '<=': return number(a) <= number(b)
          case '>': return number(a) > number(b)
          case '>=': return number(a) >= number(b)
          case '+': return number(number(a) + number(b))
          case '-': return number(number(a) - number(b))
          case 'in': if (!(b instanceof Map)) throw new Error('membership replay requires a map'); return b.has(a)
          default: throw new Error(`operator outside replay subset: ${x.op}`)
        }
      }
      case 'fn': case 'dur': case 'bdur': throw new Error('policy outside replay subset')
    }
  }
  return boolean(value(parse(expr), after))
}

const literal = (n: ts.Expression): unknown => {
  if (ts.isStringLiteral(n)) return n.text
  if (ts.isNumericLiteral(n)) return number(Number(n.text))
  if (n.kind === ts.SyntaxKind.TrueKeyword) return true
  if (n.kind === ts.SyntaxKind.FalseKeyword) return false
  if (ts.isPrefixUnaryExpression(n) && n.operator === ts.SyntaxKind.MinusToken) return number(-number(literal(n.operand)))
  throw new Error('trace argument is not a supported literal')
}
export function parseCall(line: string): Call {
  const text = line.startsWith('made with ') ? `constructor(${line.slice(10)})` : line
  const sf = ts.createSourceFile('trace.ts', text, ts.ScriptTarget.Latest, true)
  if ((sf as unknown as {parseDiagnostics: unknown[]}).parseDiagnostics.length) throw new Error('malformed trace call')
  const stmt = sf.statements[0]
  if (sf.statements.length !== 1 || !stmt || !ts.isExpressionStatement(stmt) || !ts.isCallExpression(stmt.expression) || !ts.isIdentifier(stmt.expression.expression)) throw new Error('unsupported trace call')
  const call = stmt.expression, args: Scope = {}
  for (const arg of call.arguments) {
    if (!ts.isBinaryExpression(arg) || arg.operatorToken.kind !== ts.SyntaxKind.EqualsToken || !ts.isIdentifier(arg.left) || Object.hasOwn(args, arg.left.text)) throw new Error('unsupported named trace argument')
    args[arg.left.text] = literal(arg.right)
  }
  return {method: (call.expression as ts.Identifier).text, args}
}

// Import the original bytes, construct the real class and invoke its real methods. No generated
// transition function executes here. The same witness is also replayed against its clean parent.
export async function replayClass(file: string, entry: string, expr: string, lines: string[], scopeLine?: number): Promise<Replay> {
  const steps: unknown[] = []
  try {
    if (!lines.length || lines.length > 128) throw new Error('missing or oversized concrete run')
    const sf = ts.createSourceFile(file, readFileSync(file, 'utf8'), ts.ScriptTarget.Latest, true)
    const cls = sf.statements.find((n): n is ts.ClassDeclaration => ts.isClassDeclaration(n) && n.name?.text === entry)
    if (!cls) throw new Error('replay requires the named source class')
    const parameters = (ps: ts.NodeArray<ts.ParameterDeclaration>, args: Scope): unknown[] => {
      const names = ps.map(p => { if (!ts.isIdentifier(p.name)) throw new Error('destructuring outside replay subset'); return p.name.text })
      if (names.length !== Object.keys(args).length || names.some(n => !Object.hasOwn(args, n))) throw new Error('trace arguments do not match source signature')
      return names.map(n => args[n])
    }
    const calls = lines.map(parseCall), made = calls[0]?.method === 'constructor' ? calls.shift()!.args : {}
    if (scopeLine !== undefined) {
      if (!Number.isInteger(scopeLine) || scopeLine < 1) throw new Error('missing step-law scope')
      const at = sf.getPositionOfLineAndCharacter(scopeLine - 1, 0)
      const scoped = cls.members.find((n): n is ts.MethodDeclaration => ts.isMethodDeclaration(n) && n.getFullStart() <= at && n.end > at)
      if (!scoped || !ts.isIdentifier(scoped.name) || scoped.name.text !== calls.at(-1)?.method) throw new Error('final call is outside the stated step-law scope')
    }
    const ctor = cls.members.find(ts.isConstructorDeclaration)
    const args = ctor ? parameters(ctor.parameters, made) : []
    if (!ctor && Object.keys(made).length) throw new Error('unexpected constructor inputs')
    const exports: Record<string, unknown> = await import(pathToFileURL(file).href)
    const C = exports[entry] as new (...args: unknown[]) => Scope
    const self = new C(...args)
    let broken = false
    for (const [i, call] of calls.entries()) {
      const method = cls.members.find((n): n is ts.MethodDeclaration => ts.isMethodDeclaration(n) && ts.isIdentifier(n.name) && n.name.text === call.method)
      if (!method) throw new Error(`no source method ${call.method}`)
      const before = structuredClone({...made, ...call.args, ...self})
      const fn = self[call.method]
      if (typeof fn !== 'function') throw new Error('source method is not callable')
      const result: unknown = Reflect.apply(fn, self, parameters(method.parameters, call.args))
      if (result instanceof Promise) throw new Error('async method needs isolation replay')
      const after = structuredClone({...made, ...call.args, ...self, result})
      // The prover's final call is the breaking step. Earlier calls construct its reachable state.
      if (i === calls.length - 1) broken = !holds(expr, before, after)
      steps.push({call, before, after})
    }
    if (!calls.length) throw new Error('run has no calls')
    return {ok: true, broken, steps}
  } catch (e) { return {ok: false, broken: false, steps, why: e instanceof Error ? e.message : String(e)} }
}
