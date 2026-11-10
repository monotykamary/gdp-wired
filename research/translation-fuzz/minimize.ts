// Bounded law-AST shrinking. Source remains the generated owned program, never external executable input.
import {resolve} from 'node:path'
import {type Expr, generate, render} from './model.ts'
import {shrink} from './shrink.ts'
const [root, seedArg, indexArg, lawArg = '0', mode = 'replay'] = process.argv.slice(2)
if (!root || !seedArg || !indexArg) throw new Error('usage: minimize.ts API_ROOT SEED INDEX LAW_INDEX')
const c = generate(Number(seedArg), Number(indexArg))
let law: Expr = c.laws[Number(lawArg)]!, trials = 0
if (!law) throw new Error('unknown law index')
async function finding(candidate: Expr): Promise<boolean> {
  const p = Bun.spawn(['bun', resolve(import.meta.dir, 'worker.ts'), resolve(root!), seedArg!, indexArg!, mode === '--no-replay' ? 'disabled' : 'replay', 'source', JSON.stringify(candidate)], {cwd: resolve(root!), stdout: 'pipe', stderr: 'pipe', env: {...process.env, GDP_CYCLIC_LOG: '0'}})
  const timer = setTimeout(() => p.kill('SIGKILL'), 30000)
  const [code, stdout, stderr] = await Promise.all([p.exited, new Response(p.stdout).text(), new Response(p.stderr).text()]); clearTimeout(timer)
  if (code !== 0) throw new Error(`shrinking worker failed: ${code}: ${stderr}`)
  const row = stdout.split('\n').find(s => s.startsWith('FUZZ_CASE '))
  if (!row) throw new Error('shrinking worker omitted receipt')
  return JSON.parse(row.slice(10)).laws.some((l: {status: string}) => ['FINDING', 'BLOCKED_FINDING', 'MODEL_FINDING'].includes(l.status))
}
if (!await finding(law)) throw new Error('initial law is not a native-false kernel proof')
let improved = true
while (improved && trials < 64) {
  improved = false
  for (const smaller of shrink(law)) {
    if (++trials > 64) break
    if (await finding(smaller)) { law = smaller; improved = true; break }
  }
}
console.log('FUZZ_MINIMIZED ' + JSON.stringify({id: c.id, source: c.source, law: render(law, true), lawAST: law, trials, bounded: trials >= 64, sourceShrunk: false}))
