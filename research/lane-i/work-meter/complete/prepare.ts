import {strict as assert} from 'node:assert'
import {copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync} from 'node:fs'
import {join} from 'node:path'
const out = 'complete-prepared-input'
mkdirSync(out)
for (const name of readdirSync('generator-input')) if (name.endsWith('.ts') || name.endsWith('.source') || name === 'baseline.pack') copyFileSync(join('generator-input', name), join(out, name))
for (const name of readdirSync('complete-input')) if (name.endsWith('.ts') || ['identity.json', 'candidate.patch'].includes(name)) copyFileSync(join('complete-input', name), join(out, name))
let text = readFileSync(join(out, 'preflight.ts'), 'utf8')
const replace = (old: string, value: string) => { assert.equal(text.split(old).length, 2, 'unique preflight anchor'); text = text.replace(old, value) }
replace("input=resolve('generator-input')", "input=resolve('complete-prepared-input')")
replace("if(mode==='checks'){", "if(mode==='checks' && process.env.COMPLETE_PREPARE==='1'){ const tooling=join(dest,'research/lane-i/generator');mkdirSync(tooling,{recursive:true});for(const name of readdirSync(input).filter(n=>n.endsWith('.ts')))copyFileSync(join(input,name),join(tooling,name));const result=await run(['research/lane-i/generator/instrument-ast.ts'],'constructors',600);const{stdout,traceGzipBase64,...receipt}=result;emit('CONSTRUCTOR_PREPARE_RECEIPT',receipt);process.stdout.write(stdout);if(result.exit!==0){const{gunzipSync}=await import('node:zlib');process.stderr.write(gunzipSync(Buffer.from(result.traceGzipBase64,'base64')))}assert.equal(result.exit,0,'constructor preparation');process.exit(0) }\n if(mode==='checks'){")
writeFileSync(join(out, 'preflight.ts'), text)
