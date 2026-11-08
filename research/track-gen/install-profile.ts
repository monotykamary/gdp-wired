// Only wrap generation in a disposable remote snapshot; never edit kernel or row construction.
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs'
import {createHash} from 'node:crypto'
import ts from 'typescript'
if (process.env.TRACK_GEN_DISPOSABLE !== '1') throw new Error('disposable snapshot only')
const file = 'core/counts.ts', source = readFileSync(file, 'utf8')
if (source.includes('__generationMeasure')) throw new Error('already installed')
const ast = ts.createSourceFile(file, source, ts.ScriptTarget.Latest, true)
const fn = ast.statements.find((s): s is ts.FunctionDeclaration => ts.isFunctionDeclaration(s) && s.name?.text === 'candidates')
if (!fn?.body) throw new Error('missing candidates')
const labels: Record<string,string> = {states:'small-states',kinds:'map-bounds',rowLaws:'row-laws',cubes0:'cubes',cubes:'loosen-cubes',fields:'field-laws',prefixes:'scan-prefixes',out:'admission',carried:'carry-laws'}
const edits: {at:number,text:string}[] = []
function visit(node: ts.Node): void {
  if (ts.isVariableDeclaration(node) && ts.isIdentifier(node.name) && labels[node.name.text] && node.initializer) {
    edits.push({at:node.initializer.getStart(ast),text:`__generationMeasure('${labels[node.name.text]}',()=> (`},{at:node.initializer.end,text:'))'})
  }
  ts.forEachChild(node,visit)
}
visit(fn.body)
let output=source
for(const e of edits.sort((a,b)=>b.at-a.at))output=output.slice(0,e.at)+e.text+output.slice(e.at)
output="import {measure as __generationMeasure} from '../research/track-gen/meter.ts'\n"+output
const hash=(s:string)=>createHash('sha256').update(s).digest('hex')
mkdirSync('/tmp/track-gen-profile',{recursive:true});writeFileSync('/tmp/track-gen-profile/counts.ts',source);writeFileSync(file,output)
console.log(JSON.stringify({instrumented:file,before:hash(source),after:hash(output),edits:edits.length}))
