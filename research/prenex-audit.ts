import ts from 'typescript'
import {readdirSync,readFileSync,existsSync,statSync,writeFileSync} from 'node:fs'
import {join} from 'node:path'
const files:string[]=[]
const collect=(dir:string)=>{if(!existsSync(dir))return;for(const entry of readdirSync(dir)){const path=join(dir,entry);if(['node_modules','runs','.git','vendor'].includes(entry))continue;if(statSync(path).isDirectory())collect(path);else if(/\.[cm]?tsx?$/.test(path))files.push(path)}}
for(const root of ['examples','core','corpus','tests','test'])collect(root)
const rows:{path:string,line:number,outer:string,inner:string,snippet:string}[]=[]
const name=(node:ts.CallExpression)=>ts.isIdentifier(node.expression)?node.expression.text:ts.isPropertyAccessExpression(node.expression)?node.expression.name.text:''
const quantifiers=new Set(['everyKey','everyBelow','forall','someKey','every'])
for(const path of files){const source=ts.createSourceFile(path,readFileSync(path,'utf8'),ts.ScriptTarget.Latest,true);const walk=(node:ts.Node,outer?:ts.CallExpression)=>{const isCall=ts.isCallExpression(node)&&quantifiers.has(name(node));if(isCall&&outer)rows.push({path,line:source.getLineAndCharacterOfPosition(node.getStart(source)).line+1,outer:name(outer),inner:name(node),snippet:outer.getText(source).slice(0,450)});ts.forEachChild(node,child=>walk(child,isCall?node:outer))};walk(source)}
writeFileSync(process.env.SUPERCOMPUTER_OUTPUT_DIR+'/nested-quantifier-source-candidates.json',JSON.stringify({structuralCandidatesOnly:true,files:files.length,rows},null,2)+'\n');console.log(JSON.stringify({files:files.length,candidates:rows.length,paths:[...new Set(rows.map(r=>r.path))]}))
try{const {domains}=await import('../examples/index.ts');console.log('all example modules import after conservative refusal: '+domains.length)}catch(error){console.log('example import refused: '+String(error));throw error}
