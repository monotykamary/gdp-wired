// BUILTINS ONLY: never import/require a checker, importer or dependency here.
import {readFileSync,writeFileSync,writeSync,mkdirSync,copyFileSync,constants,lstatSync,readdirSync} from 'node:fs'
import {execFileSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {resolve,join,dirname,isAbsolute,basename} from 'node:path'
const sha=(b:Buffer)=>createHash('sha256').update(b).digest('hex')
const need=(x:unknown,m:string)=>{if(!x)throw Error(m)}
function mark(event:string,data:unknown={}){const b=Buffer.from('V3_BOUNDARY '+JSON.stringify({event,data})+'\n');let i=0;while(i<b.length)i+=writeSync(1,b.subarray(i))}
const stage=resolve(process.argv[2]??'')
need(stage===process.env.LIFECYCLE_STAGE&&basename(stage).startsWith('astra-lifecycle-v3-'),'unexpected private stage')
need(lstatSync(stage).isDirectory()&&!lstatSync(stage).isSymbolicLink(),'stage is not a private directory')
need(readFileSync(join(stage,'.owner'),'utf8')==='astra-lifecycle-v3'&&readdirSync(stage).every(x=>['.owner','work'].includes(x)),'stage not fresh')
mark('verification-start')
const raw=readFileSync('review-input/input-manifest.json'),manifest=JSON.parse(raw.toString())
for(const f of manifest.inputs){need(!isAbsolute(f.path)&&!f.path.split('/').some((s:string)=>s==='..'||s==='node_modules'),'unsafe input path');need(sha(readFileSync(f.path))===f.sha256,'input changed '+f.path)}
const archivePath=resolve('review-input/typescript-5.9.3.tgz'),archive=readFileSync(archivePath)
need('sha512-'+createHash('sha512').update(archive).digest('base64')===manifest.typescript.integrity,'archive integrity')
mark('verification-complete',{manifestSha256:sha(raw),inputs:manifest.inputs.length,archiveSha256:sha(archive)})
mark('stage-copy-start')
for(const f of manifest.inputs){const dest=join(stage,f.path);mkdirSync(dirname(dest),{recursive:true});copyFileSync(f.path,dest,constants.COPYFILE_EXCL);need(sha(readFileSync(dest))===f.sha256,'staged input differs '+f.path)}
mkdirSync(join(stage,'review-input'));writeFileSync(join(stage,'review-input/input-manifest.json'),raw,{flag:'wx'})
mark('stage-copy-complete')
const modules=join(stage,'node_modules');mkdirSync(modules);const dest=join(modules,'typescript');mkdirSync(dest)
mark('unpack-start')
execFileSync('tar',['-xzf',archivePath,'--strip-components=1','-C',dest],{timeout:2000})
const p=JSON.parse(readFileSync(join(dest,'package.json'),'utf8'))
need(p.version==='5.9.3'&&Object.keys(p.dependencies??{}).length===0,'unexpected TypeScript runtime closure')
mark('unpack-complete',{typescriptVersion:p.version,mainSha256:sha(readFileSync(join(dest,'lib/typescript.js'))),jobPrivate:true})
mark('bootstrap-complete',{networkInstall:false,autoInstall:false})
