import {realpathSync,statSync,openSync,fstatSync,readFileSync,closeSync,constants} from 'node:fs'
import {isAbsolute,relative,sep,extname} from 'node:path'
import {digest,refuse} from './protocol.ts'

export type WorkspaceRoot = Readonly<{path:string,dev:number,ino:number}>
export type ConsultationOptions = {workspaceRoots?:readonly string[]}
const inside=(root:string,file:string)=>{const r=relative(root,file);return r!==''&&!isAbsolute(r)&&r!=='..'&&!r.startsWith('..'+sep)}
// Called once by the server, never with tool arguments. Freeze authority before any request.
export function configureRoots(paths:readonly string[]=[]):readonly WorkspaceRoot[]{
  if(paths.length>16)throw new Error('At most16 server workspace roots are supported')
  return Object.freeze(paths.map(p=>{if(!isAbsolute(p)||p.includes('\0'))throw new Error('Workspace roots must be absolute local directories');const path=realpathSync(p),s=statSync(path);if(!s.isDirectory())throw new Error('Workspace root must be a directory');return Object.freeze({path,dev:s.dev,ino:s.ino})}))
}
export function sourceGuard(roots:readonly WorkspaceRoot[],file:string){
  if(!roots.length)refuse('workspace-unconfigured','Configure trusted workspaceRoots on the server; callers cannot grant roots.','File checking is disabled by default.')
  if(!isAbsolute(file)||/^[a-z][a-z0-9+.-]*:/i.test(file)||file.split(/[\\/]/).includes('..'))refuse('invalid-file','Supply an absolute local file without traversal or URL syntax.','Not a supported workspace path.')
  const captures=new Map<string,{hash:string,dev:number,ino:number,size:number}>()
  const bindings=new Map<string,string>()
  let root:WorkspaceRoot|undefined
  const guard=(candidate:string)=>{
    let canonical:string
    try{canonical=realpathSync(candidate)}catch{refuse('file-unavailable','Use an existing readable regular file.','Cannot resolve workspace file.')}
    if(bindings.has(candidate)&&bindings.get(candidate)!==canonical)refuse('source-changed','Retry after symlink replacements have stopped.','Source path resolved to a different file during the request.')
    bindings.set(candidate,canonical)
    const selected=root??roots.find(r=>inside(r.path,canonical))
    if(!selected||!inside(selected.path,canonical))refuse('outside-workspace','Move the file/dependency under a server-configured root.','Resolved file escapes its authorized workspace.')
    const rs=statSync(selected.path)
    if(realpathSync(selected.path)!==selected.path||rs.dev!==selected.dev||rs.ino!==selected.ino)refuse('workspace-changed','Restart the server after reviewing the configured directory.','Workspace root identity changed.')
    root=selected
    const fd=openSync(canonical,constants.O_RDONLY|constants.O_NOFOLLOW|constants.O_NONBLOCK)
    try{
      const s=fstatSync(fd)
      if(!s.isFile())refuse('not-regular-file','Supply a regular source file, not a directory/device.','Target is not a regular file.')
      if(s.size>131072)refuse('source-budget-exceeded','Split the source into files at most128KiB.','Source exceeds128KiB.')
      const bytes=readFileSync(fd)
      if(bytes.length>131072)refuse('source-budget-exceeded','Split the source into files at most128KiB.','Source grew past128KiB.')
      const capture={hash:digest(bytes.toString('base64')),dev:s.dev,ino:s.ino,size:bytes.length},prior=captures.get(canonical)
      if(prior&&digest(prior)!==digest(capture))refuse('source-changed','Retry after edits and file replacements have stopped.','Checked source identity/content changed during the request.')
      if(realpathSync(candidate)!==canonical)refuse('source-changed','Retry in a stable trusted workspace.','Source symlink changed during authorization.')
      captures.set(canonical,capture)
    }finally{closeSync(fd)}
  }
  guard(file)
  const canonical=realpathSync(file)
  if(!['.py','.ts','.mts','.tsx','.js','.mjs'].includes(extname(canonical)))refuse('unsupported-source-language','Use Python or plain TypeScript/JavaScript; async-only Effect/XState and other CLI languages are not yet supported.','Unsupported workspace source language.')
  return {file:canonical,root:root!.path,guard,receipt:()=>{guard(file);for(const p of captures.keys())guard(p);const sources=Object.fromEntries(captures);return {file:canonical,root:root!.path,revision:digest(sources),sources}}}
}
