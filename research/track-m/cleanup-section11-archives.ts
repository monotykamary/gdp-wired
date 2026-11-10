import {readFileSync,rmSync} from 'node:fs'
for(const file of process.argv.slice(2)){
 const manifest=readFileSync(file,'utf8').split('\n').filter(l=>l.startsWith('{')).map(l=>JSON.parse(l)).find(r=>r.artifact==='section10-chunk-manifest')
 if(!manifest||!/^\/home\/user\/track-m-s10-receipts-[A-Za-z0-9]+$/.test(manifest.dir))throw new Error('unexpected archive path')
 rmSync(manifest.dir,{recursive:true,force:true});console.log(JSON.stringify({removedArchive:manifest.dir}))
}
