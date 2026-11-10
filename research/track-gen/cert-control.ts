import {existsSync,readFileSync,writeFileSync} from 'node:fs'
if(process.env.TRACK_GEN_DISPOSABLE!=='1')throw Error('disposable only')
const file='core/counts.ts',saved='/tmp/track-gen-counts-original.ts';if(!existsSync(saved))writeFileSync(saved,readFileSync(file))
let text=readFileSync(saved,'utf8');const mode=process.argv[2]
if(mode==='facts'||mode==='both'){
 const start=text.indexOf('    // Reuse Boolean-region identities'),end=text.indexOf('    pairs: for',start)
 if(start<0||end<start)throw Error('facts anchor');text=text.slice(0,start)+text.slice(end)
}
if(mode==='tail'){
 const start=text.indexOf('    // Structured identities supplement'),end=text.indexOf('\n  }\n  const picks',start)
 if(start<0||end<start)throw Error('tail anchor');text=text.slice(0,start)+text.slice(end)
}
if(mode==='singletons'||mode==='both'){
 const line='    for (const t of ts) picks.push([r[0], [t]])\n';if(!text.includes(line))throw Error('picks anchor');text=text.replace(line,'')
}
if(mode==='legacy-cert'){
 const old=readFileSync('base/core/counts.ts','utf8'),start='export function certFor(',end='// --- the candidates'
 const a=text.indexOf(start),b=text.indexOf(end,a),c=old.indexOf(start),d=old.indexOf(end,c)
 if([a,b,c,d].some(v=>v<0))throw Error('cert anchors');text=text.slice(0,a)+old.slice(c,d)+text.slice(b)
}
writeFileSync(file,text)
