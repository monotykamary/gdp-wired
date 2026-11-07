import {readFileSync} from 'node:fs'
const read=(p:string)=>{const t=readFileSync(p,'utf8');return JSON.parse(t.split('\n').find(l=>l.startsWith('{'))!)}
const root='runs/track-p-six',fixture=read('runs/track-p-data/family.json'),names=new Map<string,number>(fixture.laws.map((l:any,i:number):[string,number]=>[l.name,i]))
const e=(v:any):string=>v.op==='var'?v.name:v.op==='const'?String(v.value):v.op==='mul'?`${v.k}*(${e(v.a)})`:v.op==='add'?`(${e(v.a)}+${e(v.b)})`:v.op==='sub'?`(${e(v.a)}-${e(v.b)})`:v.op==='get'?`${v.map}[${e(v.key)}]`:JSON.stringify(v)
const data=[
 [7,read(root+'/seven-seventeen/c7/generic-all.json').trace.at(-1).extras],
 [10,read(root+'/ten-sixtysix/c10-all-audit.json').actual.trace.at(-1).extras],
 [11,read(root+'/c11/c11-current-emission.log').trace.at(-1).extras],
 [17,read(root+'/seven-seventeen/c17/generic-all.json').trace.at(-1).extras],
 [33,read(root+'/thirtythree/emission-diff.json').ledgers.find((l:any)=>l.mode==='generic-all').rounds.at(-1).extras],
 [66,read(root+'/ten-sixtysix/c66-all-audit.json').actual.trace.at(-1).extras],
] as [number,{name:string,tuple:any[]}[]][]
console.log('# Six STEP emitter audit: every extra PRE tuple\n\nHistorical emitter-only, all-input-flag/polarity-selector audit of ad4fe53e10f783a7e7b095eb3170203a5e5d83e1b239e4c39c47f2bae7850e5f. This is not the full production selector/reservation path. Full phase and semantic-witness mappings remain in the linked per-target JSON files documented by `runs/REPORT.md`. A failed or SAT partial request is not a reachable protocol counterexample.\n\nNames `C<i>` refer to indices in the unchanged original family fixture. Witness spelling is local to each audit; it does not add an equality.\n')
for(const [index,extras]of data){console.log(`## C${index}: ${extras.length} extra tuples\n\n| Source law/flag | Exact tuple in final observed audit phase |\n|---|---|`);for(const x of extras)console.log(`| ${names.has(x.name)?'C'+names.get(x.name):'`'+x.name+'`'} | \`${x.tuple.map(e).join(', ')}\` |`);if(index!==66)console.log('')}
