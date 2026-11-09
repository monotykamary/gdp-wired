import {protocols} from '../protocols/ic3syn/models.ts';
import {createHash} from 'node:crypto';
import {readFileSync} from 'node:fs';
let total=0;
for(const p of protocols) {const r=p.make(),m=r.machine,l=p.laws(r);total+=l.length;console.log(JSON.stringify({id:p.id,laws:l.map((x:any)=>x.name),pre:!!m.pre,assume:!!m.assume,facts:m.facts??[],fns:Object.keys(m.fns??{}),human:!!p.human,checkKeep:!!p.check?.keep,fields:Object.keys(m)}));}
console.log(JSON.stringify({protocols:protocols.length,totalLaws:total}));
for(const f of ['research/protocols/ic3syn/models.ts','research/protocols/ic3syn/common.ts','research/protocols/ic3syn/run.ts','research/verify-all/model-source-inventory-20261109.ts','research/verify-all/model-source-inventory-20261109.py','research/verify-all/model-source-summary-20261109.ts']) console.log('SHA256',f,createHash('sha256').update(readFileSync(f)).digest('hex'));
