import {protocols} from '../protocols/ic3syn/models.ts'
for (const p of protocols) {
 const r=p.make(); const laws=p.laws(r);
 console.log('RUNTIME '+JSON.stringify({id:p.id,file:p.file,laws:laws.map((l:any)=>l),machineFields:Object.keys(r.machine),pre:(r.machine as any).pre,assume:(r.machine as any).assume,facts:(r.machine as any).facts,keep:!!p.check?.keep}));
}
