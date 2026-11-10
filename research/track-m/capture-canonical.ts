import {gzipSync} from 'node:zlib'
import {mldrHandSet} from '../protocols/ic3syn/mldr2-probe.ts'
const {m,laws}=mldrHandSet()
const bundle:Record<string,unknown>={'input.json':{m,laws}}
for(const [file,prefix] of [['row','Inv1758'],['overlap','Inv2973'],['quorum','Inv*'],['newest','Inv3915'],['safety','one primary']]){
 const law=laws.find(l=>l.name.startsWith(prefix!))
 if(!law)throw new Error(`Missing ${prefix}`)
 bundle[`${file}.json`]={law:law.name,laws,at:{}}
}
console.log(`CAPTURE\t${gzipSync(Buffer.from(JSON.stringify(bundle))).toString('base64')}`)
