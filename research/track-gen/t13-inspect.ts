import {protocols} from '../protocols/ic3syn/models.ts'
console.log(JSON.stringify(protocols.find(p => p.id === 'mldr')!.make().machine, null, 2))
