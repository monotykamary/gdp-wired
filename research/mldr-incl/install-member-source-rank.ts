// Disposable boat-checkout experiment: reduce early field-law admission only.
// Flags, global tuple limits, proof budgets, and the checker are unchanged.
import {createHash} from 'node:crypto'
import {readFileSync,writeFileSync} from 'node:fs'
export const rankAnchor='  const terms=[...keys.values()].slice(0,4),bridged=fieldLawBridges(m,sourceLaws,next,terms,terms)'
const marker='// MEMBER_SOURCE_RANK_PROBE'
export function limitMemberSources(source:string,rank:number){
 if(!Number.isInteger(rank)||rank<0||rank>64)throw Error('rank must be an integer from 0 to 64')
 if(source.includes(marker)||source.split(rankAnchor).length!==2)throw Error('non-unique or already installed member-rank anchor')
 return source.replace(rankAnchor,`  ${marker}: ${rank}\n  sourceLaws.splice(${rank})\n${rankAnchor}`)
}
if(import.meta.main){
 const path='core/count-recovery/member-premises.ts',source=readFileSync(path,'utf8'),rank=Number(process.argv[2]),result=limitMemberSources(source,rank)
 writeFileSync(path,result)
 const hash=(text:string)=>createHash('sha256').update(text).digest('hex')
 console.log(JSON.stringify({diagnostic:true,memberSourceRank:rank,before:hash(source),after:hash(result)}))
}
