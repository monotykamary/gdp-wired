// Classify the consumer, not merely the outermost guard-leaf wrapper.
export function citationStage(c:{zones?:string[],attempt?:number}):string{
 if(c.zones?.some(z=>z.includes('closure')))return 'closure'
 if(c.attempt!==undefined)return 'later-lemma'
 if(c.zones?.some(z=>z.includes('leaf')))return 'leaf'
 return 'other'
}
