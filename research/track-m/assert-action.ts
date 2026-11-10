// Action replay processes also print open results with exit 0. Gate the actual
// source-check verdict and counted budget, not the shell's successful exit.
export {}
const [file,indexText]=process.argv.slice(2),index=Number(indexText)
if(!file||!Number.isInteger(index)||index<0||index>7)throw new Error('usage: assert-action.ts JSONL ACTION_INDEX')
const lines=(await Bun.file(file).text()).split('\n'),results:Record<string,unknown>[]=[]
for(const line of lines){try{const result=JSON.parse(line);if(Array.isArray(result.branches)&&result.branches.length===8)results.push(result)}catch{/* Progress lines are not JSON. */}}
const result=results.at(-1)
if(!result||!(result.branches as boolean[])[index])throw new Error(`action ${index} did not pass its final source check`)
if(typeof result.counted!=='number'||!Number.isFinite(result.counted)||result.counted>5000)throw new Error(`action ${index} exceeded the unchanged 5000 ms counted allowance`)
console.log(JSON.stringify({action:index,sourceChecked:true,counted:result.counted,asserted:true}))
