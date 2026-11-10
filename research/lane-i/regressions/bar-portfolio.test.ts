import {expect,test} from 'bun:test'
import {checkedPortfolioHandoff} from './bar-portfolio.ts'
const outcome=()=>({exit:null,signal:'SIGKILL',wallMs:150,resources:{oomDelta:0,kernelPidOom:false},stages:[{task:'same',stage:'imc',proven:true,checked:true,ms:100},{task:'same',stage:'answer',answer:'sat',by:'imc',ms:101}]})
test('checked portfolio cause does not accept generic killed answers',()=>{
 expect(checkedPortfolioHandoff('chc',outcome())).toBe(true)
 expect(checkedPortfolioHandoff('tip',outcome())).toBe(false)
 const unchecked=outcome();unchecked.stages[0]!.checked=false;expect(checkedPortfolioHandoff('chc',unchecked)).toBe(false)
 const oom=outcome();oom.resources.oomDelta=1;expect(checkedPortfolioHandoff('chc',oom)).toBe(false)
 const wrongTask=outcome();wrongTask.stages[1]!.task='other';expect(checkedPortfolioHandoff('chc',wrongTask)).toBe(false)
})
