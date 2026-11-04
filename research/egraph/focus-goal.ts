// A search-only permutation. The checker still receives the original goal order.
import type {Goal} from '../../kernel/kernel.ts'
export function focusGoal(goal:Goal,index:number):Goal{
  if(!Number.isInteger(index)||index<0||index>=goal.hyps.length)throw Error('invalid conclusion index')
  return {...goal,hyps:[...goal.hyps.slice(0,index),...goal.hyps.slice(index+1),goal.hyps[index]!]}
}
