import {completeWorkProfile} from './work-profile.ts'

// Raw observations only. No callback, budget, clock, reset or proof decision.
// Kept outside the admitted kernel tree; search policy owns aggregation.
export const coreMeter = {tableCells: 0, checkSteps: 0, astNodes: 0, evals: 0, cubeTests: 0, ticks: 0, tinyNodes: 0, tinyTerms: 0, reachStates: 0, reachEdges: 0, reachEvals: 0, reachCompiledEvals: 0}
// Evaluate the child before charging the allocation; never charge reused trees.
export function observeAst<T>(node: T): T { coreMeter.astNodes += 1; return node }

// The three previously unwired columns are opt-in so default raw vectors stay
// exact. These are observations, never callbacks into search or budget policy.
export function observeTableCells(count = 1): void { if (completeWorkProfile.enabled) coreMeter.tableCells += count }
export function observeCheckStep(): void { if (completeWorkProfile.enabled) coreMeter.checkSteps += 1 }
export function observeCubeTest(): void { if (completeWorkProfile.enabled) coreMeter.cubeTests += 1 }
export function observeLinearRows(rows: readonly Record<string, number>[]): void {
  if (completeWorkProfile.enabled) for (const row of rows) coreMeter.tableCells += Object.keys(row).length
}
export function observeConstraintRows(rows: readonly {lin: Record<string, number>}[], start = 0): void {
  if (completeWorkProfile.enabled) for (let i = start; i < rows.length; i++) coreMeter.tableCells += Object.keys(rows[i]!.lin).length
}
