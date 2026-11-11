import {completeWorkProfile} from './work-profile.ts'
import {startWork, workCounterView} from './work-admission.ts'
// Numeric views are compatibility telemetry. In full mode only the central
// lease can update a counter while a bounded work scope is active.
export const coreMeter = workCounterView({tableCells: 0, checkSteps: 0, astNodes: 0, evals: 0, cubeTests: 0, ticks: 0, tinyNodes: 0, tinyTerms: 0, reachStates: 0, reachEdges: 0, reachEvals: 0, reachCompiledEvals: 0},
  {tableCells: 'tableCells', checkSteps: 'checkSteps', astNodes: 'astNodes', evals: 'evals', cubeTests: 'cubeTests', ticks: 'ticks', tinyNodes: 'tinyNodes', tinyTerms: 'tinyTerms', reachStates: 'reachStates', reachEdges: 'reachEdges', reachEvals: 'reachEvals', reachCompiledEvals: 'reachCompiledEvals'})
// The factory is intentional: a post-allocation observer is too late. Child
// constructors have their own admissions; started work is never refunded.
export function observeAst<T>(build: () => T): T {
  if (completeWorkProfile.enabled) { startWork('astNodes', 1, 'AST allocation'); return build() }
  const node = build(); coreMeter.astNodes++; return node
}
export function observeTableCells(count = 1): void { if (completeWorkProfile.enabled) startWork('tableCells', count, 'table cells') }
export function observeCheckStep(): void { if (completeWorkProfile.enabled) startWork('checkSteps', 1, 'native check step') }
export function observeCubeTest(): void { if (completeWorkProfile.enabled) startWork('cubeTests', 1, 'cube test') }
export function observeLinearRows(rows: readonly Record<string, number>[]): void {
  if (completeWorkProfile.enabled) for (const row of rows) for (const key in row) if (Object.hasOwn(row, key)) observeTableCells()
}
export function observeConstraintRows(rows: readonly {lin: Record<string, number>}[], start = 0): void {
  if (completeWorkProfile.enabled) for (let i = start; i < rows.length; i++) observeLinearRows([rows[i]!.lin])
}
