// Raw observations only. No callback, budget, clock, reset or proof decision.
// Kept outside the admitted kernel tree; search policy owns aggregation.
export const coreMeter = {tableCells: 0, checkSteps: 0, astNodes: 0, evals: 0, cubeTests: 0, ticks: 0, tinyNodes: 0, tinyTerms: 0, reachStates: 0, reachEdges: 0, reachEvals: 0, reachCompiledEvals: 0}
// Evaluate the child before charging the allocation; never charge reused trees.
export function observeAst<T>(node: T): T { coreMeter.astNodes += 1; return node }
