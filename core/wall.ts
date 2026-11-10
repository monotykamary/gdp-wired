// Cooperative cancellation of untrusted search only. Never debits counted work,
// changes a proof rule, or turns an interrupted filter into a successful one.
import {pastWall} from '../kernel/prove.ts'
import {runtimeWall} from './runtime-wall.ts'
// Leave bounded completion headroom for an in-flight synchronous operation,
// result checking and output. This shortens only wall time, never counted fuel.
// The same rule applies to every protocol and budget.
export const searchWall = (ms: number): number => performance.now() + ms - Math.min(1000, Math.max(0, ms) / 20)
export class WallExpired extends Error {
  constructor(readonly phase: string) { super(`time (${phase})`); this.name = 'WallExpired' }
}
export function checkWall(phase: string): void {
  if (pastWall()) throw new WallExpired(phase)
}
// The interpreter must not import the proof engine to check its active wall:
// that would initialize cyclic proof constants before the machine constructors.
runtimeWall.check = checkWall
