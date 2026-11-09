// Shared untrusted allowance rule; existing law-level behavior is unchanged.
// Pending excludes already-tried, kept and carried laws of this round.
export const attemptShare = (remaining: number, pending: ReadonlySet<string>): number => Math.max(0, remaining) / Math.max(1, pending.size)
export function supportBudget(remaining: number, share: number, priority: boolean, structural = false): number {
 return Math.max(0, Math.min(remaining, structural ? 5_000 : priority ? Math.max(share, remaining / 3) : share))
}
