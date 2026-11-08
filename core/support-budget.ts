// Shared untrusted allowance rule; existing law-level behavior is unchanged.
export function supportBudget(remaining: number, share: number, priority: boolean, structural = false): number {
 return Math.max(0, Math.min(remaining, structural ? 5_000 : priority ? Math.max(share, remaining / 3) : share))
}
