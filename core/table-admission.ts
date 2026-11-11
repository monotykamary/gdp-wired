// Compatibility scope only. Actual table units are pre-admitted at their
// physical sites through the common ledger; there is no numeric side credit.
export function withTableAdmission<T>(run: () => T): T { return run() }
