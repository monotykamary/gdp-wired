// Dependency-free bridge: active only while untrusted count search opts in.
// The raw counter storage and protected reader own no admission policy.
export const tableAdmissionHook: {admit?: (count: number) => void, invalidate?: () => void} = {}
