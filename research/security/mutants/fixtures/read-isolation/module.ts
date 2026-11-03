// tenant is resolved by authentication; _target is an untrusted requested key.
export class PrivateRows {
  rows = new Map<string, number>()
  put(tenant: string, value: number) {
    this.rows.set(tenant, value)
  }
  // gdp: law private reads: isolated by tenant seeing result
  read(tenant: string, _target: string): number {
    return this.rows.get(tenant) ?? 0
  }
}
