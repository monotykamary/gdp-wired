// The caller supplies a permission already resolved by the authentication boundary.
export class PermissionCounter {
  changes = 0
  // gdp: law changes require permission: changes != old(changes) implies allowed
  change(allowed: boolean): boolean {
    if (!allowed) return false
    this.changes++
    return true
  }
}
