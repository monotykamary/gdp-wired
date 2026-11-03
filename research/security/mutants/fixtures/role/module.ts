// role is the authenticated principal's role, not an untrusted request field.
export class RevisionStore {
  revision = 0
  // gdp: law only maintainers revise: revision != old(revision) implies role == "maintainer"
  revise(role: 'reader' | 'maintainer'): boolean {
    if (role !== 'maintainer') return false
    this.revision++
    return true
  }
}
