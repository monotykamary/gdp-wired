// tenant comes from authentication. target is an untrusted requested tenant, deliberately ignored.
export class TenantStore {
  rows = new Map<string, number>()
  // gdp: law put preserves foreign new rows: forall k in rows: k != tenant implies ((k in rows) and (k in old(rows)) and rows[k].value == old(rows[k].value))
  // gdp: law put preserves foreign old rows: forall k in old(rows): k != tenant implies ((k in rows) and (k in old(rows)) and rows[k].value == old(rows[k].value))
  put(tenant: string, _target: string, value: number) {
    this.rows.set(tenant, value)
  }
  // gdp: law delete preserves foreign new rows: forall k in rows: k != tenant implies ((k in rows) and (k in old(rows)) and rows[k].value == old(rows[k].value))
  // gdp: law delete preserves foreign old rows: forall k in old(rows): k != tenant implies ((k in rows) and (k in old(rows)) and rows[k].value == old(rows[k].value))
  remove(tenant: string, _target: string) {
    this.rows.delete(tenant)
  }
}
