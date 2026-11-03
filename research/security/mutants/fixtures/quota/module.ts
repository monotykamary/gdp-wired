export class Quota {
  used = 0
  constructor(readonly limit: number) {
    if (limit < 0) throw new Error('negative limit')
  }
  // gdp: law admissions stay within quota: used <= limit
  admit(): boolean {
    if (this.used >= this.limit) return false
    this.used++
    return true
  }
}
