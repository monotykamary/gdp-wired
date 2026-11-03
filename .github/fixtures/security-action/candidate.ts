// Synthetic policy-review fixture, not an upstream finding.
export class Counter {
  value = 0
  hit(allowed: boolean) { this.value++; return allowed }
}
