// PREDICTION: needs a tag; LAW: r.law('n stays zero', ({n}) => n.eq(0))
export class Meter {
  n = 0
  constructor(private listener: (m: Meter) => void) {}
  tick(): void { this.listener(this) }
}
