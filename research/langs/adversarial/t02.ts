// PREDICTION: refuted; LAW: r.law('n stays zero', ({n}) => n.eq(0))
export class Meter {
  n = 0
  constructor(private enabled: () => boolean) {}
  tick(): void { if (this.enabled()) this.n = 1 }
}
