export class Shipment {
  approved = false
  shipped = false
  approve() { this.approved = true }
  // gdp: law approval precedes shipment: shipped != old(shipped) implies old(approved)
  ship(): boolean {
    if (!this.approved) return false
    this.shipped = true
    return true
  }
}
