// Deliberately broken stated law: the Action must fail this fixture.
export class Counter {
  value = 0
  // gdp: law only allowed requests change value: value != old(value) implies allowed
  hit(allowed: boolean) { this.value++; return allowed }
}
