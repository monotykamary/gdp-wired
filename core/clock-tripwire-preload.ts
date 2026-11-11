// Loaded before all search modules. A previously bound/captured function still
// crosses this gate, so captured clocks cannot bypass the scoped tripwire.
export const tripwireGate = {active: false}
const dateNow = Date.now.bind(Date)
const performanceNow = performance.now.bind(performance)
function guard(): void {
  if (tripwireGate.active) throw new Error('counted-scope wall-clock read (pre-import capture)')
}
Date.now = () => { guard(); return dateNow() }
Object.defineProperty(performance, 'now', {configurable: true, writable: true, value: () => { guard(); return performanceNow() }})
