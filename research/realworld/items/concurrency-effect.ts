// Effect's Semaphore (Effect-TS/effect, the `effect` package): 4.0.7's SemaphoreImpl (packages/effect/src/Semaphore.ts)
// and 3.22.4's Semaphore (packages/effect/src/internal/effect/circular.ts, Effect.makeSemaphore). MIT, (c) Effectful
// Technologies. https://github.com/Effect-TS/effect/blob/b174739b6b39e4bf48f00f38f1d9fde7a6934368/packages/effect/src/Semaphore.ts
//
// One semaphore: its `permits` (set by makeUnsafe and resize) and what is `taken`; free = permits - taken (:276-278).
// The requests that finish in one step, as a fiber makes them: takeIfAvailable(n) (:284-290, 4.x only), release(n)
// (:322-324), releaseAll (:326-328) and resize(p) (:313-320). A take that waits, and withPermits around another effect,
// are a fiber that acquires later and releases when its effect ends: requests that span others (the 'async' gap).
// releaseUnsafe also wakes the waiters (scheduled, :294-311): with no waiter, it is `taken -= n` and the free count.
// research/realworld/repro/conform-effect.ts runs this rule beside the real Semaphore on both versions (4.x through
// Semaphore.makeUnsafe, 3.x through Effect.unsafeMakeSemaphore, whose release, releaseAll and resize are the same:
// circular.ts:93-106).
import {Int, int, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'Effect-TS/effect', commit: 'b174739b6b39e4bf48f00f38f1d9fde7a6934368', licence: 'MIT', author: 'Effectful Technologies', language: 'TypeScript'}
const v3 = {repo: 'Effect-TS/effect', commit: '5e8c4fe9e82fecdddb7812fa0090470b15a6fea0', licence: 'MIT', author: 'Effectful Technologies', language: 'TypeScript'}

export const semaphore = () => rule('effectSemaphore')
  .params({permits0: nat}) // makeUnsafe(permits) (:215)
  .inputs({op: oneOf('takeIfAvailable', 'release', 'releaseAll', 'resize'), n: int})
  .state({taken: int.from(0), permits: int.from(({permits0}) => permits0)})
  .step(({op, n, taken, permits}) => {
    const free = Int.of(permits).minus(taken)
    // :285-289 if (this.free < n) succeed(false) else taken += n
    const takes = op.is('takeIfAvailable').and(free.atLeast(n))
    return {
      taken: when(takes, Int.of(taken).plus(n), when(op.is('release'), Int.of(taken).minus(n), when(op.is('releaseAll'), 0, taken))),
      // :315 this.permits = permits
      permits: when(op.is('resize'), n, permits),
    }
  })

const s = semaphore()
export const items: RealItem[] = [{
  id: 'concurrency/effect/Semaphore',
  domain: 'concurrency',
  source: {...src, path: 'packages/effect/src/Semaphore.ts', lines: '215-330', export: 'makeUnsafe (SemaphoreImpl)'},
  also: [{...v3, path: 'packages/effect/src/internal/effect/circular.ts', lines: '36-129', export: 'unsafeMakeSemaphore (Semaphore)'}],
  summary: 'Effect\'s semaphore: permits taken without waiting when free, released by count or all at once, and resized; free is the permits less what is taken.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'take(n) that waits for permits, withPermits(n)(effect), and the waiters woken by a release: a fiber that acquires later and releases when its effect ends spans other requests; the rule has the requests that finish at once'},
  ],
  laws: [
    invariant(s, s.law('never more free than the permits', ({taken}) => taken.atLeast(0)),
      'safety', 'inferred', 'a counting semaphore\'s free permits are its permits less those held (:276-278); release returns "the resulting available permits"'),
    invariant(s, s.law('what is taken stays within the permits', ({taken, permits}) => Int.of(taken).atMost(permits)),
      'safety', 'inferred', 'takeIfAvailable takes only free permits (:285-289)'),
    stepLaw(s, s.stepLaw('takeIfAvailable never leaves fewer than none free', ({taken, permits}, after) => Int.of(after.permits).minus(after.taken).atLeast(0).or(Int.of(after.taken).eq(taken)), ({op}) => op.is('takeIfAvailable')),
      'step', 'docs', ':138-145 "Acquires the specified number of permits only if they are immediately available."'),
    stepLaw(s, s.stepLaw('takeIfAvailable never frees permits', ({taken}, after) => Int.of(after.taken).atLeast(taken), ({op}) => op.is('takeIfAvailable')),
      'step', 'docs', ':138-145 "Acquires the specified number of permits only if they are immediately available"'),
    stepLaw(s, s.stepLaw('releaseAll leaves every permit free', ({permits}, after) => Int.of(after.permits).minus(after.taken).eq(permits), ({op}) => op.is('releaseAll')),
      'step', 'docs', ':159 "Releases all permits held by this semaphore and returns the resulting available permits."'),
    stepLaw(s, s.stepLaw('resize keeps what is taken', ({taken}, after) => Int.of(after.taken).eq(taken), ({op}) => op.is('resize')),
      'step', 'inferred', ':313-320 resize sets the permits and wakes the waiters it can; a permit held stays held'),
  ],
}]
