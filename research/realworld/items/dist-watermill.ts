// ThreeDotsLabs/watermill at 1911646, message/router/middleware/deduplicator.go: the Deduplicator middleware over its
// in-memory ExpiringKeyRepository (a consumer's inbox dedupe: a message whose hash was seen within the window is acked
// and dropped). MIT, (c) Three Dots Labs.
// https://github.com/ThreeDotsLabs/watermill/blob/1911646d2795ab0b738661e2443f23171739d8cc/message/router/middleware/deduplicator.go
import {bool, forall, max, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, stepLaw} from '../lib.ts'

// ------------------------------------------------------------------------------------------------- watermill
// Mapping: a message's hash tag (KeyFactory, Adler-32 by default) is `key`, taken as the input it is (the hash is the
// key's only use). `now` (time.Now() inside IsDuplicate, ms) and the clean-up tick's time are sent in, on one time
// line. `Exp[k]`: tags[k]'s expiry, 0 for no tag (an expiry is never 0: window >= 1 ms, :146-148). Ghosts: `clock`,
// the latest time seen; `Passed[k]`, the time the handler last got a message with key k (0: never), `passes`.
const wsrc = {repo: 'ThreeDotsLabs/watermill', commit: '1911646d2795ab0b738661e2443f23171739d8cc', licence: 'MIT', author: 'Three Dots Labs', language: 'Go'}
export const dedup = () => rule('watermill Deduplicator over mapExpiringKeyRepository')
  .params({window: nat})
  .pre(({window}) => window.atLeast(1))
  // `msg`: Middleware's handler func for a message (:112-123); `clean`: cleanOut(tagsBefore) from the ticker (:180-200).
  .inputs({op: oneOf('msg', 'clean'), key: nat, now: nat})
  .state({clock: 0, seen: bool.from(false)})
  .maps({Exp: 0, Passed: 0, Delivered: bool.from(false)})
  .assume(({now, clock}) => now.atLeast(clock).and(now.atLeast(1)))
  .flags(({op, key, Exp}) => ({
    // :161-178 IsDuplicate: a tag present is a duplicate (expired or not: "fuzzy until-next clean up expiration").
    dup: op.is('msg').and(Exp.at(key).gt(0)),
    passes: op.is('msg').and(Exp.at(key).eq(0)),
  }))
  .step(({op, key, now, window, clock, Exp, Passed, Delivered, dup, passes}) => ({
    clock: max(clock, now),
    seen: dup,
    // :175 tags[key] = now + window; :195-199 a tag whose expiry is before tagsBefore is deleted.
    Exp: Exp.each(k => when(passes.and(k.eq(key)), now.plus(window), when(op.is('clean').and(Exp.at(k).lt(now)), 0, Exp.at(k)))),
    Passed: Passed.each(k => when(passes.and(k.eq(key)), now, Passed.at(k))),
    Delivered: Delivered.each(k => Delivered.at(k).or(passes.and(k.eq(key)))),
  }))

const d = dedup()
export const items: RealItem[] = [{
  id: 'distributed/watermill/Deduplicator',
  domain: 'distributed',
  source: {...wsrc, path: 'message/router/middleware/deduplicator.go', lines: '110-200', export: 'Deduplicator.Middleware, mapExpiringKeyRepository.IsDuplicate, cleanOut'},
  summary: 'A consumer-side dedupe: a message whose hash tag was seen is acked and dropped; a tag is kept at least the window and dropped by a clean-up tick running every half window.',
  expressible: 'partial',
  gaps: [
    {gap: 'async', blocks: 'part', detail: 'the clean-up goroutine\'s ticker (every window/2) is a request; the mutex makes each call one step'},
    {gap: 'time', blocks: 'part', detail: 'time.Now() inside IsDuplicate is the request\'s `now`'},
    {gap: 'hash', blocks: 'part', detail: 'the Adler-32 or SHA-256 tag is the input `key` (a collision drops a different message, by design)'},
  ],
  laws: [
    stepLaw(d, d.stepLaw('a message whose key was delivered within the window is dropped', (_, after) => after.seen,
      ({op, key, now, window, Delivered, Passed}) => op.is('msg').and(Delivered.at(key), now.lt(Passed.at(key).plus(window)))),
    'safety', 'docs', 'deduplicator.go:141-144 "Window specifies the minimum duration of how long the duplicate tags are remembered for"'),
    stepLaw(d, d.stepLaw('a key is delivered again only after more than the window', ({key, now, window, Passed}) => Passed.at(key).plus(window).lt(now),
      ({passes, key, Delivered}) => passes.and(Delivered.at(key))), 'safety', 'docs', 'deduplicator.go:110-111 Middleware "drops similar messages in a given time window"'),
    stepLaw(d, d.stepLaw('a dropped message changes no tag', ({Exp}, after) => forall(j => after.Exp.at(j).eq(Exp.at(j))), ({dup}) => dup),
      'step', 'docs', 'deduplicator.go:167-173 an already seen key returns true and writes nothing'),
  ],
}]
