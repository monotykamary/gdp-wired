// Media and streaming: concurrent streams per account, license windows by region, device swaps over a rolling window,
// offline downloads, resume positions, a parental rating gate, royalty payouts and a transcode ladder.
import {all, bool, count, forall, loop, max, min, nat, oneOf, relation, rule, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Concurrent streams: an account starts a stream only while it is under its plan's limit.
const streams = (bug?: 'admits at the limit') => rule('concurrent streams')
  .params({limit: nat})
  .inputs({op: oneOf('start', 'stop'), account: nat})
  .maps({Streams: 0})
  .flags(({op, account, limit, Streams}) => ({
    starts: op.is('start').and(bug === 'admits at the limit' ? Streams.at(account).atMost(limit) : Streams.at(account).lt(limit)),
    stops: op.is('stop').and(Streams.at(account).gt(0)),
  }))
  .step(({account, starts, stops, Streams}) => ({Streams: Streams.set(account, when(starts, Streams.at(account).plus(1), when(stops, Streams.at(account).minus(1), Streams.at(account))))}))
const streamLaws = (r: ReturnType<typeof streams>) => [r.law('every account: streams <= limit', ({Streams, limit}) => forall(k => Streams.at(k).atMost(limit)))]
const streamsAtLimit = streams('admits at the limit')

// License windows: a title plays from its start to (not including) its end, abroad only with a worldwide license.
const license = rule('license windows').inputs({now: nat, start: nat, end: nat, region: oneOf('home', 'abroad'), worldwide: bool})
type LicenseEnv = Parameters<Parameters<typeof license.decide>[1]>[0]
const plays = (e: LicenseEnv, bug?: 'end inclusive') => all(e.start.atMost(e.now), bug === 'end inclusive' ? e.now.atMost(e.end) : e.now.lt(e.end), e.region.is('home').or(e.worldwide))
const licenseDecisions = [
  license.decide('nothing plays before its window', e => plays(e), e => e.start.atMost(e.now)),
  license.decide('nothing plays at or after its end', e => plays(e), e => e.now.lt(e.end)),
  license.decide('abroad needs a worldwide license', e => [plays(e), e.region.is('abroad')], e => e.worldwide),
]
const licenseInclusive = license.decide('nothing plays at or after its end (end inclusive)', e => plays(e, 'end inclusive'), e => e.now.lt(e.end))

// Device swaps: an account may swap devices at most `cap` times in any window. `swaps` (a sum) counts the swaps in the
// window ending at now, `recent` (a query) those in the window before the request.
const swaps = (bug?: 'admits at the cap') => rule('device swaps window')
  .params({window: nat, cap: nat, now: nat})
  .inputs({t: nat})
  .log('t')
  .sums({swapped: (r, {now, window}) => count(r.t.atMost(now).and(now.lt(r.t.plus(window))))})
  .queries({recent: (r, {t, window}) => count(t.lt(r.t.plus(window)))})
  .flags(({recent, cap}) => ({allowed: bug === 'admits at the cap' ? recent.atMost(cap) : recent.plus(1).atMost(cap)}))
  .keep(({allowed}) => allowed)
  .relations(({t, now, swapped, recent}) => [relation(swapped.atMost(recent), t.atMost(now))])
const swapLaws = (r: ReturnType<typeof swaps>) => [r.law('swaps in the window ending at now <= cap', ({swapped, cap}) => swapped.atMost(cap))]
const swapsAtCap = swaps('admits at the cap')

// Offline downloads: at most `quota` titles kept offline; a download expires or is deleted one at a time.
const downloads = (bug?: 'expiry without a download') => rule('offline downloads')
  .params({quota: nat})
  .inputs({op: oneOf('download', 'expire', 'delete')})
  .state({kept: 0, made: 0, gone: 0})
  .flags(({op, kept, quota}) => ({
    adds: op.is('download').and(kept.lt(quota)),
    drops: op.is('expire').or(op.is('delete')).and(bug === 'expiry without a download' ? kept.atLeast(0) : kept.gt(0)),
  }))
  .step(({kept, made, gone, adds, drops}) => ({kept: when(adds, kept.plus(1), when(drops, kept.minus(1), kept)), made: when(adds, made.plus(1), made), gone: when(drops, gone.plus(1), gone)}))
const downloadLaws = (r: ReturnType<typeof downloads>) => [
  r.law('kept <= quota', ({kept, quota}) => kept.atMost(quota)),
  r.law('kept + gone = made', ({kept, gone, made}) => kept.plus(gone).eq(made)),
]
const downloadsExpiry = downloads('expiry without a download')

// Resume positions: watching moves a title's position forward (never back), and only a restart resets it.
const resume = (bug?: 'seeks back') => rule('resume positions')
  .inputs({op: oneOf('watch', 'restart'), title: nat, pos: nat})
  .maps({Pos: 0})
  .step(({op, title, pos, Pos}) => ({Pos: Pos.set(title, when(op.is('restart'), 0, bug === 'seeks back' ? pos : max(Pos.at(title), pos)))}))
const resumeSteps = (r: ReturnType<typeof resume>) => [
  r.stepLaw('without a restart, no position goes back', ({Pos}, after) => forall(k => Pos.at(k).atMost(after.Pos.at(k))), ({op}) => op.is('restart').not()),
  r.stepLaw('a watch reaches at least where it played to', ({title, pos}, after) => pos.atMost(after.Pos.at(title)), ({op}) => op.is('watch')),
]
const resumeSeeks = resume('seeks back')

// A parental gate: a kids profile sees G only; a teen profile G and PG, and R only with the PIN; an adult anything.
const gate = rule('parental rating gate').inputs({rating: oneOf('G', 'PG', 'R'), profile: oneOf('kids', 'teen', 'adult'), pin: bool})
type GateEnv = Parameters<Parameters<typeof gate.decide>[1]>[0]
const shows = (e: GateEnv, bug?: 'teens skip the pin') => e.profile.match({
  kids: () => e.rating.is('G'),
  teen: () => e.rating.is('R').not().or(bug === 'teens skip the pin' ? e.rating.is('R') : e.pin),
  adult: () => yes,
})
const gateDecisions = [
  gate.decide('kids never see R', e => [shows(e) as never, e.profile.is('kids')], e => e.rating.is('R').not()),
  gate.decide('kids never see PG', e => [shows(e) as never, e.profile.is('kids')], e => e.rating.is('PG').not()),
  gate.decide('R needs an adult profile or the PIN', e => [shows(e) as never, e.rating.is('R')], e => e.profile.is('adult').or(e.pin)),
]
const gateTeens = gate.decide('R needs an adult profile or the PIN (teens skip it)', e => [shows(e, 'teens skip the pin') as never, e.rating.is('R')], e => e.profile.is('adult').or(e.pin))

// Royalties: each play earns the rights holder `rate`; a payout goes through only if everything paid stays within what
// was earned.
const royalties = (bug?: 'checks the payout alone') => rule('royalty payouts')
  .params({rate: nat})
  .inputs({op: oneOf('play', 'payout'), amount: nat})
  .state({earned: 0, paid: 0})
  .flags(({op, amount, earned, paid}) => ({pays: op.is('payout').and(bug === 'checks the payout alone' ? amount.atMost(earned) : paid.plus(amount).atMost(earned))}))
  .step(({op, amount, rate, earned, paid, pays}) => ({earned: when(op.is('play'), earned.plus(rate), earned), paid: when(pays, paid.plus(amount), paid)}))
const royaltyLaws = (r: ReturnType<typeof royalties>) => [r.law('paid <= earned', ({paid, earned}) => paid.atMost(earned))]
const royaltySteps = (r: ReturnType<typeof royalties>) => [
  r.stepsLaw('two plays earn two rates', 2, ({earned, rate}, last) => last.earned.eq(earned.plus(rate).plus(rate)), ({op}) => op.is('play')),
]
const royaltiesAlone = royalties('checks the payout alone')

// A transcode ladder: the encoder works down from the top rung, at least one rung per pass, until every rendition is
// made.
const ladder = (bug?: 'stalled passes') => {
  const base = loop(bug ? 'transcode ladder, stalled passes' : 'transcode ladder')
    .params({rungs: nat})
    .inputs({done: nat})
    .state({left: ({rungs}) => rungs, made: 0})
    .while(({left}) => left.gt(0))
    .body(({left, made, done}) => ({left: left.minus(min(left, done)), made: made.plus(min(left, done))}))
    .rank(({left}) => left)
  return bug ? base : base.assume(({done}) => done.atLeast(1))
}
const ladderLaws = (l: ReturnType<typeof ladder>) => [l.law('left + made = rungs', ({left, made, rungs}) => left.plus(made).eq(rungs))]

export const domain: Domain = {
  domain: 'media',
  about: 'concurrent streams, license windows, device swaps, offline downloads, resume positions, parental gate, royalties, transcode ladder',
  cases: [
    machineCase('concurrent streams', 'no account streams on more screens than its plan allows', streams(), streamLaws(streams()), [
      {name: 'admits at the limit', why: 'the start check uses <= and lets a stream past the limit', rule: streamsAtLimit, laws: streamLaws(streamsAtLimit)},
    ]),
    decisionCase('license windows', 'a title plays only inside its window, and abroad only with a worldwide license', licenseDecisions, [
      {name: 'end inclusive', why: 'the window check lets a title play on its end date', decision: licenseInclusive},
    ]),
    machineCase('device swaps window', 'no account swaps devices more than cap times in any window, read from the log', swaps(), swapLaws(swaps()), [
      {name: 'admits at the cap', why: 'the check admits a swap when the window already holds cap swaps', rule: swapsAtCap, laws: swapLaws(swapsAtCap)},
    ]),
    machineCase('offline downloads', 'downloads stay within the quota, and every one made is kept or gone', downloads(), downloadLaws(downloads()), [
      {name: 'expiry without a download', why: 'an expiry is counted with nothing kept, and the truncated count loses track', rule: downloadsExpiry, laws: downloadLaws(downloadsExpiry)},
    ]),
    machineCase('resume positions', 'watching never moves a position back, and a watch reaches where it played to', resume(), [], [
      {name: 'seeks back', why: 'a watch stores the position it reports, so seeking back loses progress', rule: resumeSeeks, laws: [], steps: resumeSteps(resumeSeeks)},
    ], {steps: resumeSteps(resume())}),
    decisionCase('parental rating gate', 'kids see G only, and R needs an adult profile or the PIN', gateDecisions, [
      {name: 'teens skip the PIN', why: 'the teen profile is let through to R without the PIN', decision: gateTeens},
    ]),
    machineCase('royalty payouts', 'payouts never pass what plays earned', royalties(), royaltyLaws(royalties()), [
      {name: 'checks the payout alone', why: 'each payout is compared with the earnings, forgetting what was already paid', rule: royaltiesAlone, laws: royaltyLaws(royaltiesAlone), steps: royaltySteps(royaltiesAlone)},
    ], {steps: royaltySteps(royalties())}),
    loopCase('transcode ladder', 'every pass makes a rendition, so the ladder finishes, each rung made once', ladder(), ladderLaws(ladder()), [
      {name: 'stalled passes', why: 'a pass may make nothing, so the ladder need not finish', loop: ladder('stalled passes'), laws: ladderLaws(ladder('stalled passes'))},
    ]),
  ],
}
