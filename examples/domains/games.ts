// Games and social: a coin economy, a shop with gifts, ability cooldowns, moderation strikes, leaderboards, guilds,
// loot pity, friend requests, daily rewards, matchmaking and wave clearing.
import {type Bool, type Maybe, type Term, bool, count, forall, loop, max, maybe, min, nat, no, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// The coin economy: quests mint coins up to a supply cap, sinks (repairs, fees) burn coins already in circulation. As
// naturals, "minted − burned = supply" reads supply + burned = minted.
const economy = (bug?: 'burn unchecked' | 'cap forgets amount') => rule('coin supply')
  .params({maxSupply: nat})
  .inputs({op: oneOf('mint', 'burn'), amount: nat})
  .state({minted: 0, burned: 0, supply: 0})
  .flags(({op, amount, supply, maxSupply}) => ({
    mints: op.is('mint').and(bug === 'cap forgets amount' ? supply.atMost(maxSupply) : supply.plus(amount).atMost(maxSupply)),
    burns: op.is('burn').and(bug === 'burn unchecked' ? yes : amount.atMost(supply)),
  }))
  .step(({amount, minted, burned, supply, mints, burns}) => ({
    minted: when(mints, minted.plus(amount), minted),
    burned: when(burns, burned.plus(amount), burned),
    supply: when(mints, supply.plus(amount), when(burns, supply.minus(amount), supply)),
  }))
const economyLaws = (r: ReturnType<typeof economy>) => [
  r.law('supply + burned = minted', ({supply, burned, minted}) => supply.plus(burned).eq(minted)),
  r.law('supply <= the cap', ({supply, maxSupply}) => supply.atMost(maxSupply)),
]

// The shop: players earn coins, then buy items for themselves or as gifts. A purchase goes through only if the payer's
// spending stays within their earnings.
const shop = (bug?: 'gift checks the friend') => rule('shop purchases and gifts')
  .inputs({op: oneOf('earn', 'buy', 'gift'), player: nat, friend: nat, price: nat})
  .maps({Earned: 0, Spent: 0, Items: 0})
  .flags(({op, player, friend, price, Earned, Spent}) => {
    const affords = (p: Term) => Spent.at(p).plus(price).atMost(Earned.at(p))
    return {paid: bug === 'gift checks the friend' ? op.is('buy').and(affords(player)).or(op.is('gift').and(affords(friend))) : op.is('buy').or(op.is('gift')).and(affords(player))}
  })
  .step(({op, player, friend, price, paid, Earned, Spent, Items}) => ({
    Earned: Earned.bump(player, op.is('earn'), price),
    Spent: Spent.bump(player, paid, price),
    Items: Items.bump(when(op.is('gift'), friend, player), paid),
  }))
const spentLaw = (r: ReturnType<typeof shop>) => r.law('every player: spent <= earned', ({Spent, Earned}) => forall(p => Spent.at(p).atMost(Earned.at(p))))

// An ability with charges: at most `limit` uses within any `window` ticks. `used` (a query) counts the uses in the
// window before a request; `recent` (a sum) counts the uses in the window ending at `now`.
const cooldown = (opts: {pruned?: boolean, bug?: 'off by one' | 'prunes early'} = {}) => {
  const base = rule(opts.pruned ? 'ability cooldown, pruned' : 'ability cooldown')
    .params({window: nat, limit: nat, now: nat})
    .inputs({t: nat})
    .log('t')
    .sums({recent: (r, {now, window}) => count(r.t.atMost(now).and(now.lt(r.t.plus(window))))})
    .queries({used: (r, {t, window}) => count(t.lt(r.t.plus(window)))})
    .flags(({used, limit}) => ({ready: opts.bug === 'off by one' ? used.atMost(limit) : used.plus(1).atMost(limit)}))
    .keep(({ready}) => ready)
    .relations(({t, now, recent, used}) => [relation(recent.atMost(used), t.atMost(now))])
  return !opts.pruned ? base : base.prune('t', ({window}) => (opts.bug === 'prunes early' ? window.minus(1) : window))
}
const cooldownLaw = (r: ReturnType<typeof cooldown>) => r.law('uses in the window ending at now <= limit', ({recent, limit}) => recent.atMost(limit))

// Moderation: each strike counts until `maxStrikes`, which bans the user; the ban freezes the user's post count (Frozen
// records it at the banning strike), so a banned user's posts never move again.
const moderation = (bug?: 'posts at the limit') => rule('moderation strikes and bans')
  .params({maxStrikes: nat})
  .inputs({op: oneOf('post', 'strike'), user: nat})
  .maps({Strikes: 0, Posts: 0, Frozen: 0})
  .flags(({op, user, Strikes, maxStrikes}) => ({
    posts: op.is('post').and(bug === 'posts at the limit' ? Strikes.at(user).atMost(maxStrikes) : Strikes.at(user).lt(maxStrikes)),
    strikes: op.is('strike').and(Strikes.at(user).lt(maxStrikes)),
  }))
  .step(({user, maxStrikes, posts, strikes, Strikes, Posts, Frozen}) => ({
    Strikes: Strikes.bump(user, strikes),
    Posts: Posts.bump(user, posts),
    Frozen: Frozen.set(user, when(strikes.and(Strikes.at(user).plus(1).eq(maxStrikes)), Posts.at(user), Frozen.at(user))),
  }))
const moderationLaws = (r: ReturnType<typeof moderation>) => [
  r.law('every user: strikes <= maxStrikes', ({Strikes, maxStrikes}) => forall(u => Strikes.at(u).atMost(maxStrikes))),
  r.law('every banned user: posts frozen at the ban', ({Strikes, Posts, Frozen, maxStrikes}) => forall(u => Strikes.at(u).lt(maxStrikes).or(Posts.at(u).eq(Frozen.at(u))))),
]

// A leaderboard: each submission keeps the player's best (Prev holds the best before it, so "the best only goes up"
// is Prev <= Best) and the board's top (prevTop likewise).
const board = (bug?: 'overwrites best' | 'top against player best') => rule('leaderboard')
  .inputs({player: nat, score: nat})
  .state({top: 0, prevTop: 0})
  .maps({Best: 0, Prev: 0})
  .step(({player, score, top, Best, Prev}) => ({
    Prev: Prev.set(player, Best.at(player)),
    Best: Best.set(player, bug === 'overwrites best' ? score : max(Best.at(player), score)),
    prevTop: top,
    top: bug === 'top against player best' ? when(score.gt(Best.at(player)), score, top) : max(top, score),
  }))
const boardLaws = (r: ReturnType<typeof board>) => [
  r.law('a personal best never drops', ({Prev, Best}) => forall(p => Prev.at(p).atMost(Best.at(p)))),
  r.law('every best <= the top', ({Best, top}) => forall(p => Best.at(p).atMost(top))),
  r.law('the top never drops', ({prevTop, top}) => prevTop.atMost(top)),
]

// A guild of at most `cap` members: members join (or are invited) while there's room, and leave.
const guild = (bug?: 'invites skip the cap' | 'off by one') => rule('guild membership')
  .params({cap: nat})
  .inputs({op: oneOf('join', 'invite', 'leave'), member: nat})
  .state({size: 0})
  .maps({In: 0})
  .flags(({op, member, In, size, cap}) => ({
    joins: bug === 'invites skip the cap'
      ? op.is('join').and(In.at(member).eq(0), size.lt(cap)).or(op.is('invite').and(In.at(member).eq(0)))
      : op.is('join').or(op.is('invite')).and(In.at(member).eq(0), bug === 'off by one' ? size.atMost(cap) : size.lt(cap)),
    leaves: op.is('leave').and(In.at(member).eq(1)),
  }))
  .step(({member, joins, leaves, size, In}) => ({
    size: when(joins, size.plus(1), when(leaves, size.minus(1), size)),
    In: In.set(member, when(joins, 1, when(leaves, 0, In.at(member)))),
  }))
const guildLaws = (r: ReturnType<typeof guild>) => [
  r.law('size <= cap', ({size, cap}) => size.atMost(cap)),
  r.law('membership is 0 or 1', ({In}) => forall(m => In.at(m).atMost(1))),
]

// Loot with pity: a chest drops a rare when the roll is lucky, or surely once `pity` misses have piled up. So misses
// never pass the pity, and every pity + 1 chests hold at least one rare.
const loot = (bug?: 'pity one late') => rule('loot drops with pity')
  .params({pity: nat})
  .inputs({lucky: bool})
  .state({misses: 0, opened: 0, rares: 0})
  .flags(({lucky, misses, pity}) => ({dropped: lucky.or(bug === 'pity one late' ? misses.gt(pity) : misses.atLeast(pity))}))
  .step(({misses, opened, rares, dropped}) => ({
    misses: when(dropped, 0, misses.plus(1)),
    opened: opened.plus(1),
    rares: when(dropped, rares.plus(1), rares),
  }))
const lootLaws = (r: ReturnType<typeof loot>) => [
  r.law('misses <= pity', ({misses, pity}) => misses.atMost(pity)),
  r.law('rares + misses <= opened', ({rares, misses, opened}) => rares.plus(misses).atMost(opened)),
  r.law('opened <= rares * (pity + 1) + misses', ({rares, misses, opened, pity}) => opened.atMost(rares.mul(pity.plus(1)).plus(misses))),
]

// Friend requests between users 0..3, a request from a to b kept at key 4a + b: `accept` (sent by `to`) makes the
// pair friends only if `from` asked; a request can be withdrawn before it's accepted, and unfriending clears both.
const pair = (a: Term, b: Term) => a.times(4).plus(b)
const friends = (bug?: 'accept reads the swapped pair') => rule('friend requests')
  .inputs({op: oneOf('request', 'accept', 'withdraw', 'unfriend'), from: upTo(3), to: upTo(3)})
  .maps({Requested: 0, Friends: 0})
  .flags(({op, from, to, Requested}) => ({accepts: op.is('accept').and(Requested.at(bug ? pair(to, from) : pair(from, to)).eq(1))}))
  .step(({op, from, to, accepts, Requested, Friends}) => {
    const k = pair(from, to)
    return {
      Requested: Requested.set(k, op.match({request: () => 1, accept: () => Requested.at(k), withdraw: () => when(Friends.at(k).eq(0), 0, Requested.at(k)), unfriend: () => 0})),
      Friends: Friends.set(k, when(accepts, 1, when(op.is('unfriend'), 0, Friends.at(k)))),
    }
  })
const friendLaws = (r: ReturnType<typeof friends>) => [
  r.law('friends only where asked', ({Friends, Requested}) => forall(k => Friends.at(k).atMost(Requested.at(k)))),
  r.law('a request is 0 or 1', ({Requested}) => forall(k => Requested.at(k).atMost(1))),
]

// Daily login rewards: one claim per day (Claimed keyed by day), each worth at most 50 coins.
const login = rule('daily login rewards')
  .inputs({day: nat, reward: upTo(50)})
  .state({claims: 0, coins: 0})
  .maps({Claimed: 0})
  .flags(({day, Claimed}) => ({fresh: Claimed.at(day).eq(0)}))
  .step(({day, reward, fresh, claims, coins, Claimed}) => ({
    Claimed: Claimed.bump(day, fresh),
    claims: when(fresh, claims.plus(1), claims),
    coins: when(fresh, coins.plus(reward), coins),
  }))
const loginLaws = [
  login.law('every day claimed at most once', ({Claimed}) => forall(d => Claimed.at(d).atMost(1))),
  login.law('coins <= 50 per claim', ({coins, claims}) => coins.atMost(claims.times(50))),
]
const loginLastDay = login.state({last: 0})
  .flags(({day, claims, last}) => ({fresh2: claims.eq(0).or(day.ne(last))}))
  .step(({day, reward, fresh2, claims, coins, last, Claimed}) => ({
    Claimed: Claimed.bump(day, fresh2),
    claims: when(fresh2, claims.plus(1), claims),
    coins: when(fresh2, coins.plus(reward), coins),
    last: when(fresh2, day, last),
  }))

// Matchmaking: a ranked pairing needs both players rated, within 100 points plus the time waited; a rating moves by a
// delta (plus a streak bonus on a win) and is clamped to [floor, ceiling].
const pairing = rule('ranked pairing').inputs({a: upTo(3000), b: maybe(upTo(3000)), ranked: bool, wait: upTo(600)})
type PairEnv = {a: Term, b: Maybe<Term>, ranked: Bool, wait: Term}
const pairs = ({a, b, ranked, wait}: PairEnv, checksNewcomers = true) => b.match({
  none: () => (checksNewcomers ? ranked.not() : yes),
  some: r => a.atMost(r.plus(100).plus(wait)).and(r.atMost(a.plus(100).plus(wait))),
})
const rating = rule('rating update').params({floor: upTo(1000), ceiling: upTo(3000)}).inputs({rating: upTo(3000), won: bool, delta: upTo(50), streak: bool})
type RatingEnv = {floor: Term, ceiling: Term, rating: Term, won: Bool, delta: Term, streak: Bool}
const next = ({floor, ceiling, rating: r, won, delta, streak}: RatingEnv, bug?: 'bonus outside the clamp' | 'loss unclamped') => when(won,
  bug === 'bonus outside the clamp' ? min(ceiling, r.plus(delta)).plus(streak.n.times(10)) : min(ceiling, r.plus(delta).plus(streak.n.times(10))),
  bug === 'loss unclamped' ? r.minus(delta) : max(floor, r.minus(delta)))
const inRange = (env: RatingEnv, bug?: 'bonus outside the clamp' | 'loss unclamped') => env.floor.atMost(next(env, bug)).and(next(env, bug).atMost(env.ceiling))
const matchDecisions = [
  pairing.decide('an unrated player never enters a ranked match', ({ranked, b}) => [ranked, b.isNone], env => pairs(env).not()),
  pairing.decide('paired players are within 700 points', env => pairs(env), ({a, b}) => b.match({none: () => yes, some: r => a.atMost(r.plus(700)).and(r.atMost(a.plus(700)))})),
  pairing.decide('ratings within 100 always pair', ({a, b}) => b.match({none: () => no, some: r => a.atMost(r.plus(100)).and(r.atMost(a.plus(100)))}), env => pairs(env)),
  rating.decide('a rating stays within [floor, ceiling]', ({floor, ceiling, rating: r}) => [floor.atMost(r), r.atMost(ceiling)], env => inRange(env)),
  rating.decide('a win never lowers a rating', ({won, rating: r, ceiling}) => [won, r.atMost(ceiling)], env => next(env).atLeast(env.rating)),
  rating.decide('a loss never raises a rating', ({won, rating: r, floor}) => [won.not(), floor.atMost(r)], env => next(env).atMost(env.rating)),
]
const matchBroken = [
  {name: 'pairs newcomers in ranked', why: 'the pairing forgets that an unrated player may only play casual', decision: pairing.decide('an unrated player never enters a ranked match', ({ranked, b}) => [ranked, b.isNone], env => pairs(env, false).not())},
  {name: 'streak bonus outside the clamp', why: 'the bonus is added after the ceiling is applied', decision: rating.decide('a rating stays within [floor, ceiling]', ({floor, ceiling, rating: r}) => [floor.atMost(r), r.atMost(ceiling)], env => inRange(env, 'bonus outside the clamp'))},
  {name: 'loss without the floor', why: 'a loss subtracts the delta without clamping to the floor', decision: rating.decide('a rating stays within [floor, ceiling]', ({floor, ceiling, rating: r}) => [floor.atMost(r), r.atMost(ceiling)], env => inRange(env, 'loss unclamped'))},
]

// Clearing enemy waves: each turn kills some enemies; clearing a wave brings the next one at full size. The rank is
// (waves left, enemies): a clear drops the first, any other turn the second.
const waves = (bug?: 'no minimum kill' | 'refill keeps the wave') => {
  const base = loop('clearing enemy waves')
    .params({total: nat, size: nat})
    .inputs({kills: nat})
    .state({left: ({total}) => total, enemies: ({size}) => size})
    .while(({left}) => left.gt(0))
    .body(({left, enemies, size, kills}) => ({
      left: when(enemies.atMost(kills), bug === 'refill keeps the wave' ? left : left.minus(1), left),
      enemies: when(enemies.atMost(kills), size, enemies.minus(kills)),
    }))
    .rank(({left, enemies}) => [left, enemies])
  return bug === 'no minimum kill' ? base : base.assume(({kills}) => kills.atLeast(1))
}
const waveLaws = (l: ReturnType<typeof waves>) => [
  l.law('enemies <= wave size', ({enemies, size}) => enemies.atMost(size)),
  l.law('waves left <= total', ({left, total}) => left.atMost(total)),
]

const economyBurn = economy('burn unchecked'), economyCap = economy('cap forgets amount')
const shopGift = shop('gift checks the friend')
const cooldownOff = cooldown({bug: 'off by one'}), cooldownEarly = cooldown({pruned: true, bug: 'prunes early'})
const moderationLimit = moderation('posts at the limit')
const boardOverwrite = board('overwrites best'), boardTop = board('top against player best')
const guildInvite = guild('invites skip the cap'), guildOff = guild('off by one')
const lootLate = loot('pity one late')
const friendsSwapped = friends('accept reads the swapped pair')
const wavesNoMin = waves('no minimum kill'), wavesKeep = waves('refill keeps the wave')

export const domain: Domain = {
  domain: 'games',
  about: 'coin supply, shop and gifts, cooldowns, moderation, leaderboards, guilds, loot pity, friends, daily rewards, matchmaking, waves',
  cases: [
    machineCase('coin supply', 'minted coins are either in circulation or burned, and circulation stays under the cap', economy(), economyLaws(economy()), [
      {name: 'burn unchecked', why: 'a sink burns more than is in circulation, and the truncated supply loses track', rule: economyBurn, laws: economyLaws(economyBurn)},
      {name: 'cap forgets the amount', why: 'the mint checks the supply before the mint, not after', rule: economyCap, laws: economyLaws(economyCap)},
    ]),
    machineCase('shop purchases and gifts', 'no player ever spends more than they earned, gifts included', shop(), [spentLaw(shop())], [
      {name: 'gift checks the friend', why: 'a gift is checked against the recipient\'s balance but charged to the giver', rule: shopGift, laws: [spentLaw(shopGift)]},
    ]),
    machineCase('ability cooldown', 'an ability is used at most `limit` times in any window, read from the log', cooldown(), [cooldownLaw(cooldown())], [
      {name: 'off by one', why: 'the check admits a use when the window already holds `limit` uses', rule: cooldownOff, laws: [cooldownLaw(cooldownOff)]},
    ]),
    machineCase('ability cooldown, pruned', 'the same, the log dropping uses older than the window', cooldown({pruned: true}), [cooldownLaw(cooldown({pruned: true}))], [
      {name: 'prunes one tick early', why: 'a use still inside the window is dropped, so the next request sees one use fewer', rule: cooldownEarly, laws: [cooldownLaw(cooldownEarly)]},
    ]),
    machineCase('moderation strikes and bans', 'strikes stop at the ban, and a banned user\'s posts never move', moderation(), moderationLaws(moderation()), [
      {name: 'posts at the limit', why: 'the post check uses <= and lets a user with maxStrikes strikes post', rule: moderationLimit, laws: moderationLaws(moderationLimit)},
    ]),
    machineCase('leaderboard', 'personal bests and the top only go up, and no best passes the top', board(), boardLaws(board()), [
      {name: 'overwrites the best', why: 'a submission replaces the best with the latest score', rule: boardOverwrite, laws: boardLaws(boardOverwrite)},
      {name: 'top against the player best', why: 'the top is replaced by any score beating the player\'s own best, even below the top', rule: boardTop, laws: boardLaws(boardTop)},
    ]),
    machineCase('guild membership', 'a guild never holds more than its cap', guild(), guildLaws(guild()), [
      {name: 'invites skip the cap', why: 'an officer invite forgets the room check', rule: guildInvite, laws: guildLaws(guildInvite)},
      {name: 'off by one', why: 'a join is admitted at size = cap', rule: guildOff, laws: guildLaws(guildOff)},
    ]),
    machineCase('loot drops with pity', 'misses never pass the pity count, so every pity + 1 chests hold a rare', loot(), lootLaws(loot()), [
      {name: 'pity one late', why: 'the guarantee kicks in after pity + 1 misses', rule: lootLate, laws: lootLaws(lootLate)},
    ]),
    machineCase('friend requests', 'users become friends only where one of them asked', friends(), friendLaws(friends()), [
      {name: 'accept reads the swapped pair', why: 'accepting looks up the acceptor\'s own outgoing request', rule: friendsSwapped, laws: friendLaws(friendsSwapped)},
    ]),
    machineCase('daily login rewards', 'every day\'s reward is claimed at most once', login, loginLaws, [
      {name: 'compares with the last day', why: 'a claim is refused only on the day last claimed, so going back a day claims again', rule: loginLastDay, laws: [loginLastDay.law('every day claimed at most once', ({Claimed}) => forall(d => Claimed.at(d).atMost(1)))]},
    ]),
    decisionCase('matchmaking and ratings', 'ranked pairs are rated and close, and ratings move within [floor, ceiling]', matchDecisions, matchBroken),
    loopCase('clearing enemy waves', 'with at least one kill a turn every wave falls, and a wave never exceeds its size', waves(), waveLaws(waves()), [
      {name: 'no minimum kill', why: 'a turn may kill nothing, and the wave stands forever', loop: wavesNoMin, laws: waveLaws(wavesNoMin)},
      {name: 'refill keeps the wave', why: 'clearing a wave refills it without counting it down', loop: wavesKeep, laws: waveLaws(wavesKeep)},
    ]),
  ],
}
