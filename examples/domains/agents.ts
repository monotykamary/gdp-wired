// AI agents and LLM operations: token budgets per user, tool calls per task, an org's agent spend within its budget,
// concurrent requests per API key, an approval gate for destructive tools, a task queue, sandbox capabilities carried
// by each call, retries with backoff, and where sensitive data may be sent. Each rule takes the bug its broken variant
// carries.
import {type Bool, type Maybe, type Term, bool, everyKey, forall, loop, max, maybe, min, nat, no, oneOf, rule, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// A daily token budget per user: a request of `tokens` goes through only if the user's usage stays within the budget.
const tokens = (bug?: 'checks usage before the request') => rule('daily token budget per user')
  .params({budget: nat})
  .inputs({user: nat, tokens: nat})
  .maps({Used: 0})
  .flags(({user, tokens: n, budget, Used}) => ({ok: bug ? Used.at(user).atMost(budget) : Used.at(user).plus(n).atMost(budget)}))
  .step(({user, tokens: n, ok, Used}) => ({Used: Used.bump(user, ok, n)}))
const tokenLaws = (r: ReturnType<typeof tokens>) => [r.law('every user: tokens used <= budget', ({Used, budget}) => forall(u => Used.at(u).atMost(budget)))]

// Tool calls per task: an agent may call tools at most `maxCalls` times while working on one task.
const toolCalls = (bug?: 'off by one') => rule('tool calls per task')
  .params({maxCalls: nat})
  .inputs({task: nat})
  .maps({Calls: 0})
  .flags(({task, maxCalls, Calls}) => ({calls: bug ? Calls.at(task).atMost(maxCalls) : Calls.at(task).lt(maxCalls)}))
  .step(({task, calls, Calls}) => ({Calls: Calls.bump(task, calls)}))
const callLaws = (r: ReturnType<typeof toolCalls>) => [r.law('every task: calls <= maxCalls', ({Calls, maxCalls}) => forall(t => Calls.at(t).atMost(maxCalls)))]
const callSteps = (r: ReturnType<typeof toolCalls>) => [
  r.stepLaw('a call adds exactly one to its task', ({task, Calls}, after) => after.Calls.at(task).eq(Calls.at(task).plus(1)), ({calls}) => calls),
  r.stepLaw('a refused call changes nothing', ({task, Calls}, after) => after.Calls.at(task).eq(Calls.at(task)), ({calls}) => calls.not()),
  r.stepsLaw('two calls on one task add two', 2, ({task, Calls}, after, [, next]) => next!.task.eq(task).implies(after.Calls.at(task).eq(Calls.at(task).plus(2))), ({calls}) => calls),
]

// An org funds its agents; an agent spends from its org's budget; an admin may cut the budget, never below what was spent.
const orgSpend = (bug?: 'cut below spent') => rule('agent spend per org')
  .inputs({op: oneOf('fund', 'spend', 'cut'), org: nat, amount: nat})
  .maps({Budget: 0, Spent: 0})
  .flags(({op, org, amount, Budget, Spent}) => ({
    spends: op.is('spend').and(Spent.at(org).plus(amount).atMost(Budget.at(org))),
    cuts: op.is('cut').and(bug ? amount.atMost(Budget.at(org)) : Spent.at(org).plus(amount).atMost(Budget.at(org))),
  }))
  .step(({op, org, amount, spends, cuts, Budget, Spent}) => ({
    Budget: Budget.set(org, when(op.is('fund'), Budget.at(org).plus(amount), when(cuts, Budget.at(org).minus(amount), Budget.at(org)))),
    Spent: Spent.bump(org, spends, amount),
  }))
const orgLaws = (r: ReturnType<typeof orgSpend>) => [r.law('every org: spent <= budget', ({Spent, Budget}) => forall(o => Spent.at(o).atMost(Budget.at(o))))]

// Concurrent requests per API key: a request starts while the key has fewer than `maxActive` in flight.
const concurrency = (bug?: 'retries skip the check') => rule('concurrent requests per API key')
  .params({maxActive: nat})
  .inputs({op: oneOf('start', 'retry', 'finish'), key: nat})
  .maps({Active: 0})
  .flags(({op, key, maxActive, Active}) => ({
    starts: bug ? op.is('start').and(Active.at(key).lt(maxActive)).or(op.is('retry')) : op.is('start').or(op.is('retry')).and(Active.at(key).lt(maxActive)),
    finishes: op.is('finish').and(Active.at(key).atLeast(1)),
  }))
  .step(({key, starts, finishes, Active}) => ({Active: Active.set(key, when(starts, Active.at(key).plus(1), when(finishes, Active.at(key).minus(1), Active.at(key))))}))
const concurrencyLaws = (r: ReturnType<typeof concurrency>) => [r.law('every key: in flight <= maxActive', ({Active, maxActive}) => forall(k => Active.at(k).atMost(maxActive)))]

// The approval gate: a destructive tool call runs only after a human approved that action, and an approval cannot be
// revoked once the action ran (Ran records destructive runs).
const approval = (bug?: 'destructive runs unchecked' | 'revokes after the run') => rule('approval gate for destructive tools')
  .inputs({op: oneOf('approve', 'revoke', 'run'), action: nat, destructive: bool})
  .maps({Approved: 0, Ran: 0})
  .flags(({op, action, destructive, Approved, Ran}) => ({
    runs: op.is('run').and(bug === 'destructive runs unchecked' ? yes : destructive.not().or(Approved.at(action).eq(1))),
    revokes: op.is('revoke').and(bug === 'revokes after the run' ? yes : Ran.at(action).eq(0)),
  }))
  .step(({op, action, destructive, runs, revokes, Approved, Ran}) => ({
    Approved: Approved.set(action, when(op.is('approve'), 1, when(revokes, 0, Approved.at(action)))),
    Ran: Ran.set(action, when(runs.and(destructive), 1, Ran.at(action))),
  }))
const approvalLaws = (r: ReturnType<typeof approval>) => [
  r.law('every destructive action that ran was approved', ({Ran, Approved}) => forall(a => Ran.at(a).atMost(Approved.at(a)))),
  r.law('approvals are 0 or 1', ({Approved}) => forall(a => Approved.at(a).atMost(1))),
]

// A task queue: submissions wait; a worker runs a waiting task. Every task submitted is waiting or run.
const queue = (bug?: 'runs on an empty queue') => rule('agent task queue')
  .inputs({op: oneOf('submit', 'run')})
  .state({submitted: 0, waiting: 0, ran: 0})
  .flags(({op, waiting}) => ({runs: op.is('run').and(bug ? yes : waiting.atLeast(1))}))
  .step(({op, runs, submitted, waiting, ran}) => ({
    submitted: when(op.is('submit'), submitted.plus(1), submitted),
    waiting: when(op.is('submit'), waiting.plus(1), when(runs, waiting.minus(1), waiting)),
    ran: when(runs, ran.plus(1), ran),
  }))
const queueLaws = (r: ReturnType<typeof queue>) => [r.law('waiting + ran = submitted', ({waiting, ran, submitted}) => waiting.plus(ran).eq(submitted))]
const queueSteps = (r: ReturnType<typeof queue>) => [r.stepLaw('a run takes one task off the queue', ({waiting}, after) => after.waiting.plus(1).eq(waiting), ({runs}) => runs)]

// The sandbox: a tool call carries the capabilities it needs (a set); it runs only if every one was granted, and every
// capability a call ever used is remembered.
const sandbox = (bug?: 'checks one capability') => rule('sandbox capabilities')
  .inputs({op: oneOf('grant', 'call'), cap: nat})
  .carries('Needs')
  .maps({Granted: 0, Used: 0})
  .flags(({cap, Needs, Granted}) => ({covered: bug ? Needs.at(cap).atMost(Granted.at(cap)) : everyKey(k => Needs.at(k).atMost(Granted.at(k)))}))
  .flags(({op, covered}) => ({calls: op.is('call').and(covered)}))
  .step(({op, cap, calls, Granted, Used, Needs}) => ({
    Granted: Granted.set(cap, when(op.is('grant'), max(Granted.at(cap), 1), Granted.at(cap))),
    Used: Used.each(k => when(calls, max(Used.at(k), Needs.at(k)), Used.at(k))),
  }))
const sandboxLaws = (r: ReturnType<typeof sandbox>) => [r.law('every capability used was granted', ({Used, Granted}) => forall(k => Used.at(k).atMost(Granted.at(k))))]

// Retries with backoff: each failed attempt waits min(delay, 3) seconds and tries again, at most `tries` times. The rank is the
// attempts left.
const retries = (bug?: 'retries forever' | 'backoff uncapped') => loop('retries with backoff')
  .params({tries: nat})
  .inputs({ok: bool, delay: nat})
  .state({left: ({tries}) => tries, waited: 0})
  .while(({left}) => left.gt(0))
  .body(({left, waited, ok, delay}) => ({
    left: when(ok, 0, bug === 'retries forever' ? left : left.minus(1)),
    waited: waited.plus(bug === 'backoff uncapped' ? delay : min(delay, 3)),
  }))
  .rank(({left}) => left)
const retryLaws = (l: ReturnType<typeof retries>) => [
  l.law('attempts left <= tries', ({left, tries}) => left.atMost(tries)),
  l.law('waited <= 3 per attempt made', ({waited, tries, left}) => waited.atMost(tries.minus(left).times(3))),
]

// Where data may go: a request with personal data is sent to an external model only with consent that hasn't expired.
const routing = rule('sensitive data routing').inputs({pii: bool, wantsExternal: bool, consentUntil: maybe(nat), now: nat})
type RouteEnv = {pii: Bool, wantsExternal: Bool, consentUntil: Maybe<Term>, now: Term}
const external = ({pii, wantsExternal, consentUntil, now}: RouteEnv, bug?: 'missing consent counts') =>
  wantsExternal.and(pii.not().or(consentUntil.match({none: () => (bug ? yes : no), some: u => now.lt(u)})))
const routeDecisions = [
  routing.decide('personal data without consent stays local', ({pii, consentUntil}) => [pii, consentUntil.isNone], env => external(env).not()),
  routing.decide('expired consent keeps personal data local', ({pii, consentUntil, now}) => [pii, consentUntil.match({none: () => no, some: u => u.atMost(now)})], env => external(env).not()),
  routing.decide('data without personal fields goes where asked', ({pii, wantsExternal}) => [pii.not(), wantsExternal], env => external(env)),
]
const routeBroken = [
  {name: 'missing consent counts as given', why: 'a request with no consent record is treated as consented', decision: routing.decide('personal data without consent stays local', ({pii, consentUntil}) => [pii, consentUntil.isNone], env => external(env, 'missing consent counts').not())},
]

const tokensBefore = tokens('checks usage before the request')
const callsOff = toolCalls('off by one')
const orgCut = orgSpend('cut below spent')
const retrySkip = concurrency('retries skip the check')
const approvalUnchecked = approval('destructive runs unchecked'), approvalRevoke = approval('revokes after the run')
const queueEmpty = queue('runs on an empty queue')
const sandboxOne = sandbox('checks one capability')
const retryForever = retries('retries forever'), retryUncapped = retries('backoff uncapped')

export const domain: Domain = {
  domain: 'ai agents',
  about: 'token budgets, tool calls per task, org spend, concurrency per key, approval gates, task queues, sandbox capabilities, retries, data routing',
  cases: [
    machineCase('daily token budget per user', 'no user ever uses more tokens than the budget', tokens(), tokenLaws(tokens()), [
      {name: 'checks usage before the request', why: 'the check reads the usage before the request is added, so the last request overshoots', rule: tokensBefore, laws: tokenLaws(tokensBefore)},
    ]),
    machineCase('tool calls per task', 'an agent calls tools at most maxCalls times per task; a call adds one, a refused call changes nothing', toolCalls(), callLaws(toolCalls()), [
      {name: 'off by one', why: 'the check admits a call when the task already made maxCalls', rule: callsOff, laws: callLaws(callsOff), steps: callSteps(callsOff)},
    ], {steps: callSteps(toolCalls())}),
    machineCase('agent spend per org', 'an org\'s agents never spend more than its budget, cuts included', orgSpend(), orgLaws(orgSpend()), [
      {name: 'cut below spent', why: 'a budget cut is checked against the budget, not against what was already spent', rule: orgCut, laws: orgLaws(orgCut)},
    ]),
    machineCase('concurrent requests per API key', 'no key ever has more than maxActive requests in flight', concurrency(), concurrencyLaws(concurrency()), [
      {name: 'retries skip the check', why: 'a retry starts without counting against the key\'s limit', rule: retrySkip, laws: concurrencyLaws(retrySkip)},
    ]),
    machineCase('approval gate for destructive tools', 'every destructive action that ran was approved by a human, and stays approved', approval(), approvalLaws(approval()), [
      {name: 'destructive runs unchecked', why: 'the gate lets any run through, destructive or not', rule: approvalUnchecked, laws: approvalLaws(approvalUnchecked)},
      {name: 'revokes after the run', why: 'an approval is withdrawn after the action already ran, erasing the record', rule: approvalRevoke, laws: approvalLaws(approvalRevoke)},
    ]),
    machineCase('agent task queue', 'every submitted task is waiting or ran, and a run takes one off the queue', queue(), queueLaws(queue()), [
      {name: 'runs on an empty queue', why: 'a worker runs a task when none is waiting', rule: queueEmpty, laws: queueLaws(queueEmpty), steps: queueSteps(queueEmpty)},
    ], {steps: queueSteps(queue())}),
    machineCase('sandbox capabilities', 'a tool call runs only if every capability it carries was granted', sandbox(), sandboxLaws(sandbox()), [
      {name: 'checks one capability', why: 'the sandbox checks the capability named in the request, not every one the call carries', rule: sandboxOne, laws: sandboxLaws(sandboxOne)},
    ]),
    loopCase('retries with backoff', 'retries halt within tries attempts, each waiting at most 3', retries(), retryLaws(retries()), [
      {name: 'retries forever', why: 'a failed attempt doesn\'t count, so a failing call retries forever', loop: retryForever, laws: retryLaws(retryForever)},
      {name: 'backoff uncapped', why: 'the delay is taken as sent, without the cap', loop: retryUncapped, laws: retryLaws(retryUncapped)},
    ]),
    decisionCase('sensitive data routing', 'personal data goes to an external model only with unexpired consent', routeDecisions, routeBroken),
  ],
}
