// LiteLLM's budget and rate-limit rules, read from its Python by gdp-wired/extract-py (core/extract-py.ts): what each
// item reads (module and functions, so a fork's maintainers see at a glance whether their changes touch it), the
// boundary each states (answers, skip, a store), and the laws, written against the extracted rule's names so the same
// law runs unchanged on a fork. `run.ts` extracts them from a checkout (upstream at the pinned tag, or a fork) and
// proves the laws; research/realworld/items/litellm-py.ts scores the rules extracted at the pin with the corpus.
import {type Cond, type StepLaw, all, no} from '../../../core/dsl.ts'
import type {PyOptions} from '../../../core/extract-py.ts'

// The pin: LiteLLM's latest release when the items were written.
export const PIN = {repo: 'BerriAI/litellm', tag: 'v1.106.6', commit: '61c6ab78393ef45683dd7d963d2a315bd845e20b', licence: 'MIT', author: 'Berri AI', language: 'Python'}

// The extracted rule as a law reads it: its variables by the names extraction gives them.
// eslint-disable-next-line @typescript-eslint/no-explicit-any
type X = any
type R = {stepLaw: (name: string, then: (b: X, a: X) => Cond, when?: (b: X) => Cond) => StepLaw}
// A law: its name, kind and intent (as the corpus's), and the step law on the extracted rule.
export type PyLaw = {name: string, kind: 'step' | 'access', intent: 'docs' | 'tests' | 'inferred', why: string, law: (r: R) => StepLaw}
export type PySpec = {
  id: string, domain: 'quota' | 'rate limit' | 'circuit breaker',
  file: string, reads: string, summary: string,
  opts: Omit<PyOptions, 'root' | 'python'>,
  // What the extraction leaves to the request or out, for the triage and a fork's reader (the notes say it in full).
  boundary: string,
  // With the boundary inferred (run.ts --bare: no answers, skip or stores), what must still be stated: nothing, or
  // what the code doesn't declare (an untyped result) or a modelling choice (Redis off).
  needs?: Partial<PyOptions>,
  laws: PyLaw[],
}

// x < y and x ≥ y whichever of the two is the integer (a natural compares to an integer from the integer's side).
const lt = (x: X, y: X): Cond => { try { return x.lt(y) } catch { return y.gt(x) } }
const atLeast = (x: X, y: X): Cond => { try { return x.atLeast(y) } catch { return y.atMost(x) } }

const art = (w: string) => (/^[aeiou]/.test(w) ? 'an' : 'a')

// --- the per-entity max_budget checks (litellm/proxy/auth/auth_checks.py) --------------------------------------------
// Each refuses a request when its entity's spend (the cross-pod counter get_current_spend reads, answered by the
// request) has reached the entity's max_budget. The same three laws for each entity; `set` is the condition that the
// entity and its max_budget are given, `off` what else lets the request through by design (a throttled key, an info
// route).
const budget = (entity: string, set: (b: X) => Cond, max: (b: X) => X, off: (b: X) => Cond, why: string): PyLaw[] => [
  {name: `${art(entity)} ${entity} whose spend has reached its max_budget is refused`, kind: 'access', intent: 'docs', why,
    law: r => r.stepLaw(`${art(entity)} ${entity} whose spend has reached its max_budget is refused`, (_b, a) => a.failed, b => all(set(b), off(b).not(), atLeast(b.get_current_spend, max(b))))},
  {name: `${art(entity)} ${entity} below its max_budget is admitted`, kind: 'access', intent: 'docs', why: 'auth_checks.py: the check raises only when the budget is exceeded',
    law: r => r.stepLaw(`${art(entity)} ${entity} below its max_budget is admitted`, (_b, a) => a.failed.not(), b => all(set(b), lt(b.get_current_spend, max(b))))},
  {name: `${art(entity)} ${entity} with no max_budget is admitted`, kind: 'access', intent: 'docs', why: 'BUDGET_CODE_MATRIX.md: a hard max_budget blocks; with none set there is nothing to block on',
    law: r => r.stepLaw(`${art(entity)} ${entity} with no max_budget is admitted`, (_b, a) => a.failed.not(), b => set(b).not())},
]
const BUDGET = {failures: 'kept' as const, answers: {get_current_spend: 'float'}, skip: ['asyncio.create_task', 'CallInfo', '_MASKED_KEY_NAME_RE', 'project_spend_counter_key']}
const MATRIX = 'BUDGET_CODE_MATRIX.md: "Hard max_budget ... block"; the docs: a request is rejected once spend reaches max_budget'
const AUTH = 'litellm/proxy/auth/auth_checks.py'
const SPEND = 'get_current_spend (the cross-pod spend counter, litellm/proxy/proxy_server.py) answered by the request; the alert (CallInfo, asyncio.create_task) and the error message left out'

export const SPECS: PySpec[] = [
  {id: 'quota/litellm-py/virtual_key_max_budget_check', domain: 'quota', file: AUTH, reads: `${AUTH}: virtual_key_max_budget_check, _apply_budget_exceeded_throttle (answered)`,
    summary: 'A key is refused when its spend has reached its max_budget, unless it opted into the over-budget throttle.',
    opts: {entry: ['virtual_key_max_budget_check'], ...BUDGET, answers: {...BUDGET.answers, _apply_budget_exceeded_throttle: 'bool'}},
    boundary: `${SPEND}; whether the key is throttled instead (_apply_budget_exceeded_throttle) answered too`,
    laws: budget('key', b => b.valid_token_max_budget_none.not(), b => b.valid_token_max_budget, b => b.apply_budget_exceeded_throttle, MATRIX)},
  {id: 'quota/litellm-py/team_max_budget_check', domain: 'quota', file: AUTH, reads: `${AUTH}: team_max_budget_check`,
    summary: 'A team is refused when its spend is past its max_budget.',
    opts: {entry: ['team_max_budget_check'], ...BUDGET},
    boundary: SPEND,
    laws: budget('team', b => all(b.team_object_none.not(), b.team_object_max_budget_none.not()), b => b.team_object_max_budget, () => no, MATRIX)},
  {id: 'quota/litellm-py/_project_max_budget_check', domain: 'quota', file: AUTH, reads: `${AUTH}: _project_max_budget_check`,
    summary: 'A project is refused when its spend has reached its budget table\'s max_budget.',
    opts: {entry: ['_project_max_budget_check'], ...BUDGET},
    boundary: SPEND,
    laws: budget('project', b => all(b.project_object_none.not(), b.project_object_litellm_budget_table_none.not(), b.project_object_litellm_budget_table_max_budget_none.not()), b => b.project_object_litellm_budget_table_max_budget, () => no, MATRIX)},
  {id: 'quota/litellm-py/check_end_user_budget', domain: 'quota', file: AUTH, reads: `${AUTH}: check_end_user_budget, RouteChecks.is_info_route (answered)`,
    summary: 'An end user (a customer) is refused when their spend is past their budget table\'s max_budget, except on info routes.',
    opts: {entry: ['check_end_user_budget'], ...BUDGET, answers: {...BUDGET.answers, 'RouteChecks.is_info_route': 'bool'}},
    boundary: `${SPEND}; whether the route is an info route (RouteChecks.is_info_route) answered too`,
    laws: budget('end user', b => all(b.end_user_obj_litellm_budget_table_none.not(), b.end_user_obj_litellm_budget_table_max_budget_none.not()), b => b.end_user_obj_litellm_budget_table_max_budget, b => b.is_info_route, MATRIX)},
]

// --- per-session limits (litellm/proxy/hooks/): state in the proxy's internal usage cache ----------------------------
// The cache is stated as a store (its async_get_cache and async_set_cache a map per key template; its TTL left out) with
// Redis off (`dual_cache.redis_cache` None: the in-memory path every limiter falls back to). The session id and the
// limit come from the request's metadata and the agent registry: answered by the request.
const REDIS_OFF = {stores: {internal_usage_cache: {attrs: {'dual_cache.redis_cache': null}}}}
const STORE = (value: 'int' | 'float') => ({internal_usage_cache: {get: ['async_get_cache'], set: ['async_set_cache'], value, attrs: {'dual_cache.redis_cache': null}}})
const HOOK_SKIP = ['verbose_proxy_logger', 'resolve_llm_provider_for_rate_limit', 'with_service_target', 'os.getenv', 'ProxyRateLimitError', 'log_redis_failure']
const ITER = 'internal_usage_cache_session_iterations_count', SPENT = 'internal_usage_cache_session_budget_spend'
const sessionGiven = (b: X, limit: string) => all(b.get_session_id_none.not(), b[`${limit}_none`].not())
SPECS.push(
  {id: 'rate limit/litellm-py/MaxIterationsHandler', domain: 'rate limit', file: 'litellm/proxy/hooks/max_iterations_limiter.py',
    reads: 'litellm/proxy/hooks/max_iterations_limiter.py: _PROXY_MaxIterationsHandler.__init__, async_pre_call_hook, _make_cache_key, _increment_and_get, _in_memory_increment (_get_session_id and _get_max_iterations answered)',
    summary: 'Each call of an agent session counts one; a call past the session\'s max_iterations is refused with a 429.',
    opts: {entry: '_PROXY_MaxIterationsHandler', methods: ['async_pre_call_hook'], failures: 'kept', answers: {_get_session_id: 'str | None', _get_max_iterations: 'int | None'}, skip: HOOK_SKIP, stores: STORE('int')},
    boundary: 'the session counter in the internal usage cache, Redis off (its Lua INCR path not read), its TTL left out; the session id and max_iterations answered by the request',
    needs: REDIS_OFF,
    laws: [
      {name: 'a call is admitted only while its session is below max_iterations', kind: 'access', intent: 'docs', why: 'max_iterations_limiter.py:3-8 "When the count exceeds max_iterations ... returns 429"',
        law: r => r.stepLaw('a call is admitted only while its session is below max_iterations', (b, a) => a.failed.not().implies(lt(b[ITER].at(b.get_session_id.id).value, b.get_max_iterations)), b => sessionGiven(b, 'get_max_iterations'))},
      {name: 'a session at its max_iterations is refused', kind: 'access', intent: 'docs', why: 'max_iterations_limiter.py:3-8',
        law: r => r.stepLaw('a session at its max_iterations is refused', (_b, a) => a.failed, b => all(sessionGiven(b, 'get_max_iterations'), atLeast(b[ITER].at(b.get_session_id.id).value, b.get_max_iterations)))},
      {name: 'every call of a limited session counts one, refused or not', kind: 'step', intent: 'inferred', why: '_in_memory_increment: the counter is incremented before the check',
        law: r => r.stepLaw('every call of a limited session counts one, refused or not', (b, a) => a[ITER].at(b.get_session_id.id).value.eq(b[ITER].at(b.get_session_id.id).value.plus(1)), b => sessionGiven(b, 'get_max_iterations'))},
      {name: 'a call with no session or no max_iterations is admitted and counts nothing', kind: 'step', intent: 'docs', why: 'async_pre_call_hook: "if session_id is None: return None" and "if max_iterations is None: return None"',
        law: r => r.stepLaw('a call with no session or no max_iterations is admitted and counts nothing', (b, a) => all(a.failed.not(), a[ITER].at(b.get_session_id.id).value.eq(b[ITER].at(b.get_session_id.id).value)), b => sessionGiven(b, 'get_max_iterations').not())},
    ]},
  {id: 'quota/litellm-py/MaxBudgetPerSessionHandler', domain: 'quota', file: 'litellm/proxy/hooks/max_budget_per_session_limiter.py',
    reads: 'litellm/proxy/hooks/max_budget_per_session_limiter.py: _PROXY_MaxBudgetPerSessionHandler.__init__, async_pre_call_hook, _make_cache_key, _get_current_spend (_get_session_id and _get_max_budget_per_session answered)',
    summary: 'A call of an agent session is refused once the session\'s spend has reached its max_budget_per_session.',
    opts: {entry: '_PROXY_MaxBudgetPerSessionHandler', methods: ['async_pre_call_hook'], failures: 'kept', answers: {_get_session_id: 'str | None', _get_max_budget_per_session: 'float | None'}, skip: HOOK_SKIP, stores: STORE('float')},
    boundary: 'the session\'s spend in the internal usage cache, Redis off, read only (the success event that adds a response\'s cost keys it by the raw key, not read here: the claim is for every spend the cache may hold); the session id and the budget answered by the request',
    needs: REDIS_OFF,
    laws: [
      {name: 'a session whose spend has reached max_budget_per_session is refused', kind: 'access', intent: 'docs', why: 'max_budget_per_session_limiter.py: "whether accumulated spend exceeds the budget (429 if so)"',
        law: r => r.stepLaw('a session whose spend has reached max_budget_per_session is refused', (_b, a) => a.failed, b => all(sessionGiven(b, 'get_max_budget_per_session'), atLeast(b[SPENT].at(b.get_session_id.id).value, b.get_max_budget_per_session)))},
      {name: 'a session below max_budget_per_session is admitted', kind: 'access', intent: 'docs', why: 'max_budget_per_session_limiter.py',
        law: r => r.stepLaw('a session below max_budget_per_session is admitted', (_b, a) => a.failed.not(), b => all(sessionGiven(b, 'get_max_budget_per_session'), lt(b[SPENT].at(b.get_session_id.id).value, b.get_max_budget_per_session)))},
    ]},
)

// --- router cooldown (litellm/router_utils/cooldown_handlers.py) -------------------------------------------------------
// The allowed-fails policy: a deployment's fails this window (the fleet-wide counter, answered) against the allowed
// fails: the deployment's override, else the exception type's router policy (answered), else the router's allowed_fails.
const COOL = 'should_cooldown_based_on_allowed_fails_policy_result'
const coolWhen = (r: R, name: string, when: (b: X) => Cond, allowed: (b: X) => X) =>
  r.stepLaw(name, (b, a) => all(a.failed.not(), a[COOL].iff(lt(allowed(b), b.increment_allowed_fails))), when)
SPECS.push({id: 'circuit breaker/litellm-py/should_cooldown_based_on_allowed_fails_policy', domain: 'circuit breaker', file: 'litellm/router_utils/cooldown_handlers.py',
  reads: 'litellm/router_utils/cooldown_handlers.py: should_cooldown_based_on_allowed_fails_policy (Router.get_allowed_fails_from_policy and _increment_allowed_fails answered)',
  summary: 'A deployment is put in cooldown once its failures this window pass the allowed fails: the deployment\'s override, else the router\'s policy for the exception type, else the router\'s allowed_fails.',
  opts: {entry: ['should_cooldown_based_on_allowed_fails_policy'], failures: 'kept', answers: {get_allowed_fails_from_policy: 'int | None', _increment_allowed_fails: 'int'}},
  boundary: 'the fleet-wide fail counter (_increment_allowed_fails: DualCache.increment_cache, Redis or this worker) and the router\'s per-exception policy (Router.get_allowed_fails_from_policy) answered by the request; the counter\'s key and TTL not read',
  // (Router.get_allowed_fails_from_policy declares no result type)
  needs: {answers: {get_allowed_fails_from_policy: 'int | None'}},
  laws: [
    {name: 'with an override, a deployment cools down exactly when its fails pass it', kind: 'step', intent: 'docs', why: 'cooldown_handlers.py: "When allowed_fails_override ... supplied they take precedence over the router-level values"',
      law: r => coolWhen(r, 'with an override, a deployment cools down exactly when its fails pass it', b => b.allowed_fails_override_none.not(), b => b.allowed_fails_override)},
    {name: 'with no override, the exception\'s policy governs', kind: 'step', intent: 'docs', why: 'cooldown_handlers.py: allowed_fails_from_policy if not None, else litellm_router_instance.allowed_fails',
      law: r => coolWhen(r, 'with no override, the exception\'s policy governs', b => all(b.allowed_fails_override_none, b.get_allowed_fails_from_policy_none.not()), b => b.get_allowed_fails_from_policy)},
    {name: 'with neither, the router\'s allowed_fails governs', kind: 'step', intent: 'docs', why: 'cooldown_handlers.py: "True if fails exceed the allowed limit (should cooldown)"',
      law: r => coolWhen(r, 'with neither, the router\'s allowed_fails governs', b => all(b.allowed_fails_override_none, b.get_allowed_fails_from_policy_none, b.litellm_router_instance_allowed_fails_none.not()), b => b.litellm_router_instance_allowed_fails)},
  ]})
