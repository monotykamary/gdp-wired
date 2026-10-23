// node-casbin v5.51.1 (casbin/node-casbin): the policy-effect decision (src/effect/defaultEffectorStream.ts, driven by
// the enforcer's policy loop, src/coreEnforcer.ts privateEnforce) and the RBAC role manager (src/rbac/defaultRoleManager.ts).
// Apache-2.0, (c) The Casbin Authors. https://github.com/casbin/node-casbin/tree/2d90c7d8c3b522415605cf3d25481e763e73381e/src
import {bool, forall, nat, no, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'casbin/node-casbin', commit: '2d90c7d8c3b522415605cf3d25481e763e73381e', licence: 'Apache-2.0', author: 'The Casbin Authors', language: 'TypeScript'}

// ---------------------------------------------------------------------------------------------------------------------
// The effector. One request is one enforce() call; one step is one turn of the loop over the policies
// (coreEnforcer.ts:483-573): the matcher's result for policy i and its p_eft column become an Effect (:530-562), which
// is pushed into the stream (:564); the loop breaks once the stream says `done` (:570-572), so a turn after `done` is a
// request where every part keeps its value. With no policy (or a matcher that reads none), the code pushes one Allow or
// Indeterminate (:574-596): one turn with p_eft absent. The result is `current()` (:598), the stream's `res`.
export const effectorStream = () => rule('casbin DefaultEffectorStream')
  // defaultEffectorStream.ts:37-75 the model's policy_effect expression (constants.ts:15-21 EffectExpress). Any other
  // expression throws at the first push (:73-74): an enforce that fails, not modelled.
  .params({expr: oneOf('allow', 'deny', 'allowAndDeny', 'priority', 'subjectPriority')})
  // coreEnforcer.ts:528-549 the matcher's result: false, 0 or '' (Indeterminate); true, a non-empty string or the number
  // 1 (Allow); the number 2 (Indeterminate), 3 (Deny), or any other number (taken as it is: an Effect that is none of
  // the three). :552-561 the policy's p_eft column: absent, 'allow', 'deny', or another string.
  .inputs({result: oneOf('falsy', 'truthy', 'num2', 'num3', 'numOther'), pEft: oneOf('none', 'allow', 'deny', 'other')})
  // defaultEffectorStream.ts:23-25 done, res, rec. Ghosts: `sawAllow`, `sawDeny`, `pushes`: whether an Allow / a Deny
  // effect was pushed, and how many effects were (what the expression's some(where ...) ranges over).
  .state({done: bool.from(false), res: bool.from(false), rec: bool.from(false), sawAllow: bool.from(false), sawDeny: bool.from(false), pushes: 0})
  .flags(({result, pEft, done}) => {
    // :530-549 then :552-561: an Allow from the matcher is turned into the policy's own effect.
    const allowed = result.is('truthy')
    return {
      push: done.not(),
      eAllow: allowed.and(pEft.is('none').or(pEft.is('allow'))),
      eDeny: allowed.and(pEft.is('deny')).or(result.is('num3')),
      eIndet: result.is('falsy').or(result.is('num2'), allowed.and(pEft.is('other'))),
    }
  })
  .step(({expr, push, eAllow, eDeny, eIndet, done, res, rec, sawAllow, sawDeny, pushes}) => {
    const prio = expr.is('priority').or(expr.is('subjectPriority'))
    // defaultEffectorStream.ts:38-72, case by case.
    const res2 = when(expr.is('allow'), when(eAllow, yes, res),
      when(expr.is('deny'), when(eDeny, no, yes),
        when(expr.is('allowAndDeny'), when(eAllow, yes, when(eDeny, no, res)),
          when(eIndet.not(), eAllow, res))))
    const done2 = when(expr.is('allow'), eAllow.or(done), when(expr.is('deny'), eDeny.or(done),
      when(expr.is('allowAndDeny'), eDeny.or(done), eIndet.not().or(done))))
    const rec2 = when(expr.is('allow'), eAllow.or(rec), when(expr.is('deny'), eDeny.or(rec),
      when(expr.is('allowAndDeny'), eAllow.or(eDeny), when(prio, eIndet.not().or(rec), rec))))
    return {
      res: when(push, res2, res), done: when(push, done2, done), rec: when(push, rec2, rec),
      sawAllow: when(push, eAllow.or(sawAllow), sawAllow), sawDeny: when(push, eDeny.or(sawDeny), sawDeny),
      pushes: when(push, pushes.plus(1), pushes),
    }
  })

const eff = effectorStream()
const effItem: RealItem = {
  id: 'access/node-casbin/effectorStream',
  domain: 'access',
  source: {...src, path: 'src/effect/defaultEffectorStream.ts', lines: '22-78', export: 'DefaultEffectorStream'},
  also: [{...src, path: 'src/coreEnforcer.ts', lines: '483-598', export: 'privateEnforce'}, {...src, path: 'src/constants.ts', lines: '15-21', export: 'EffectExpress'}],
  summary: 'The enforcer pushes each policy\'s effect (from the matcher and p_eft) into the effector stream until it is done; the result is allow or deny by the model\'s policy_effect: some allow, no deny, allow-and-no-deny, or the first decisive policy.',
  expressible: 'full',
  gaps: [],
  laws: [
    invariant(eff, eff.law('allow-and-deny: any matching deny denies', ({expr, sawDeny, res}) => expr.is('allowAndDeny').and(sawDeny).implies(res.not())),
      'safety', 'docs', 'constants.ts:18 `some(where (p_eft == allow)) && !some(where (p_eft == deny))`: deny overrides allow'),
    invariant(eff, eff.law('allow-and-deny: no matching allow, no access', ({expr, sawAllow, res}) => expr.is('allowAndDeny').and(res).implies(sawAllow)),
      'access', 'docs', 'constants.ts:18 `some(where (p_eft == allow))`: access needs an allow'),
    invariant(eff, eff.law('allow-override: allowed exactly when some policy allows', ({expr, sawAllow, res}) => expr.is('allow').implies(res.iff(sawAllow))),
      'access', 'docs', 'constants.ts:16 `some(where (p_eft == allow))`'),
    invariant(eff, eff.law('deny-override: once evaluated, allowed exactly when no policy denies', ({expr, sawDeny, res, pushes}) => expr.is('deny').and(pushes.atLeast(1)).implies(res.iff(sawDeny.not()))),
      'access', 'docs', 'constants.ts:17 `!some(where (p_eft == deny))`'),
    stepLaw(eff, eff.stepLaw('once decided, the result never changes', ({res}, after) => after.res.iff(res), ({done}) => done),
      'step', 'inferred', 'coreEnforcer.ts:570-572 the loop breaks on `done`: the stream\'s answer is final'),
    stepLaw(eff, eff.stepLaw('priority: the first decisive policy decides', ({eAllow}, after) => after.done.and(after.res.iff(eAllow)), ({expr, done, eIndet}) => expr.is('priority').and(done.not(), eIndet.not())),
      'step', 'docs', 'constants.ts:19 `priority(p_eft) || deny`: policies in order, the first that applies decides'),
  ],
}

// ---------------------------------------------------------------------------------------------------------------------
// The role manager, without domains, patterns or a domain hierarchy (defaultRoleManager.ts:194-197 then reads the one
// default domain's roles as they are). Role names are interned as numbers below `names` (a param); a link name1 ->
// name2 is the cell `name1 * names + name2` of `Link`... which needs a product of two unknowns, so `names` is the
// constant N below and every name is assumed below it (an encoding bound, see gaps).
const N = 64
export const roleManager = () => rule('casbin DefaultRoleManager')
  // :137-141 maxHierarchyLevel (the enforcer passes 10).
  .params({maxLevel: nat})
  // The depth the rule computes hasLink to (see gaps): this item is the role manager with maxHierarchyLevel 0 or 1.
  .pre(({maxLevel}) => maxLevel.atMost(1))
  // One call: addLink (:228-240), deleteLink (:255-271), clear (:245-248), hasLink (:277-296: reads only).
  .inputs({op: oneOf('addLink', 'deleteLink', 'clear', 'hasLink'), a: nat, b: nat})
  .assume(({a, b}) => a.lt(N).and(b.lt(N)))
  // Roles (:86, a Map name -> Role) as `Known` (the name has a Role object), Role.roles (:39) as `Link` at a*N+b.
  // `answer`: what the last hasLink returned (its output).
  .maps({Known: 0, Link: 0})
  .state({answer: bool.from(false)})
  .flags(({op, a, b, Known}) => ({
    adds: op.is('addLink'),
    // :264-266 `if (!allRoles.has(name1) || !allRoles.has(name2)) return;`
    deletes: op.is('deleteLink').and(Known.at(a).eq(1), Known.at(b).eq(1)),
    clears: op.is('clear'),
  }))
  .step(({op, a, b, adds, deletes, clears, maxLevel, Known, Link, answer}) => ({
    // :237-238 loadOrDefault creates both roles; written at every key since one step may create two.
    Known: Known.each(k => when(clears, 0, when(adds.and(k.eq(a).or(k.eq(b))), 1, Known.at(k)))),
    // :46-51 addRole skips a duplicate; :53-55 deleteRole filters it out.
    Link: Link.each(k => when(clears, 0, when(adds.and(k.eq(a.times(N).plus(b))), 1, when(deletes.and(k.eq(a.times(N).plus(b))), 0, Link.at(k))))),
    // :284-295 for maxLevel <= 1: name1 === name2, or both known and (level >= 1 and a direct link).
    answer: when(op.is('hasLink'), a.eq(b).or(Known.at(a).eq(1).and(Known.at(b).eq(1), maxLevel.atLeast(1), Link.at(a.times(N).plus(b)).eq(1))), answer),
  }))

const rm = roleManager()
const rmItem: RealItem = {
  id: 'access/node-casbin/roleManager',
  domain: 'access',
  source: {...src, path: 'src/rbac/defaultRoleManager.ts', lines: '37-296', export: 'DefaultRoleManager'},
  summary: 'Role inheritance links (addLink, deleteLink, clear) and hasLink: name1 inherits name2 if equal or reachable through at most maxHierarchyLevel links.',
  expressible: 'partial',
  gaps: [
    {gap: 'recursion', blocks: 'part', detail: 'Role.hasRole (defaultRoleManager.ts:57-71) recurses over the link graph to depth maxHierarchyLevel (a param, 10 by default, from the enforcer); the rule computes hasLink only for maxHierarchyLevel <= 1 (equal names or one direct link: `.pre`), and every law about inherited roles is unstated',
      laws: ['hasLink is transitive within maxHierarchyLevel', 'deleting the last path revokes the inherited role', 'no inheritance deeper than maxHierarchyLevel']},
    {gap: 'two-key-map', blocks: 'part', detail: 'a map keyed by a pair of names: links are the cells name1 * 64 + name2 of one map, with every interned name assumed below 64 (no two-key maps; a param bound would be a product of two unknowns)'},
    {gap: 'string', blocks: 'part', detail: 'pattern matching functions (addMatchingFunc, addDomainMatchingFunc: globs or regexes over role and domain names, :194-221) are left out; the rule is the role manager without them'},
  ],
  laws: [
    invariant(rm, rm.law('every link joins two known roles', ({Link, Known}) => forall((x, y) => x.lt(N).and(y.lt(N), Link.at(x.times(N).plus(y)).eq(1)).implies(Known.at(x).eq(1).and(Known.at(y).eq(1))))),
      'safety', 'inferred', 'defaultRoleManager.ts:237-239 a link is added only between roles it creates; hasLink (:290) reads only known roles'),
    stepLaw(rm, rm.stepLaw('a name always inherits itself', (_, after) => after.answer, ({op, a, b}) => op.is('hasLink').and(a.eq(b))),
      'access', 'docs', 'defaultRoleManager.ts:284-286 `if (name1 === name2) return true`'),
    stepLaw(rm, rm.stepLaw('after addLink, name1 inherits name2 directly', ({a, b}, after) => after.Link.at(a.times(N).plus(b)).eq(1).and(after.Known.at(a).eq(1), after.Known.at(b).eq(1)), ({op}) => op.is('addLink')),
      'step', 'docs', 'defaultRoleManager.ts:224-225 "addLink adds the inheritance link between role: name1 and role: name2"'),
    stepLaw(rm, rm.stepLaw('after deleteLink, name1 no longer inherits name2 directly', ({a, b}, after) => after.Link.at(a.times(N).plus(b)).eq(0), ({op}) => op.is('deleteLink')),
      'step', 'docs', 'defaultRoleManager.ts:251-252 "aka role: name1 does not inherit role: name2 any more"'),
    stepLaw(rm, rm.stepLaw('a link changes only for the pair named', ({a, b, Link}, after) => forall(k => k.eq(a.times(N).plus(b)).or(after.Link.at(k).eq(Link.at(k)))), ({op}) => op.is('addLink').or(op.is('deleteLink'))),
      'step', 'inferred', 'defaultRoleManager.ts:239, :270: addRole / deleteRole touch role1\'s list at role2 only'),
    stepLaw(rm, rm.stepLaw('with maxHierarchyLevel 0 only a name itself is held', ({a, b}, after) => after.answer.implies(a.eq(b)), ({op, maxLevel}) => op.is('hasLink').and(maxLevel.eq(0))),
      'access', 'docs', 'defaultRoleManager.ts:61-63 `if (hierarchyLevel <= 0) return false`'),
  ],
  unstated: [
    {name: 'hasLink is transitive within maxHierarchyLevel', kind: 'access', intent: 'docs', why: 'defaultRoleManager.ts:57-71 hasRole follows links to depth maxHierarchyLevel: recursion over the graph'},
    {name: 'deleting the last path revokes the inherited role', kind: 'access', intent: 'inferred', why: 'the purpose of deleteLink; needs reachability over the graph'},
    {name: 'no inheritance deeper than maxHierarchyLevel', kind: 'safety', intent: 'docs', why: 'defaultRoleManager.ts:135 "the maximized allowed RBAC hierarchy level"'},
  ],
}

export const items: RealItem[] = [effItem, rmItem]
