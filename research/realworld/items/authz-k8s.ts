// Kubernetes v1.37.1, the RBAC authorizer's rule check: RuleAllows (plugin/pkg/auth/authorizer/rbac/rbac.go) and the
// matchers it calls (pkg/apis/rbac/v1/evaluation_helpers.go). Apache-2.0, (c) The Kubernetes Authors.
// https://github.com/kubernetes/kubernetes/tree/f78e722310e50bcaca9276be22276d9e91d91308
//
// One PolicyRule and one request's attributes, a decision. Strings are interned as numbers, the same string always the
// same number: 0 is "" and 1 is "*". A rule's lists (Verbs, APIGroups, Resources, ResourceNames, NonResourceURLs) are
// read only by "some element equals", so each is the set of its elements, carried by the request.
import {bool, everyKey, lit, nat, rule} from '../../../core/dsl.ts'
import {type RealItem, decision} from '../lib.ts'

const src = {repo: 'kubernetes/kubernetes', commit: 'f78e722310e50bcaca9276be22276d9e91d91308', licence: 'Apache-2.0', author: 'The Kubernetes Authors', language: 'Go'}
const EMPTY = 0, STAR = 1

export const ruleAllows = () => rule('kubernetes RBAC RuleAllows')
  .inputs({
    // rbac.go:192 requestAttributes.IsResourceRequest(); GetVerb, GetAPIGroup, GetName, GetPath.
    isResource: bool, verb: nat, group: nat, name: nat, path: nat,
    // rbac.go:193-196 combinedResource: GetResource(), or GetResource() + "/" + GetSubresource() when there is one
    // (`hasSub`); `starSub` is "*/" + GetSubresource() (evaluation_helpers.go:69-71: a rule resource of length
    // len(sub) + 2 that starts with "*/" and ends with sub is exactly that string). The encoder interns both.
    combined: nat, hasSub: bool, starSub: nat,
    // evaluation_helpers.go:102 some rule URL ends in "*" and the path starts with it, the "*" trimmed (see gaps).
    prefixHit: bool,
  })
  // The rule: rbacv1.PolicyRule's lists, as sets.
  .carries('Verbs', 'Groups', 'Resources', 'Names', 'URLs')
  .assume(({Verbs, Groups, Resources, Names, URLs}) => everyKey(k => Verbs.at(k).atMost(1).and(Groups.at(k).atMost(1), Resources.at(k).atMost(1), Names.at(k).atMost(1), URLs.at(k).atMost(1))))

type Env = Parameters<Parameters<ReturnType<typeof ruleAllows>['decide']>[1]>[0]
// rbac.go:191-206, the matchers inline.
export const allows = ({isResource, verb, group, name, path, combined, hasSub, starSub, prefixHit, Verbs, Groups, Resources, Names, URLs}: Env) => {
  // evaluation_helpers.go:26-37 VerbMatches, :39-50 APIGroupMatches: "*" or the requested value.
  const verbOk = Verbs.has(STAR).or(Verbs.has(verb)), groupOk = Groups.has(STAR).or(Groups.has(group))
  // :52-78 ResourceMatches: "*", the combined resource, or (with a subresource) "*/<subresource>".
  const resourceOk = Resources.has(STAR).or(Resources.has(combined), hasSub.and(Resources.has(starSub)))
  // :80-92 ResourceNameMatches: no names means every name.
  const nameOk = everyKey(k => Names.at(k).eq(0)).or(Names.has(name))
  // :94-108 NonResourceURLMatches: "*", the path, or a "prefix*".
  const urlOk = URLs.has(STAR).or(URLs.has(path), prefixHit)
  return isResource.and(verbOk, groupOk, resourceOk, nameOk).or(isResource.not().and(verbOk, urlOk))
}

const r = ruleAllows()
export const items: RealItem[] = [{
  id: 'access/kubernetes/rbacRuleAllows',
  domain: 'access',
  source: {...src, path: 'plugin/pkg/auth/authorizer/rbac/rbac.go', lines: '181-206', export: 'RuleAllows'},
  also: [{...src, path: 'pkg/apis/rbac/v1/evaluation_helpers.go', lines: '26-108', export: 'VerbMatches, APIGroupMatches, ResourceMatches, ResourceNameMatches, NonResourceURLMatches'}],
  summary: 'Whether one RBAC PolicyRule allows a request: verb, API group, resource (with "*" and "*/subresource" wildcards) and resource name for a resource request, verb and URL (with "prefix*") otherwise.',
  expressible: 'partial',
  gaps: [
    {gap: 'string', blocks: 'part', detail: 'NonResourceURLMatches\' "prefix*" rule (evaluation_helpers.go:102, strings.HasSuffix / HasPrefix / TrimRight) is a yes/no the request carries (`prefixHit`); the resource-side strings are interned (resource + "/" + subresource, "*/" + subresource), which is exact'},
    {gap: 'unbounded-collection', blocks: 'law', detail: 'RulesAllow (rbac.go:181-189) and the authorizer\'s visitor (:66-76) range over every rule of every binding of the user: a list of rules each with its own lists, which the rule (one PolicyRule) does not hold',
      laws: ['adding a rule never removes access', 'no rule, no access']},
  ],
  laws: [
    decision(r.decide('without the verb or "*", a rule allows nothing', ({verb, Verbs}) => [Verbs.has(verb).not(), Verbs.has(STAR).not()], e => allows(e).not()),
      'access', 'docs', 'evaluation_helpers.go:26-37 VerbMatches; RBAC docs: a rule grants only the verbs it lists'),
    // Stated first without `Names.has(EMPTY).not()`, this law was refuted: a rule whose ResourceNames lists "" allows an
    // unnamed request (create pods, confirmed on the original code by repro/k8s-rulenames.sh). The whitelist matches
    // the empty name like any other; the docs' claim is about rules that name real resources (a law error).
    decision(r.decide('a rule naming only non-empty resources never allows an unnamed request', ({isResource, name, Names}) => [isResource, name.eq(EMPTY), everyKey(k => Names.at(k).eq(0)).not(), Names.has(EMPTY).not()], e => allows(e).not()),
      'access', 'docs', 'RBAC docs "You cannot restrict create or deletecollection requests by their resource name"'),
    decision(r.decide('"*" everywhere and no names allows every resource request', ({isResource, Verbs, Groups, Resources, Names}) => [isResource, Verbs.has(STAR), Groups.has(STAR), Resources.has(STAR), everyKey(k => Names.at(k).eq(0))], e => allows(e)),
      'access', 'docs', 'rbacv1 VerbAll / APIGroupAll / ResourceAll "*"; ResourceNames "An empty set means that everything is allowed"'),
    decision(r.decide('a non-resource request needs a matching URL', ({isResource, path, prefixHit, URLs}) => [isResource.not(), URLs.has(STAR).not(), URLs.has(path).not(), prefixHit.not()], e => allows(e).not()),
      'access', 'docs', 'rbac.go:204-205 a non-resource request is checked by NonResourceURLMatches only'),
    decision(r.decide('a subresource needs its own grant', ({isResource, hasSub, combined, starSub, Resources}) => [isResource, hasSub, Resources.has(STAR).not(), Resources.has(combined).not(), Resources.has(starSub).not()], e => allows(e).not()),
      'access', 'docs', 'RBAC docs: "pods/log" must be listed for the log subresource; "pods" alone does not grant it'),
    // Noninterference of the name, in one request: the decision is the one for the same request with no name. (As a
    // relate over two requests, each with its five sets, it was proven too, in 120 s.)
    decision(r.decide('with no resource names, the name never matters', ({Names}) => everyKey(k => Names.at(k).eq(0)), e => allows(e).iff(allows({...e, name: lit(EMPTY)}))),
      'access', 'docs', 'rbacv1 PolicyRule.ResourceNames "An empty set means that everything is allowed"'),
  ],
  unstated: [
    {name: 'adding a rule never removes access', kind: 'access', intent: 'inferred', why: 'rbac.go:66-76 the visitor allows on the first rule that allows: RBAC is purely additive'},
    {name: 'no rule, no access', kind: 'access', intent: 'docs', why: 'rbac.go:127 DecisionNoOpinion when no rule allows; RBAC docs "there are no deny rules"'},
  ],
}]
