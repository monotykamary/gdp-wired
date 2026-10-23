// cedar-examples, the Document Cloud use case: a Google-Drive-like policy set (policies.cedar), with its schema
// (policies.cedarschema) and the README that states what it should do. Apache-2.0, (c) Cedar contributors.
// https://github.com/cedar-policy/cedar-examples/tree/268c5618eb145052c21f07c2e14e1781482a23e9/cedar-example-use-cases/document_cloud
//
// Cedar's decision: Allow when some permit is satisfied and no forbid is (Cedar's authorization semantics); a policy
// whose condition errors is not satisfied. Requests are taken schema-valid (policies.cedarschema: each action's
// principal and resource types), so no condition here errors. The entity store's facts a request reads are inputs:
// `principal in resource.viewACL` (Cedar's `in`: the entity hierarchy, reflexive and transitive), the blocked sets'
// `contains`, and the attributes of the resource. Entity ids are numbers.
import {bool, nat, oneOf, rule} from '../../../core/dsl.ts'
import {type RealItem, decision} from '../lib.ts'

const src = {repo: 'cedar-policy/cedar-examples', commit: '268c5618eb145052c21f07c2e14e1781482a23e9', licence: 'Apache-2.0', author: 'Cedar contributors (Amazon)'}
const dir = 'cedar-example-use-cases/document_cloud'

const Action = oneOf('CreateDocument', 'ViewDocument', 'DeleteDocument', 'ModifyDocument', 'EditIsPrivate', 'AddToShareACL', 'EditPublicAccess', 'CreateGroup', 'ModifyGroup', 'DeleteGroup')
export const documentCloud = () => rule('cedar document cloud')
  .inputs({
    action: Action,
    // principal: Public::"public" (isPublic) or User::pid.
    isPublic: bool, pid: nat,
    // resource: Drive (CreateDocument, CreateGroup), Group (ModifyGroup, DeleteGroup), or Document (the rest), per the
    // schema. `theDrive`: resource == Drive::"drive". `owner`: resource.owner (Document and Group).
    theDrive: bool, owner: nat,
    // Document attributes: isPrivate, publicAccess (a String; the README names none, view, edit).
    isPrivate: bool, publicAccess: oneOf('none', 'view', 'edit', 'other'),
    // principal in resource.viewACL / modifyACL / manageACL (the entity hierarchy, from the store).
    inView: bool, inModify: bool, inManage: bool,
    // resource.owner.blocked.contains(principal), principal.blocked.contains(resource.owner).
    ownerBlocksP: bool, pBlocksOwner: bool,
    // context.is_authenticated.
    authenticated: bool,
  })
  // policies.cedarschema: only ViewDocument takes the Public principal; every other action takes a User.
  .assume(({isPublic, action}) => isPublic.implies(action.is('ViewDocument')))

type Env = Parameters<Parameters<ReturnType<typeof documentCloud>['decide']>[1]>[0]
const onDoc = ({action}: Env) => action.is('CreateDocument').or(action.is('CreateGroup'), action.is('ModifyGroup'), action.is('DeleteGroup')).not()
// `principal == resource.owner`: a User whose id is the owner (Public is never a User).
const isOwner = ({isPublic, pid, owner}: Env) => isPublic.not().and(pid.eq(owner))
const permits = (e: Env) => {
  const {action: a, isPublic, theDrive, isPrivate, publicAccess, inView, inModify, inManage} = e
  return [
    a.is('CreateDocument').and(theDrive), // policies.cedar:1-5
    a.is('ViewDocument').and(isOwner(e)), // :7-12 (and again :30-35)
    a.is('ViewDocument').and(inView, isPrivate.not()), // :14-20
    isPublic.and(a.is('ViewDocument'), publicAccess.is('view').or(publicAccess.is('edit')), isPrivate.not()), // :22-28
    a.is('ModifyDocument').and(isOwner(e)), // :37-42
    a.is('ModifyDocument').and(inModify, isPrivate.not()), // :44-50
    isPublic.and(a.is('ViewDocument'), publicAccess.is('edit'), isPrivate.not()), // :52-58
    a.is('EditIsPrivate').or(a.is('AddToShareACL'), a.is('EditPublicAccess')).and(isOwner(e)), // :60-68
    a.is('AddToShareACL').or(a.is('EditPublicAccess')).and(inManage), // :70-75
    a.is('CreateGroup').and(theDrive), // :77-81
    a.is('ModifyGroup').or(a.is('DeleteGroup')).and(isOwner(e)), // :83-88
  ]
}
const forbids = (e: Env) => {
  const {action: a, isPublic, ownerBlocksP, pBlocksOwner, authenticated, isPrivate} = e
  return [
    // :90-106 `principal has blocked` (Users have it, Public does not).
    a.is('ViewDocument').or(a.is('ModifyDocument'), a.is('EditIsPrivate'), a.is('AddToShareACL'), a.is('EditPublicAccess'), a.is('DeleteDocument'))
      .and(isPublic.not(), ownerBlocksP.or(pBlocksOwner)),
    authenticated.not(), // :108-109
    // :111-118 `resource has owner && principal != resource.owner && resource has isPrivate && resource.isPrivate`: only
    // a Document has isPrivate.
    onDoc(e).and(isOwner(e).not(), isPrivate),
  ]
}
const anyOf = (cs: ReturnType<typeof permits>) => cs.reduce((x, y) => x.or(y))
export const allows = (e: Env) => anyOf(permits(e)).and(anyOf(forbids(e)).not())

const r = documentCloud()
const okUser = (e: Env) => [e.authenticated, e.ownerBlocksP.not(), e.pBlocksOwner.not()]
export const items: RealItem[] = [{
  id: 'access/cedar-examples/documentCloud',
  domain: 'access',
  source: {...src, path: `${dir}/policies.cedar`, lines: '1-118', export: 'policies.cedar', language: 'Cedar'},
  also: [{...src, path: `${dir}/policies.cedarschema`, lines: '1-63', export: 'schema', language: 'Cedar'}, {...src, path: `${dir}/README.md`, lines: '1-260', export: 'README', language: 'Markdown'}],
  summary: 'A document-sharing policy set: owners, view/modify/manage ACLs, public access, blocklists, a private-document guard rail and an authentication forbid; allowed when a permit holds and no forbid does.',
  expressible: 'partial',
  gaps: [
    {gap: 'recursion', blocks: 'part', detail: 'Cedar\'s `principal in resource.viewACL` (and modifyACL, manageACL) is ancestry in the entity hierarchy, reflexive and transitive to any depth (User in Group in DocumentShare); the rule takes each as a yes/no the entity store supplies, so laws about group membership (a member of a shared group may view) are unstated',
      laws: ['a member of a group in the view ACL can view a non-private document']},
    {gap: 'dynamic-policy', blocks: 'part', detail: 'the policy set is Cedar text the Cedar engine evaluates; the rule is a hand translation of this file under Cedar\'s permit/forbid semantics (schema-valid requests, so no condition errors), not of the engine'},
  ],
  laws: [
    decision(r.decide('an unauthenticated request is always denied', ({authenticated}) => authenticated.not(), e => allows(e).not()),
      'safety', 'docs', 'README "This forbid policy requires that requests contain a valid authentication context"'),
    decision(r.decide('only the owner can delete a document', e => [e.action.is('DeleteDocument'), allows(e)], e => isOwner(e)),
      'access', 'docs', 'README "DeleteDocument: Only the owner should be able do this."'),
    decision(r.decide('the owner can delete their document', e => [e.action.is('DeleteDocument'), isOwner(e), ...okUser(e)], e => allows(e)),
      'access', 'docs', 'README "Users need to be able upload, delete, and modify the sharing permissions on their documents"; "Delete Document: ... only the owner can do this"'),
    decision(r.decide('a private document is open to its owner only', e => [onDoc(e), e.isPrivate, allows(e)], e => isOwner(e)),
      'access', 'docs', 'README "Private: only the owner can view/edit/comment/delete the document"'),
    decision(r.decide('a blocked user never sees the blocker\'s documents', e => [e.action.is('ViewDocument'), e.isPublic.not(), e.ownerBlocksP], e => allows(e).not()),
      'access', 'docs', 'README "if Alice blocks Bob, then Bob should not be able to view any documents Alice owns"'),
    decision(r.decide('the owner can always view their document', e => [e.action.is('ViewDocument'), isOwner(e), ...okUser(e)], e => allows(e)),
      'access', 'docs', 'README "The owner should always be able to view the document."'),
    decision(r.decide('the owner never loses the right to share', e => [e.action.is('AddToShareACL'), isOwner(e), ...okUser(e)], e => allows(e)),
      'access', 'docs', 'README "AddToShareACL: ... The owner can never have their access be revoked."'),
    decision(r.decide('the public can view a public document', e => [e.action.is('ViewDocument'), e.isPublic, e.isPrivate.not(), e.publicAccess.is('view'), e.authenticated.not()], e => allows(e)),
      'access', 'docs', 'README "Public: A principal that represents an un-authenticated user"; "An un-authenticated principal can view only when explicitly permitted"'),
    decision(r.relate('the modify ACL never decides viewing', (a, b) => [a.action.is('ViewDocument'), b.action.is('ViewDocument'), a.isPublic.iff(b.isPublic), a.pid.eq(b.pid), a.owner.eq(b.owner), a.theDrive.iff(b.theDrive),
      a.isPrivate.iff(b.isPrivate), a.publicAccess.is('none').iff(b.publicAccess.is('none')), a.publicAccess.is('view').iff(b.publicAccess.is('view')), a.publicAccess.is('edit').iff(b.publicAccess.is('edit')),
      a.inView.iff(b.inView), a.inManage.iff(b.inManage), a.ownerBlocksP.iff(b.ownerBlocksP), a.pBlocksOwner.iff(b.pBlocksOwner), a.authenticated.iff(b.authenticated)], (a, b) => allows(a).iff(allows(b))),
      'access', 'inferred', 'README "ViewDocument: Must pass ACL check" (the view ACL, :14-20); modifyACL is read only by ModifyDocument (:44-50)'),
  ],
  unstated: [
    {name: 'a member of a group in the view ACL can view a non-private document', kind: 'access', intent: 'docs', why: 'README "Documents can be shared with entire Groups at once": needs Cedar\'s `in` over the hierarchy'},
  ],
}]

