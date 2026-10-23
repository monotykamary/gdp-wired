// Gitea v28.2.0, pull request reviews as protected branches count them (models/issues/review.go, models/issues/pull.go,
// services/pull/pull.go, services/pull/review.go). MIT, (c) The Gitea Authors.
// https://github.com/go-gitea/gitea/blob/829b49c1ae96015e345f9d2a0eb1ea7acd5f31e1/models/issues/review.go
//
// One pull request's review table: each row a reviewer's review (approve, reject, comment, a review request, or a
// pending review being written) with its official, dismissed and stale flags and the commit it was made on. A
// protected branch counts the approvals that are official and not dismissed (and, with IgnoreStaleApprovals, not
// stale) (pull.go:769-785 GetGrantedApprovalsCount). A function that returns an error inside db.WithTx / TxContext
// rolls back: nothing changes, which the step says as "every part keeps its value". Queries that pick one row (a
// reviewer's current pending review, their latest approve/reject/request review) are answered by the request: it
// carries the row, and `.assume` says it is the row the query returns. Line numbers are review.go's unless named.
import {type Term, bool, choose, everyKey, forall, maybe, nat, no, oneOf, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'go-gitea/gitea', commit: '829b49c1ae96015e345f9d2a0eb1ea7acd5f31e1', licence: 'MIT', author: 'The Gitea Authors', language: 'Go'}

const Type = oneOf('none', 'approve', 'reject', 'comment', 'request', 'pending') // 'none': no row (deleted, or not made)
export const reviews = () => rule('Gitea pull request reviews')
  // protected_branch.go:59-65 the branch rule's DismissStaleApprovals.
  .params({dismissStale: bool})
  // One call: SubmitReview (doer, type, content empty?, code comments?, commit, stale), a code comment starting a
  // pending review, AddReviewRequest / RemoveReviewRequest (doer = the reviewer), DeleteReview, DismissReview (admin),
  // or a push (services/pull/pull.go:456-475: `changed` when the diff to the merge base changed, `commit` the new head).
  // `isOff`: IsOfficialReviewer (:276-306, permissions and the branch rule's whitelist) for the doer, an input.
  // `cur`: the doer's pending review (GetCurrentReview, :430-449); `l1`, `l2`: their latest approve/reject/request row
  // before and after a deletion (GetReviewByIssueIDAndUserID, :588-606); `closed`: the pull is closed or merged.
  .inputs({op: oneOf('submit', 'comment', 'request', 'unrequest', 'delete', 'dismiss', 'push'), doer: nat, type: oneOf('approve', 'reject', 'comment'),
    empty: bool, hasComments: bool, commit: nat, stale: bool, isOff: bool, cur: maybe(nat), l1: maybe(nat), l2: maybe(nat), id: nat, dismiss: bool, changed: bool, closed: bool})
  .state({next: 0})
  // review.go:122-148 Review: reviewer_id, type, official, dismissed, stale, commit_id.
  .maps({By: 0, Ty: Type.from('none'), Off: bool.from(false), Dis: bool.from(false), Stale: bool.from(false), Commit: 0})
  .assume(({op, doer, cur, l1, l2, id, next, By, Ty}) => {
    const mine = (k: typeof id) => k.lt(next).and(By.at(k).eq(doer))
    const arr = (k: typeof id) => mine(k).and(Ty.at(k).is('approve').or(Ty.at(k).is('reject'), Ty.at(k).is('request')))
    // the latest arr row (the highest id), skipping `gone` (the row deleted just before the second query)
    const latest = (l: typeof l1, gone?: Term) => {
      const counts = (k: typeof id) => (gone ? arr(k).and(k.eq(gone).not()) : arr(k))
      return l.match({none: () => everyKey(k => counts(k).not()), some: x => counts(x).and(everyKey(k => x.lt(k).implies(counts(k).not())))})
    }
    const first = l1.match({none: () => next, some: x => x})
    return cur.match({none: () => everyKey(k => mine(k).and(Ty.at(k).is('pending')).not()), some: c => mine(c).and(Ty.at(c).is('pending'))})
      // after RemoveReviewRequest deletes l1, or DeleteReview deletes `id`
      .and(latest(l1), latest(l2, when(op.is('delete'), id, first)))
  })
  .flags(({op, type, empty, hasComments, cur, l1, id, dismiss, closed, Ty, Dis}) => {
    const ar = type.is('approve').or(type.is('reject'))
    const l1Request = l1.match({none: () => no, some: x => Ty.at(x).is('request')})
    return {
      // :469-521 SubmitReview: without a pending review, a non-approval needs content (ContentEmptyErr); with one, a
      // non-approval needs content or code comments.
      submits: op.is('submit').and(cur.match({none: () => type.is('approve').or(empty.not()), some: () => type.is('approve').or(hasComments, empty.not())})),
      fresh: cur.isNone,
      ar,
      // createCodeComment (services/pull/review.go) starts a pending review when the doer has none (CreateReview, Pending).
      starts: op.is('comment').and(cur.isNone),
      // :699-770 AddReviewRequest: skipped when the latest is already a request; refused on a closed or merged pull.
      requests: op.is('request').and(l1Request.not(), l1.isNone.or(closed.not())),
      // :772-806 RemoveReviewRequest: only when the latest is a request.
      unrequests: op.is('unrequest').and(l1Request),
      // :996-1048 DeleteReview: a request can't be deleted this way.
      deletes: op.is('delete').and(Ty.at(id).is('none').not(), Ty.at(id).is('request').not()),
      // :640-655 DismissReview: no-op unless the flag changes on an approve or reject review.
      dismisses: op.is('dismiss').and(Ty.at(id).is('approve').or(Ty.at(id).is('reject')), Dis.at(id).iff(dismiss).not()),
      pushes: op.is('push'),
    }
  })
  .step(({doer, type, commit, stale, isOff, cur, l1, l2, id, dismiss, changed, dismissStale, next, By, Ty, Off, Dis, Stale, Commit,
    submits, fresh, ar, starts, requests, unrequests, deletes, dismisses, pushes}) => {
    const mine = (k: typeof id) => By.at(k).eq(doer).and(k.lt(next))
    const insert = submits.and(fresh).or(starts, requests)
    const row = cur.match({none: () => next, some: c => c}) // the row a submission writes
    const l1v = l1.match({none: () => next, some: x => x}), l2v = l2.match({none: () => next, some: x => x})
    const gone = (k: typeof id) => unrequests.and(k.eq(l1v)).or(deletes.and(k.eq(id)))
    // restoreLatestOfficialReview (:808-822): RemoveReviewRequest when the reviewer is official (:792-799);
    // DeleteReview when the deleted review was official (:1040-1044).
    const restores = unrequests.and(isOff).or(deletes.and(Off.at(id))).and(l2.isSome)
    // UPDATE review SET official=false WHERE reviewer = doer: SubmitReview of an approve/reject (:488-491, :520-523),
    // AddReviewRequest of an official reviewer (:730-737).
    const clears = submits.and(ar).or(requests.and(isOff))
    // the type written: a request, a pending review, or the submitted type (`t` only types the choice: never taken)
    const put = (t: ReturnType<typeof Ty.at>) => when(requests, 'request', when(starts, 'pending', when(type.is('approve'), 'approve', when(type.is('reject'), 'reject', when(type.is('comment'), 'comment', t)))))
    return {
      next: when(insert, next.plus(1), next),
      By: By.each(k => when(insert.and(k.eq(next)), doer, By.at(k))),
      Ty: Ty.each(k => {
        const t = Ty.at(k)
        // :402-407 CreateReview (any type but pending) and :566-571 deletes the doer's review requests.
        const dropsRequest = submits.or(requests).and(mine(k), t.is('request'))
        return when(submits.and(k.eq(row)).or(insert.and(k.eq(next))), put(t), when(gone(k).or(dropsRequest), 'none', t))
      }),
      Off: Off.each(k => choose(submits.and(k.eq(row)), ar.and(isOff), choose(insert.and(k.eq(next)), requests.and(isOff),
        choose(restores.and(k.eq(l2v)), yes, choose(clears.and(mine(k)), no, Off.at(k)))))),
      // :408-415 CreateReview of an approve/reject dismisses the doer's approve/reject reviews; services/pull/review.go
      // :361-402 DismissApprovalReviews on a push that changed the diff when the rule dismisses stale approvals.
      Dis: Dis.each(k => {
        const t = Ty.at(k), arRow = t.is('approve').or(t.is('reject'))
        return choose(dismisses.and(k.eq(id)), dismiss,
          choose(submits.and(fresh, ar, mine(k), arRow), yes,
            choose(pushes.and(changed, dismissStale, t.is('approve')), yes, choose(insert.and(k.eq(next)), no, Dis.at(k)))))
      }),
      // :626-638 MarkReviewsAsStale on a changed diff, then MarkReviewsAsNotStale for the new head commit.
      Stale: Stale.each(k => choose(submits.and(k.eq(row)).or(insert.and(k.eq(next))), submits.and(stale),
        choose(pushes, choose(Commit.at(k).eq(commit), no, Stale.at(k).or(changed)), Stale.at(k)))),
      Commit: Commit.each(k => when(submits.and(k.eq(row)).or(insert.and(k.eq(next))), when(submits, commit, 0), Commit.at(k))),
    }
  })

const r = reviews()
const cite = (path: string, lines: string, exp: string) => ({...src, path, lines, export: exp})
export const items: RealItem[] = [{
  id: 'approval/gitea/reviews',
  domain: 'approval',
  source: cite('models/issues/review.go', '381-822', 'CreateReview, SubmitReview, MarkReviewsAsStale, MarkReviewsAsNotStale, DismissReview, AddReviewRequest, RemoveReviewRequest, restoreLatestOfficialReview'),
  also: [cite('models/issues/review.go', '996-1048', 'DeleteReview'), cite('models/issues/pull.go', '762-803', 'HasEnoughApprovals, GetGrantedApprovalsCount, MergeBlockedByRejectedReview'),
    cite('services/pull/pull.go', '456-475', 'push: MarkReviewsAsStale, DismissApprovalReviews'), cite('services/pull/review.go', '361-402', 'DismissApprovalReviews')],
  summary: 'Each reviewer\'s latest approve/reject review is the official one; a protected branch merges with RequiredApprovals official, undismissed approvals; new commits mark reviews stale and, by rule, dismiss approvals.',
  expressible: 'partial',
  gaps: [
    {gap: 'unbounded-collection', blocks: 'law', detail: 'the merge check counts rows of the review table (GetGrantedApprovalsCount: COUNT(*) where approve, official, not dismissed); a count over a map\'s cells is not a term, so "merges only with RequiredApprovals approvals" is not stated; the law that counted approvals are of distinct reviewers is', laws: ['a pull request merges only with at least RequiredApprovals approvals from distinct reviewers']},
    {gap: 'external', blocks: 'part', detail: 'IsOfficialReviewer (write access, the approvals whitelist, teams) is an input; team review requests, migrated reviews (original_author_id), RecalculateReviewsOfficial and the merge itself are left out'},
  ],
  laws: [
    invariant(r, r.law('two counted approvals are never by the same reviewer', ({next, By, Ty, Off, Dis}) => forall((i, j) => {
      const counts = (k: typeof i) => Ty.at(k).is('approve').and(Off.at(k), Dis.at(k).not())
      return i.lt(j).and(j.lt(next), counts(i), counts(j)).implies(By.at(i).eq(By.at(j)).not())
    })), 'safety', 'docs', 'review.go:486 "Only reviewers latest review of type approve and reject shall count as \\"official\\""; protected_branch.go:59 RequiredApprovals counts approvers'),
    stepLaw(r, r.stepLaw("after a reviewer approves or rejects, none of their other reviews counts", ({doer, cur, next, By}, after) => {
      const row = cur.match({none: () => next, some: c => c})
      return forall(k => k.eq(row).not().and(By.at(k).eq(doer), k.lt(next)).implies(after.Ty.at(k).is('approve').and(after.Off.at(k), after.Dis.at(k).not()).not()))
    }, ({submits, ar}) => submits.and(ar)),
    'step', 'docs', 'review.go:409-410 "make sure if the created review gets dismissed no old review surface"; :486-487'),
    stepLaw(r, r.stepLaw('with DismissStaleApprovals, a push that changes the diff leaves no approval counted', (_, after) =>
      forall(k => after.Ty.at(k).is('approve').and(after.Off.at(k), after.Dis.at(k).not()).not()),
    ({pushes, changed, dismissStale}) => pushes.and(changed, dismissStale)),
    'step', 'docs', 'services/pull/pull.go:462 "dismiss all approval reviews if protected branch rule item enabled"; review.go:384 "New commits pushed, approval review dismissed automatically"'),
    stepLaw(r, r.stepLaw('only approve and reject reviews are dismissed or undismissed', ({id, Ty, Dis}, after) => after.Dis.at(id).iff(Dis.at(id)).or(Ty.at(id).is('approve'), Ty.at(id).is('reject')),
      ({op}) => op.is('dismiss')),
    'step', 'docs', 'services/pull/review.go:411-413 "not need to dismiss this review because it\'s type is not Approve or change request"; review.go:641'),
  ],
  unstated: [{name: 'a pull request merges only with at least RequiredApprovals approvals from distinct reviewers', kind: 'access', intent: 'docs', why: 'pull.go:762-767 HasEnoughApprovals: GetGrantedApprovalsCount >= RequiredApprovals'}],
}]
