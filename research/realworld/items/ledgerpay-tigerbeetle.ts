// TigerBeetle 0.17.9, the state machine's accounts and transfers: single-phase transfers, two-phase (pending, then
// posted, voided or expired), balancing and closing transfers, the debits/credits limit flags and the u128 overflow
// checks. Apache-2.0, (c) TigerBeetle, Inc.
// https://github.com/tigerbeetle/tigerbeetle/blob/cc1c06a924e49b11089c521b2209d34c92caaf18/src/state_machine.zig
//
// One request is one event of a create_accounts or create_transfers batch, or the expiry of one pending transfer whose
// timeout has passed (execute_expire_pending_transfers expires every due one, each at its own timestamp: a run of
// these requests). An event that returns an error result changes nothing, except that a transfer failing with a
// transient error (tigerbeetle.zig:322-333) has its id kept as orphaned (state_machine.zig:3215-3249), so the id can
// never be used again. `now` is the event's timestamp, sent in (the replica's prepare timestamp, strictly increasing:
// a request at or before the last commit is not one the state machine is given).
import {type Bool, type Choice, type Term, bool, forall, max as larger, nat, no, oneOf, record, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'tigerbeetle/tigerbeetle', commit: 'cc1c06a924e49b11089c521b2209d34c92caaf18', licence: 'Apache-2.0', author: 'TigerBeetle, Inc.', language: 'Zig'}
const NS = 1_000_000_000 // std.time.ns_per_s, Transfer.timeout_ns (tigerbeetle.zig:104-108)
// tigerbeetle.zig:10-31 Account (the fields the state machine reads); `exists`: the account is in the groove.
const Account = record({exists: bool, ledger: nat, dnec: bool, cned: bool, closed: bool, dp: nat, dpo: nat, cp: nat, cpo: nat})
// tigerbeetle.zig:83-103 Transfer; `kind`: absent, an orphaned id (state_machine.zig:3248), a single-phase transfer,
// a pending one, or one that posted or voided another.
const Transfer = record({kind: oneOf('none', 'orphan', 'single', 'pending', 'postvoid'), dr: nat, cr: nat, amount: nat, ledger: nat, code: nat, timeout: nat, ts: nat, closeD: bool, closeC: bool})

export const tigerbeetle = () => rule('TigerBeetle accounts and transfers')
  // `max`: math.maxInt(u128); `tmax`: maxInt(u63), the timestamp bound (:3920-3934); `d`: the pending transfer a
  // liveness law watches (not the code's).
  .params({max: nat, tmax: nat, d: nat})
  // An event: an account to create (`id`, `ledger`, `code`, its flags) or a transfer (`id`, `dr`, `cr`, `amount`,
  // `pid` = pending_id, `timeout`, `ledger`, `code`, its flags), or `expire` the pending transfer `id`. user_data is
  // copied and never read; `reserved`, `padding` and the balances of a new account are taken as 0, as clients send them.
  .inputs({op: oneOf('account', 'transfer', 'expire'), id: nat, now: nat, dr: nat, cr: nat, amount: nat, pid: nat, timeout: nat, ledger: nat, code: nat,
    dnec: bool, cned: bool, closed: bool, pending: bool, post: bool, void: bool, balD: bool, balC: bool, closeD: bool, closeC: bool})
  .assume(({id, dr, cr, amount, pid, timeout, now, max, tmax}) => id.atMost(max).and(dr.atMost(max), cr.atMost(max), amount.atMost(max), pid.atMost(max), timeout.lt(2 ** 32), now.atMost(tmax)))
  // `commit`: self.commit_timestamp. Ghosts (not TigerBeetle's): the sums over every account of debits_pending,
  // credits_pending, debits_posted and credits_posted, changed by what each event adds to and takes from them.
  .state({commit: 0, tdp: 0, tcp: 0, tdpo: 0, tcpo: 0})
  // The accounts groove, the transfers groove, and transfers_pending (each pending transfer's status, by its id: the
  // code keys it by the pending transfer's timestamp, one to one).
  .maps({A: Account.from({exists: false, ledger: 0, dnec: false, cned: false, closed: false, dp: 0, dpo: 0, cp: 0, cpo: 0}),
    T: Transfer.from({kind: 'none', dr: 0, cr: 0, amount: 0, ledger: 0, code: 0, timeout: 0, ts: 0, closeD: false, closeC: false}),
    Status: oneOf('none', 'pending', 'posted', 'voided', 'expired').from('none')})
  .flags(({op, id, now, dr, cr, amount, pid, timeout, ledger, code, dnec, cned, pending, post, void: voids, balD, balC, closeD, closeC, max, tmax, commit, A, T, Status}) => {
    const fresh = now.gt(commit)
    // create_account (:3613-3689): an id of 0 or maxInt, an existing id (:3627-3629, create_account_exists: no
    // change), both limit flags (:3637-3639), a zero ledger or code: no account.
    const accounts = op.is('account').and(fresh, id.gt(0), id.lt(max), A.at(id).exists.not(), dnec.and(cned).not(), ledger.gt(0), code.gt(0))
    // create_transfer (:3719-3986), up to the branch to post_or_void (:3745-3747): the id checks and the groove lookup
    // (:3729-3739: found is create_transfer_exists, no change; orphaned is id_already_failed).
    const tr = op.is('transfer').and(fresh, id.gt(0), id.lt(max), T.at(id).kind.is('none'))
    const pv = post.or(voids)
    // :3749-3765, every check before the accounts are read: none of them transient.
    const single = tr.and(pv.not(), dr.gt(0), dr.lt(max), cr.gt(0), cr.lt(max), cr.eq(dr).not(), pid.eq(0),
      pending.or(timeout.eq(0).and(closeD.not(), closeC.not())), ledger.gt(0), code.gt(0))
    const da = A.at(dr), ca = A.at(cr)
    // :3771-3792 an account not found: transient.
    const found = da.exists.and(ca.exists)
    // :3796-3799 the ledgers; :3838-3839 a closed account: transient.
    const sameLedger = da.ledger.eq(ca.ledger).and(ledger.eq(da.ledger)), open = da.closed.not().and(ca.closed.not())
    // :3841-3853 amount_actual: a balancing transfer moves at most what balances the account (`-|`: saturating).
    const amt = balanced(amount, balD, balC, da, ca)
    // :3855-3893 the u128 overflow checks (a pending transfer's pending sums too); :3900-3911 the timeout's.
    const fits = pending.implies(amt.plus(da.dp).atMost(max).and(amt.plus(ca.cp).atMost(max)))
      .and(amt.plus(da.dpo).atMost(max), amt.plus(ca.cpo).atMost(max), amt.plus(da.dp).plus(da.dpo).atMost(max), amt.plus(ca.cp).plus(ca.cpo).atMost(max), now.plus(timeout.times(NS)).atMost(tmax))
    // :3913-3914, Account.debits_exceed_credits / credits_exceed_debits (tigerbeetle.zig:34-42): transient.
    const limits = da.dnec.implies(da.dp.plus(da.dpo).plus(amt).atMost(da.cpo)).and(ca.cned.implies(ca.cp.plus(ca.cpo).plus(amt).atMost(ca.dpo)))
    const creates = single.and(found, sameLedger, open, fits, limits)
    // post_or_void_pending_transfer (:4053-4299): the flag and field checks (:4066-4079), then the pending transfer
    // (:4081-4090: not found is transient).
    const p = T.at(pid)
    const pvShape = tr.and(pv, post.and(voids).not(), pending.not(), balD.not(), balC.not(), closeD.not(), closeC.not(), pid.gt(0), pid.lt(max), pid.eq(id).not(), timeout.eq(0))
    const pFound = p.kind.is('pending').or(p.kind.is('single')).or(p.kind.is('postvoid'))
    // :4091 not a pending transfer; :4101-4114 a different debit or credit account, ledger or code than given.
    const pMatches = p.kind.is('pending').and(dr.eq(0).or(dr.eq(p.dr)), cr.eq(0).or(cr.eq(p.cr)), ledger.eq(0).or(ledger.eq(p.ledger)), code.eq(0).or(code.eq(p.code)))
    // :4118-4131 amount_actual: a void of 0 voids the whole amount, a post of maxInt posts it; more than the pending
    // amount, or a void of less, is refused.
    const pAmt = postAmount(amount, voids, max, p.amount)
    const pAmount = pAmt.atMost(p.amount).and(voids.implies(pAmt.atLeast(p.amount)))
    // :4133-4158 already posted, voided or expired; :4160-4171 a timeout that has passed (expired).
    const pLive = Status.at(pid).is('pending').and(p.timeout.eq(0).or(now.lt(p.ts.plus(p.timeout.times(NS)))))
    // :4208-4214 "The only movement allowed in a closed account is voiding a pending transfer" (transient).
    const pOpen = voids.or(A.at(p.dr).closed.not().and(A.at(p.cr).closed.not()))
    const resolves = pvShape.and(pFound, pMatches, pAmount, pLive, pOpen)
    // tigerbeetle.zig:322-333 the transient errors, which orphan the id: an account not found, a closed account or
    // the limits for a transfer; the pending transfer not found, or a closed account, for a post or void.
    const orphans = single.and(found.not().or(found.and(sameLedger, open.not().or(fits.and(limits.not())))))
      .or(pvShape.and(pFound.not().or(pFound.and(pMatches, pAmount, pLive, pOpen.not()))))
    // execute_expire_pending_transfers (:4511-4620): a pending transfer with a timeout, due (:4548-4549), still pending (:4596).
    const e = T.at(id)
    const expires = op.is('expire').and(fresh, e.kind.is('pending'), e.timeout.gt(0), Status.at(id).is('pending'), e.ts.plus(e.timeout.times(NS)).atMost(now))
    return {accounts, creates, resolves, orphans, expires}
  })
  .step(({op, id, now, dr, cr, amount, pid, timeout, ledger, code, dnec, cned, closed, pending, post, void: voids, balD, balC, closeD, closeC, max,
    commit, tdp, tcp, tdpo, tcpo, A, T, Status, accounts, creates, resolves, orphans, expires}) => {
    const amt = balanced(amount, balD, balC, A.at(dr), A.at(cr))
    // The pending transfer a post, void or expiry resolves, and the amount it posts.
    // (The keys read only the request: a flag inside a map's key stops the kernel, `unknown flag`.)
    const resolving = op.is('transfer').and(post.or(voids)), p = T.at(when(resolving, pid, id))
    // amount_actual of a post or void (:4118-4124); what a post moves to the posted side (a void and an expiry: none).
    const pAmt = postAmount(amount, voids, max, p.amount), posts = when(resolves.and(voids.not()), pAmt, 0)
    const ends = resolves.or(expires)
    // :3955-3982 a created transfer adds amount_actual to the pending or posted sides; :4246-4261 a post or void takes
    // the whole pending amount off and posts amount_actual; :4559-4571 an expiry takes it off.
    const addP = when(creates.and(pending), amt, 0), addPo = when(creates.and(pending.not()), amt, 0).plus(posts)
    const offP = when(ends, p.amount, 0)
    return {
      commit: when(accounts.or(creates, resolves, expires), now, commit),
      A: A.each(k => {
        const a = A.at(k), mk = accounts.and(k.eq(id)), mv = creates.or(ends)
        const isD = when(ends, k.eq(p.dr), k.eq(dr)), isC = when(ends, k.eq(p.cr), k.eq(cr))
        // create_account (:3665-3680): a new account with zero balances and the flags given.
        return {
          exists: mk.or(a.exists), ledger: when(mk, ledger, a.ledger), dnec: when(mk, dnec, a.dnec), cned: when(mk, cned, a.cned),
          // :3967-3970 a closing transfer closes its account; :4264-4273, :4573-4580 voiding or expiring it reopens it.
          closed: when(mk, closed, when(mv.and(isD.and(creates, closeD).or(isC.and(creates, closeC))), yes,
            when(mv.and(isD.and(ends, voids.or(expires), p.closeD).or(isC.and(ends, voids.or(expires), p.closeC))), no, a.closed))),
          dp: when(mk, 0, when(mv.and(isD), a.dp.plus(addP).minus(offP), a.dp)), dpo: when(mk, 0, when(mv.and(isD), a.dpo.plus(addPo), a.dpo)),
          cp: when(mk, 0, when(mv.and(isC), a.cp.plus(addP).minus(offP), a.cp)), cpo: when(mk, 0, when(mv.and(isC), a.cpo.plus(addPo), a.cpo)),
        }
      }),
      // :3940-3954 the transfer inserted; :4216-4230 the post or void inserted; :3248 an orphaned id.
      T: T.set(id, (() => {
        const t = T.at(id), ins = creates.or(resolves)
        return {
          kind: when(creates.and(pending), 'pending', when(creates, 'single', when(resolves, 'postvoid', when(orphans, 'orphan', t.kind)))),
          dr: when(ins, when(creates, dr, p.dr), t.dr), cr: when(ins, when(creates, cr, p.cr), t.cr), amount: when(ins, when(creates, amt, pAmt), t.amount),
          ledger: when(ins, when(creates, ledger, p.ledger), t.ledger), code: when(ins, when(creates, code, p.code), t.code),
          timeout: when(ins, when(creates, timeout, 0), t.timeout), ts: when(ins, now, t.ts),
          closeD: when(ins, creates.and(closeD), t.closeD), closeC: when(ins, creates.and(closeC), t.closeC),
        }
      })()),
      // :3962-3965 a pending transfer is pending; :4237-4244 posted or voided; :4596-4597 expired.
      Status: (() => {
        const key = when(resolving, pid, id)
        return Status.set(key, when(creates.and(pending), 'pending', when(resolves.and(voids), 'voided', when(resolves, 'posted', when(expires, 'expired', Status.at(key))))))
      })(),
      tdp: tdp.plus(addP).minus(offP), tcp: tcp.plus(addP).minus(offP), tdpo: tdpo.plus(addPo), tcpo: tcpo.plus(addPo),
    }
  })

// :3841-3853 amount_actual of a balancing transfer.
type Acct = {dp: Term, dpo: Term, cp: Term, cpo: Term}
function balanced(amount: Term, balD: Bool, balC: Bool, da: Acct, ca: Acct) {
  const a1 = when(balD, lesser(amount, da.cpo.minus(da.dpo.plus(da.dp))), amount)
  return when(balC, lesser(a1, ca.dpo.minus(ca.cpo.plus(ca.cp))), a1)
}
// :4118-4124: a void of 0 is the pending amount; a post of maxInt is the pending amount.
function postAmount(amount: Term, voids: Bool, max: Term, pending: Term) {
  return when(voids, when(amount.eq(0), pending, amount), when(amount.eq(max), pending, amount))
}
const lesser = (a: Term, b: Term) => when(a.atMost(b), a, b)

const r = tigerbeetle()
const sm = (lines: string, exp: string) => ({...src, path: 'src/state_machine.zig', lines, export: exp})
export const items: RealItem[] = [{
  id: 'ledger/tigerbeetle/transfers',
  domain: 'ledger',
  source: sm('3613-4299', 'StateMachine.create_account, create_transfer, post_or_void_pending_transfer'),
  also: [sm('4511-4620', 'StateMachine.execute_expire_pending_transfers'), sm('3215-3249', 'StateMachine.transient_error'),
    {...src, path: 'src/tigerbeetle.zig', lines: '10-148', export: 'Account, AccountFlags, Transfer, TransferFlags'},
    {...src, path: 'src/tigerbeetle.zig', lines: '320-397', export: 'CreateTransferStatus.transient'}],
  summary: 'Accounts with pending and posted debits and credits; transfers posted at once or held pending and later posted (up to the held amount), voided or expired, each at most once, under the limit flags and the u128 overflow checks.',
  expressible: 'partial',
  gaps: [
    {gap: 'batch', blocks: 'part', detail: 'linked chains (flags.linked: a chain of events succeeding or failing together, rolled back on error) are not modelled: each event is its own request'},
    {gap: 'scope', blocks: 'part', detail: 'imported events (flags.imported: user-supplied timestamps, with their own checks) are not modelled'},
    {gap: 'batch', blocks: 'part', detail: 'the expiry pulse expires every due pending transfer in one operation; the rule expires one per request, which covers every order but also lets other events run between them'},
  ],
  laws: [
    invariant(r, r.law('an account that forbids it never has more debits than credits', ({A}) => forall(k => A.at(k).dnec.implies(A.at(k).dp.plus(A.at(k).dpo).atMost(A.at(k).cpo)))),
      'safety', 'docs', 'tigerbeetle.zig:34-37 debits_exceed_credits: `debits_pending + debits_posted + amount > credits_posted` is refused'),
    invariant(r, r.law('an account that forbids it never has more credits than debits', ({A}) => forall(k => A.at(k).cned.implies(A.at(k).cp.plus(A.at(k).cpo).atMost(A.at(k).dpo)))),
      'safety', 'docs', 'tigerbeetle.zig:39-42 credits_exceed_debits'),
    invariant(r, r.law('posted debits equal posted credits', ({tdpo, tcpo}) => tdpo.eq(tcpo)),
      'safety', 'inferred', 'double entry: every transfer posts the same amount to a debit and a credit account (:3955-3960, :4253-4257)'),
    invariant(r, r.law('pending debits equal pending credits', ({tdp, tcp}) => tdp.eq(tcp)),
      'safety', 'inferred', 'every pending transfer holds the same amount on both sides (:3955-3958), and releases it from both (:4246-4247, :4559-4560)'),
    stepLaw(r, r.stepLaw('a pending transfer is resolved at most once', ({Status}, after) => forall(k => Status.at(k).is('posted').or(Status.at(k).is('voided'), Status.at(k).is('expired')).implies(same3(after.Status.at(k), Status.at(k))))),
      'step', 'docs', 'state_machine.zig:4133-4148 pending_transfer_already_posted, pending_transfer_already_voided, pending_transfer_expired'),
    stepLaw(r, r.stepLaw('a post never posts more than was pending', ({tdpo, T, pid}, after) => after.tdpo.atMost(tdpo.plus(T.at(pid).amount)), ({resolves, post}) => resolves.and(post)),
      'step', 'docs', 'state_machine.zig:4126 exceeds_pending_transfer_amount'),
    stepLaw(r, r.stepLaw('only voiding or expiry moves a closed account', ({A}, after) => forall(k => A.at(k).closed.implies(after.A.at(k).dpo.eq(A.at(k).dpo).and(after.A.at(k).cpo.eq(A.at(k).cpo), after.A.at(k).dp.atMost(A.at(k).dp), after.A.at(k).cp.atMost(A.at(k).cp))))),
      'step', 'docs', 'state_machine.zig:4208 "The only movement allowed in a closed account is voiding a pending transfer"; :4582 "Pending transfers can expire in closed accounts"'),
    leadsTo(r, r.leadsTo('a pending transfer with a timeout is resolved in the end', {
      from: ({Status, T, d}) => Status.at(d).is('pending').and(T.at(d).kind.is('pending'), T.at(d).timeout.gt(0)),
      to: ({Status, d}) => Status.at(d).is('pending').not(),
      helpful: ({T, d, commit}) => ({op: 2, id: d, now: larger(commit.plus(1), T.at(d).ts.plus(T.at(d).timeout.times(NS)))}),
    }), 'docs', 'tigerbeetle.zig:98-99 "Timeout in seconds for pending transfers to expire automatically if not manually posted or voided"; fair: the expiry pulse runs'),
  ],
}]
function same3(a: Choice<'none' | 'pending' | 'posted' | 'voided' | 'expired'>, b: Choice<'none' | 'pending' | 'posted' | 'voided' | 'expired'>) {
  return a.is('posted').and(b.is('posted')).or(a.is('voided').and(b.is('voided')), a.is('expired').and(b.is('expired')))
}
