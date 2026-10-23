// Blnk v0.15.6, the balance arithmetic: transfers (UpdateBalances), inflight holds committed or voided, as
// applyTransactionToBalances applies them to a source and a destination balance. Apache-2.0, (c) Blnk Finance.
// https://github.com/blnkfinance/blnk/tree/36ecff3ec7f480c38689ad4e6fedc4b9f172a6ff
//
// One request is one applyTransactionToBalances call (transaction_execution.go:320-365) on the balances it names:
// status commit runs CommitInflightDebit on the source and CommitInflightCredit on the destination (:327-338), void
// the two rollbacks (:342-354), anything else UpdateBalances (:356-361). An error leaves both balances as they were
// (the caller persists nothing for a transaction that fails; the balances are loaded afresh for the next one). The
// amounts are PreciseAmount, big integers in the currency's smallest unit (Precision 1 in the test harness).
import {Int, bool, forall, int, nat, oneOf, record, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant} from '../lib.ts'

const src = {repo: 'blnkfinance/blnk', commit: '36ecff3ec7f480c38689ad4e6fedc4b9f172a6ff', licence: 'Apache-2.0', author: 'Blnk Finance', language: 'Go'}
// model/balance.go:24-40: Balance, CreditBalance, DebitBalance, InflightBalance, InflightCreditBalance,
// InflightDebitBalance (big.Int, any sign).
const Balance = record({balance: int, credit: int, debit: int, ibalance: int, icredit: int, idebit: int})

export const blnk = () => rule('Blnk balances')
  // `status`: the transaction's status (commit, void, or another: apply); `src`, `dst`: the two balances' keys;
  // `amt`: PreciseAmount; `inflight`, `overdraft`: Inflight, AllowOverdraft; `limit`: the overdraft limit in precise
  // units (OverdraftLimit times Precision, rounded, model.go:186-191; 0: none).
  .inputs({status: oneOf('apply', 'commit', 'void'), src: nat, dst: nat, amt: nat, inflight: bool, overdraft: bool, limit: nat})
  // Ghosts (not Blnk's): the sums of each component over every balance, which the test harness recomputes after each
  // operation (invariant_fuzz_test.go:250-300); and per balance whether it ever sourced an unconditional overdraft and
  // the largest limit it sourced under (the harness's maxOverdraft, :125-130, :171-182).
  .ints({tC: 0, tD: 0, tIC: 0, tID: 0})
  .maps({B: Balance.from({balance: 0, credit: 0, debit: 0, ibalance: 0, icredit: 0, idebit: 0}), Unbounded: bool.from(false), MaxLimit: 0})
  .flags(({status, src, dst, amt, overdraft, limit, B}) => {
    const s = B.at(src), d = B.at(dst)
    return {
      // UpdateBalances (model.go:477-507): validate (:459-475) refuses an amount that isn't positive; then
      // canProcessTransaction (:153-207): an unconditional overdraft passes (:154-157); else `Balance -
      // InflightDebitBalance >= amount` passes (:165-177); else with a limit, `available - amount >= -limit` passes
      // (:180-201); else it fails. (QueuedDebitBalance is nil outside the queued checks, :170-174.)
      applies: status.is('apply').and(amt.gt(0), overdraft.and(limit.eq(0)).or(s.balance.minus(s.idebit).atLeast(amt),
        limit.gt(0).and(s.balance.minus(s.idebit).minus(amt).atLeast(Int.of(limit).negate())))),
      // CommitInflightDebit / CommitInflightCredit (:228-258), RollbackInflightDebit / RollbackInflightCredit
      // (:260-283): checkSufficientInflight* (:209-226) refuses more than is held. (A zero amount commits nothing:
      // ApplyPrecision falls back to Amount, 0.)
      commits: status.is('commit').and(s.idebit.atLeast(amt), d.icredit.atLeast(amt)),
      voids: status.is('void').and(s.idebit.atLeast(amt), d.icredit.atLeast(amt)),
    }
  })
  .step(({src, dst, amt, inflight, overdraft, limit, B, Unbounded, MaxLimit, tC, tD, tIC, tID, applies, commits, voids}) => {
    const a = Int.of(amt), zero = Int.of(0)
    const posted = applies.and(inflight.not()), held = applies.and(inflight)
    return {
      B: B.each(k => {
        const b = B.at(k), isS = k.eq(src), isD = k.eq(dst)
        // addDebit / addCredit (:117-138) on the source and the destination; the commits move a held amount to the
        // posted side (:236-238, :252-254), the rollbacks release it (:266, :277).
        const credit = b.credit.plus(when(posted.or(commits).and(isD), a, zero))
        const debit = b.debit.plus(when(posted.or(commits).and(isS), a, zero))
        const icredit = b.icredit.plus(when(held.and(isD), a, zero)).minus(when(commits.or(voids).and(isD), a, zero))
        const idebit = b.idebit.plus(when(held.and(isS), a, zero)).minus(when(commits.or(voids).and(isS), a, zero))
        const touched = isS.or(isD)
        // computeBalance (:140-151) recomputes the one it is asked for: the posted one after a posted transfer and a
        // commit, the inflight one after an inflight transfer, a commit and a rollback.
        return {
          credit, debit, icredit, idebit,
          balance: when(touched.and(posted.or(commits)), credit.minus(debit), b.balance),
          ibalance: when(touched.and(held.or(commits, voids)), icredit.minus(idebit), b.ibalance),
        }
      }),
      Unbounded: Unbounded.set(src, Unbounded.at(src).or(applies.and(overdraft, limit.eq(0)))),
      MaxLimit: MaxLimit.set(src, when(applies.and(limit.gt(MaxLimit.at(src))), limit, MaxLimit.at(src))),
      tC: tC.plus(when(posted.or(commits), a, zero)), tD: tD.plus(when(posted.or(commits), a, zero)),
      tIC: tIC.plus(when(held, a, zero)).minus(when(commits.or(voids), a, zero)), tID: tID.plus(when(held, a, zero)).minus(when(commits.or(voids), a, zero)),
    }
  })

const r = blnk()
const fuzz = (lines: string, why: string) => `model/invariant_fuzz_test.go:${lines} ${why}`
export const items: RealItem[] = [{
  id: 'ledger/blnk/balances',
  domain: 'ledger',
  source: {...src, path: 'model/model.go', lines: '117-283', export: 'Balance.addCredit, addDebit, computeBalance, canProcessTransaction, CommitInflight*, RollbackInflight*'},
  also: [
    {...src, path: 'model/model.go', lines: '447-507', export: 'Transaction.validate, UpdateBalances'},
    {...src, path: 'transaction_execution.go', lines: '320-365', export: 'Blnk.applyTransactionToBalances'},
    {...src, path: 'model/invariant_fuzz_test.go', lines: '1-40', export: 'TestLedgerInvariants_Seeded'},
  ],
  summary: 'Balances with posted and inflight credits and debits: a transfer debits the source and credits the destination (checked against available funds and an overdraft limit), an inflight hold is later committed or voided.',
  expressible: 'partial',
  gaps: [
    {gap: 'float', blocks: 'part', detail: 'OverdraftLimit is a float64 turned into precise units by decimal rounding (model.go:186-191), and a transaction without a PreciseAmount has its float Amount converted; the rule takes the precise limit and amount'},
    {gap: 'other', blocks: 'part', detail: 'RollbackInflight* take any big.Int, negative too; the rule takes amounts of at least 0 (the callers pass a transaction\'s PreciseAmount)'},
    {gap: 'external', blocks: 'part', detail: 'QueuedDebitBalance (set from the database when queued checks are on) is left out of the available funds'},
  ],
  laws: [
    invariant(r, r.law('every balance is its credits less its debits', ({B}) => forall(k => B.at(k).balance.eq(B.at(k).credit.minus(B.at(k).debit)))),
      'safety', 'tests', fuzz('13', '"Derived-balance identity: Balance == CreditBalance - DebitBalance"')),
    invariant(r, r.law('every inflight balance is its inflight credits less its inflight debits', ({B}) => forall(k => B.at(k).ibalance.eq(B.at(k).icredit.minus(B.at(k).idebit)))),
      'safety', 'tests', fuzz('13-14', '"InflightBalance == InflightCreditBalance - InflightDebitBalance"')),
    invariant(r, r.law('no inflight debit is ever negative', ({B}) => forall(k => B.at(k).idebit.atLeast(0))),
      'safety', 'tests', fuzz('12', '"Component sanity: all four credit/debit components are non-negative"')),
    invariant(r, r.law('money is conserved', ({tC, tD}) => tC.eq(tD)),
      'safety', 'tests', fuzz('9-11', '"Conservation: sum(CreditBalance) == sum(DebitBalance)"')),
    invariant(r, r.law('inflight money is conserved', ({tIC, tID}) => tIC.eq(tID)),
      'safety', 'tests', fuzz('10-11', '"sum(InflightCreditBalance) == sum(InflightDebitBalance)"')),
    invariant(r, r.law('no balance overdraws past the largest limit it sourced under', ({B, Unbounded, MaxLimit}) =>
      forall(k => Unbounded.at(k).or(B.at(k).balance.minus(B.at(k).idebit).plus(MaxLimit.at(k)).atLeast(0)))),
      'safety', 'tests', fuzz('15-17', '"Overdraft safety: a balance that has only ever sourced transactions without overdraft (or within an overdraft limit L) never has Balance - InflightDebitBalance < 0 (resp. < -L)"')),
  ],
  unstated: [
    {name: 'every inflight pool equals the sum of its open holds', kind: 'safety', intent: 'tests', why: fuzz('18-19', '"Hold accounting: each balance\'s inflight pools equal the sum of the harness-tracked remaining amounts of its open holds": holds are the callers\' records, a sum over a collection the rule does not keep')},
  ],
}]
