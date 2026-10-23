// OpenZeppelin Contracts v4.9.6, RefundEscrow (with ConditionalEscrow and Escrow, which it extends). MIT, (c)
// OpenZeppelin. https://github.com/OpenZeppelin/openzeppelin-contracts/tree/dc44c9f1a4c3b10af99492eed84f83ed244203f6/contracts/utils/escrow
//
// An escrow holding deposits for a beneficiary from several refundees: the owner deposits while Active, then either
// closes it (the beneficiary takes the whole balance) or enables refunds (the owner withdraws each refundee's deposit).
// A call that fails a `require` reverts: nothing changes, which the step says as "every part keeps its value".
import {forall, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'OpenZeppelin/openzeppelin-contracts', commit: 'dc44c9f1a4c3b10af99492eed84f83ed244203f6', licence: 'MIT', author: 'OpenZeppelin', language: 'Solidity'}

export const refundEscrow = () => rule('RefundEscrow')
  // RefundEscrow.sol:31 `_beneficiary` (immutable), Ownable's owner; addresses as numbers. `d`: the refundee a liveness
  // law watches (not the code's).
  .params({owner: nat, beneficiary: nat, d: nat})
  // RefundEscrow.sol:38 `require(beneficiary_ != address(0))`.
  .pre(({beneficiary}) => beneficiary.atLeast(1))
  // One call: which function, msg.sender, its address argument (refundee / payee), msg.value.
  .inputs({op: oneOf('deposit', 'close', 'enableRefunds', 'beneficiaryWithdraw', 'withdraw'), sender: nat, who: nat, value: nat})
  // RefundEscrow.sol:30 `_state` (State.Active at :40); `balance`: address(this).balance; `toBeneficiary`, `refunded`
  // and `deposited`: the value sent out by sendValue (:90, Escrow.sol:63) and in by msg.value, totals of the transfers
  // the code makes (observed effects, not fields of the contract).
  .state({st: oneOf('Active', 'Refunding', 'Closed').from('Active'), balance: 0, toBeneficiary: 0, refunded: 0, deposited: 0})
  // Escrow.sol:28 `_deposits`.
  .maps({Deposits: 0})
  .flags(({op, sender, owner, who, st, balance, Deposits}) => ({
    // RefundEscrow.sol:61-63 `require(state() == State.Active)`, then Escrow.sol:40 `onlyOwner`.
    deposits: op.is('deposit').and(st.is('Active'), sender.eq(owner)),
    // RefundEscrow.sol:70-72 and :79-81: onlyOwner, `require(state() == State.Active)`.
    closes: op.is('close').and(sender.eq(owner), st.is('Active')),
    refunds: op.is('enableRefunds').and(sender.eq(owner), st.is('Active')),
    // RefundEscrow.sol:88-90: anyone, `require(state() == State.Closed)`, sends the whole balance.
    pays: op.is('beneficiaryWithdraw').and(st.is('Closed')),
    // ConditionalEscrow.sol:21-23 `require(withdrawalAllowed(payee))` (RefundEscrow.sol:97-98: state Refunding), then
    // Escrow.sol:58 `onlyOwner`; Escrow.sol:63 `payee.sendValue(payment)`, Address.sol:65
    // `require(address(this).balance >= amount)`. (A send the recipient reverts, Address.sol:68, reverts the call: a
    // request that does nothing, which a request of another op already is.)
    withdraws: op.is('withdraw').and(st.is('Refunding'), sender.eq(owner), Deposits.at(who).atMost(balance)),
  }))
  .step(({who, value, st, balance, toBeneficiary, refunded, deposited, Deposits, deposits, closes, refunds, pays, withdraws}) => ({
    st: when(closes, 'Closed', when(refunds, 'Refunding', st)),
    // Escrow.sol:41-42 `_deposits[payee] += amount`; :59-61 `payment = _deposits[payee]; _deposits[payee] = 0`.
    Deposits: Deposits.set(who, when(deposits, Deposits.at(who).plus(value), when(withdraws, 0, Deposits.at(who)))),
    balance: when(deposits, balance.plus(value), when(pays, 0, when(withdraws, balance.minus(Deposits.at(who)), balance))),
    toBeneficiary: when(pays, toBeneficiary.plus(balance), toBeneficiary),
    refunded: when(withdraws, refunded.plus(Deposits.at(who)), refunded),
    deposited: when(deposits, deposited.plus(value), deposited),
  }))

const r = refundEscrow()
const cite = (lines: string, exp: string) => ({...src, path: `contracts/utils/escrow/${exp}.sol`, lines, export: exp})
export const items: RealItem[] = [{
  id: 'ledger/openzeppelin/RefundEscrow',
  domain: 'ledger',
  source: cite('18-99', 'RefundEscrow'),
  also: [cite('13-24', 'ConditionalEscrow'), cite('22-66', 'Escrow'), {...src, path: 'contracts/utils/Address.sol', lines: '64-69', export: 'sendValue'}],
  summary: 'Deposits held for a beneficiary while Active; then Closed (the beneficiary withdraws the balance) or Refunding (the owner refunds each depositor).',
  expressible: 'full',
  gaps: [],
  laws: [
    invariant(r, r.law('no more is paid out than was deposited', ({toBeneficiary, refunded, deposited}) => toBeneficiary.plus(refunded).atMost(deposited)),
      'safety', 'inferred', 'the purpose of an escrow: it pays out only what it holds'),
    invariant(r, r.law('the beneficiary and the refundees are never both paid', ({toBeneficiary, refunded}) => toBeneficiary.eq(0).or(refunded.eq(0))),
      'safety', 'docs', 'RefundEscrow.sol:13-16 "allow for either withdrawal by the beneficiary, or refunds to the depositors"'),
    // Stated first for every state, this law was refuted: once Closed and the beneficiary paid, `depositsOf` still
    // returns the old credits against a balance of 0 (README: a law error, not a bug: no withdrawal is allowed then).
    invariant(r, r.law("until closed, every refundee's deposit is covered by the balance", ({Deposits, balance, st}) => forall(k => st.is('Closed').or(Deposits.at(k).atMost(balance)))),
      'safety', 'inferred', 'Escrow.sol:35 "Stores the sent amount as credit to be withdrawn": a credit the contract can pay while it may be withdrawn'),
    stepLaw(r, r.stepLaw('the state never returns to Active', (_, after) => after.st.is('Active').not(), b => b.st.is('Active').not()),
      'step', 'docs', 'RefundEscrow.sol:66-83: close and enableRefunds only "while active", nothing sets Active again'),
    stepLaw(r, r.stepLaw('only the owner changes the state', ({sender, owner}, after) => after.st.is('Active').or(sender.eq(owner)), ({st}) => st.is('Active')),
      'access', 'docs', 'RefundEscrow.sol:70, :79 `onlyOwner`'),
    stepLaw(r, r.stepLaw('a refund only while refunding', ({st, refunded}, after) => after.refunded.atMost(refunded).or(st.is('Refunding'))),
      'step', 'docs', 'RefundEscrow.sol:97-98 withdrawalAllowed is `state() == State.Refunding`'),
    leadsTo(r, r.leadsTo('once refunding, every deposit is refunded', {
      from: ({st, Deposits, d}) => st.is('Refunding').and(Deposits.at(d).gt(0)),
      to: ({Deposits, d}) => Deposits.at(d).eq(0),
      helpful: ({d, owner}) => ({op: 4, sender: owner, who: d}),
    }), 'docs', 'RefundEscrow.sol:77 "Allows for refunds to take place"; the owner withdrawing for d refunds d'),
  ],
}]
