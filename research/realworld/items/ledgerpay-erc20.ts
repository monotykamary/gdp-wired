// OpenZeppelin Contracts v5.7.0, ERC20: balances, allowances and the total supply under transfer, approve and
// transferFrom, and the internal _mint and _burn a token contract calls. MIT, (c) OpenZeppelin.
// https://github.com/OpenZeppelin/openzeppelin-contracts/blob/cab19933c33c2ad1d4c7a84864a3601dddfd16f3/contracts/token/ERC20/ERC20.sol
//
// A call that reverts changes nothing: every part keeps its value. ERC20 is abstract (:29): `mint` and `burn` are the
// internal _mint and _burn (:214-234) as a token that extends it exposes them, with any caller.
import {forall, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'OpenZeppelin/openzeppelin-contracts', commit: 'cab19933c33c2ad1d4c7a84864a3601dddfd16f3', licence: 'MIT', author: 'OpenZeppelin', language: 'Solidity'}
// `_allowances[owner][spender]` (:32) is a mapping of mappings; the rule keys one map by the pair, `owner * 2^26 +
// spender`, which is one key per pair for addresses below 2^26 (the gap below).
const W = 2 ** 26
export const erc20 = () => rule('ERC20')
  // `max`: type(uint256).max, the bound of a checked addition (:179) and the infinite allowance (:296).
  .params({max: nat})
  // One call: which function, msg.sender (_msgSender, Context.sol), and its arguments as addresses and a value.
  .inputs({op: oneOf('transfer', 'approve', 'transferFrom', 'mint', 'burn'), sender: nat, from: nat, to: nat, spender: nat, value: nat})
  // Every address argument below 2^26 (the gap); every value a uint256, at most max.
  .assume(({sender, from, to, spender, value, max}) => sender.lt(W).and(from.lt(W), to.lt(W), spender.lt(W), value.atMost(max)))
  // :30 `_balances`, :32 `_allowances`, :34 `_totalSupply`; `held`: a ghost (not the contract's), the sum of every
  // balance, changed by what each step adds to and takes from the balances.
  .state({totalSupply: 0, held: 0})
  .maps({Bal: 0, Allow: 0})
  .flags(({op, sender, from, to, spender, value, max, totalSupply, Bal, Allow}) => {
    // Who pays (0: none, as _update reads address(0): a mint), and the allowance read.
    const payer = when(op.is('transfer'), sender, when(op.is('mint'), 0, from))
    const allowance = Allow.at(from.times(W).plus(sender))
    // :176-201 _update: from address(0), `_totalSupply += value` reverts past max (checked arithmetic); otherwise
    // `fromBalance < value` reverts (:182-184).
    const updates = payer.eq(0).implies(totalSupply.plus(value).atMost(max)).and(payer.gt(0).implies(Bal.at(payer).atLeast(value)))
    return {
      // :99-103 transfer(to, value) is _transfer(sender, to, value); :159-167 _transfer reverts on a zero from or to.
      transfers: op.is('transfer').and(sender.gt(0), to.gt(0), updates),
      // :120-124 approve(spender, value) is _approve(sender, spender, value); :273-283 reverts on a zero owner or spender.
      approves: op.is('approve').and(sender.gt(0), spender.gt(0)),
      // :142-147 transferFrom: _spendAllowance(from, sender, value) (:294-304: below max, `currentAllowance < value`
      // reverts; the _approve it calls reverts on a zero owner or spender), then _transfer(from, to, value).
      transfersFrom: op.is('transferFrom').and(from.gt(0), sender.gt(0), to.gt(0), allowance.lt(max).implies(allowance.atLeast(value)), updates),
      // :214-219 _mint reverts on a zero account; :229-234 _burn too.
      mints: op.is('mint').and(to.gt(0), updates),
      burns: op.is('burn').and(from.gt(0), updates),
    }
  })
  .step(({op, sender, from, to, spender, value, max, totalSupply, held, Bal, Allow, transfers, approves, transfersFrom, mints, burns}) => {
    const moves = transfers.or(transfersFrom, mints, burns)
    const payer = when(op.is('transfer'), sender, when(op.is('mint'), 0, from)), payee = when(op.is('burn'), 0, to)
    const slot = when(op.is('approve'), sender.times(W).plus(spender), from.times(W).plus(sender))
    const allowance = Allow.at(from.times(W).plus(sender))
    return {
      // :181-188 `_balances[from] = fromBalance - value`, then :196-201 `_balances[to] += value` (the same account
      // when from is to: it ends where it was).
      Bal: Bal.each(k => when(moves, Bal.at(k).minus(when(payer.gt(0).and(k.eq(payer)), value, 0)).plus(when(payee.gt(0).and(k.eq(payee)), value, 0)), Bal.at(k))),
      // :280 `_allowances[owner][spender] = value`; :296-302 an allowance below max goes down by the value spent.
      Allow: Allow.set(slot, when(approves, value, when(transfersFrom.and(allowance.lt(max)), allowance.minus(value), Allow.at(slot)))),
      // :177-179 from address(0) `_totalSupply += value`; :191-195 to address(0) `_totalSupply -= value`.
      totalSupply: when(moves, totalSupply.plus(when(payer.eq(0), value, 0)).minus(when(payee.eq(0), value, 0)), totalSupply),
      held: when(moves, held.plus(when(payee.gt(0), value, 0)).minus(when(payer.gt(0), value, 0)), held),
    }
  })

const r = erc20()
export const items: RealItem[] = [{
  id: 'ledger/openzeppelin/ERC20',
  domain: 'ledger',
  source: {...src, path: 'contracts/token/ERC20/ERC20.sol', lines: '99-305', export: 'ERC20.transfer, approve, transferFrom, _transfer, _update, _mint, _burn, _approve, _spendAllowance'},
  summary: 'Token balances and allowances: a transfer moves value between balances, transferFrom spends an allowance (unless infinite), mint and burn change the total supply.',
  expressible: 'partial',
  gaps: [
    {gap: 'two-key-map', blocks: 'part', detail: 'the allowances are a mapping of mappings; the rule keys one map by owner * 2^26 + spender, one key per pair only for addresses below 2^26 (gdp-wired has no map keyed by two values, and a constant of 2^160 is not a safe integer)'},
  ],
  laws: [
    invariant(r, r.law('the balances sum to the total supply', ({held, totalSupply}) => held.eq(totalSupply)),
      'safety', 'docs', 'ERC20.sol:186 "value <= fromBalance <= totalSupply", :198 "balance + value is at most totalSupply"'),
    invariant(r, r.law('no balance exceeds the total supply', ({Bal, totalSupply}) => forall(k => Bal.at(k).atMost(totalSupply))),
      'safety', 'docs', 'ERC20.sol:197-199 "Overflow not possible: balance + value is at most totalSupply, which we know fits into a uint256" (unchecked)'),
    invariant(r, r.law('the total supply never passes the uint256 bound', ({totalSupply, max}) => totalSupply.atMost(max)),
      'safety', 'docs', 'ERC20.sol:178 "Overflow check required: The rest of the code assumes that totalSupply never overflows"'),
    stepLaw(r, r.stepLaw('a transfer neither creates nor destroys tokens', ({totalSupply}, after) => after.totalSupply.eq(totalSupply), ({op}) => op.is('transfer').or(op.is('transferFrom'))),
      'step', 'docs', 'ERC20.sol:92-97 transfer "Moves a `value` amount of tokens from the caller\'s account to `to`"'),
    stepLaw(r, r.stepLaw('only its owner, a spender it approved, or a burn lowers a balance', ({op, sender, value, Bal, Allow}, after) =>
      forall(k => after.Bal.at(k).lt(Bal.at(k)).implies(sender.eq(k).or(op.is('burn'), op.is('transferFrom').and(Allow.at(k.times(W).plus(sender)).atLeast(value)))))),
      'access', 'docs', 'ERC20.sol:126-141 transferFrom "the caller must have allowance for ``from``\'s tokens of at least `value`"'),
    stepLaw(r, r.stepLaw('transferFrom spends the allowance it uses', ({from, sender, value, Allow}, after) =>
      after.Allow.at(from.times(W).plus(sender)).plus(value).eq(Allow.at(from.times(W).plus(sender))), ({transfersFrom, from, sender, max, Allow}) => transfersFrom.and(Allow.at(from.times(W).plus(sender)).lt(max))),
      'step', 'docs', 'ERC20.sol:287-290 _spendAllowance "Updates `owner`\'s allowance for `spender` based on spent `value`. Does not update the allowance value in case of infinite allowance."'),
  ],
}]
