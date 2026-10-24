// Extracted by gdp-wired/extract from Balance.go (Balance, a struct and its methods).
// Checked against the code it was read from; read again with extract() after the code changes.
import {all, any, bool, int, no, oneOf, rule, when} from 'gdp-wired'

export const balanceRule = rule("Balance")
  .inputs({method: oneOf('addCredit', 'addDebit', 'computeBalance', 'RollbackInflightCredit', 'RollbackInflightDebit'), addCredit_amountBigInt: int, addCredit_inflight: bool, addDebit_amountBigInt: int, addDebit_inflight: bool, computeBalance_inflight: bool, RollbackInflightCredit_amount: int, RollbackInflightDebit_amount: int})
  .state({Balance: int.from(0), Balance_nil: bool.from(true), InflightBalance: int.from(0), InflightBalance_nil: bool.from(true), CreditBalance: int.from(0), CreditBalance_nil: bool.from(true), InflightCreditBalance: int.from(0), InflightCreditBalance_nil: bool.from(true), DebitBalance: int.from(0), DebitBalance_nil: bool.from(true), InflightDebitBalance: int.from(0), InflightDebitBalance_nil: bool.from(true)})
  .assume(({method, InflightCreditBalance_nil, InflightCreditBalance, RollbackInflightCredit_amount, InflightDebitBalance_nil, InflightDebitBalance, RollbackInflightDebit_amount}) => all(method.is('RollbackInflightCredit').implies(RollbackInflightCredit_amount.atMost(when(InflightCreditBalance_nil, 0, InflightCreditBalance))), method.is('RollbackInflightDebit').implies(RollbackInflightDebit_amount.atMost(when(InflightDebitBalance_nil, 0, InflightDebitBalance)))))
  .step(({method, Balance_nil, Balance, computeBalance_inflight, CreditBalance_nil, CreditBalance, DebitBalance_nil, DebitBalance, InflightBalance_nil, InflightBalance, InflightCreditBalance_nil, InflightCreditBalance, InflightDebitBalance_nil, InflightDebitBalance, RollbackInflightCredit_amount, RollbackInflightDebit_amount, addCredit_inflight, addCredit_amountBigInt, addDebit_inflight, addDebit_amountBigInt}) => {
    const t1 = method.is('addCredit')
    const t2 = when(Balance_nil, 0, Balance)
    const t3 = method.is('addDebit')
    const t4 = method.is('computeBalance')
    const t5 = when(CreditBalance_nil, 0, CreditBalance)
    const t6 = when(DebitBalance_nil, 0, DebitBalance)
    const t7 = t5.minus(t6)
    const t8 = when(InflightBalance_nil, 0, InflightBalance)
    const t9 = when(InflightCreditBalance_nil, 0, InflightCreditBalance)
    const t10 = when(InflightDebitBalance_nil, 0, InflightDebitBalance)
    const t11 = t9.minus(t10)
    const t12 = method.is('RollbackInflightCredit')
    const t13 = t9.minus(RollbackInflightCredit_amount)
    const t14 = when(InflightCreditBalance_nil, t13, t13)
    const t15 = t14.minus(t10)
    const t16 = t10.minus(RollbackInflightDebit_amount)
    const t17 = when(InflightDebitBalance_nil, t16, t16)
    const t18 = t9.minus(t17)
    const t19 = t5.plus(addCredit_amountBigInt)
    const t20 = t9.plus(addCredit_amountBigInt)
    const t21 = t6.plus(addDebit_amountBigInt)
    const t22 = t10.plus(addDebit_amountBigInt)
    return {Balance: when(t1, t2, when(t3, t2, when(t4, when(Balance_nil, when(computeBalance_inflight, 0, t7), when(computeBalance_inflight, Balance, t7)), t2))), Balance_nil: no, InflightBalance: when(t1, t8, when(t3, t8, when(t4, when(InflightBalance_nil, when(computeBalance_inflight, t11, 0), when(computeBalance_inflight, t11, InflightBalance)), when(t12, when(InflightBalance_nil, t15, t15), when(InflightBalance_nil, t18, t18))))), InflightBalance_nil: no, CreditBalance: when(t1, when(CreditBalance_nil, when(addCredit_inflight, 0, t19), when(addCredit_inflight, CreditBalance, t19)), t5), CreditBalance_nil: no, InflightCreditBalance: when(t1, when(InflightCreditBalance_nil, when(addCredit_inflight, t20, 0), when(addCredit_inflight, t20, InflightCreditBalance)), when(t3, t9, when(t4, t9, when(t12, t14, t9)))), InflightCreditBalance_nil: no, DebitBalance: when(t1, t6, when(t3, when(DebitBalance_nil, when(addDebit_inflight, 0, t21), when(addDebit_inflight, DebitBalance, t21)), t6)), DebitBalance_nil: no, InflightDebitBalance: when(t1, t10, when(t3, when(InflightDebitBalance_nil, when(addDebit_inflight, t22, 0), when(addDebit_inflight, t22, InflightDebitBalance)), when(t4, t10, when(t12, t10, t17)))), InflightDebitBalance_nil: no}
  })

// What every state of the code is: a law about every state is about the code's with these beside it.
export const balanceInvariants = [balanceRule.law("Balance: a nil one holds 0", ({Balance, Balance_nil}) => any(Balance_nil.not(), Balance.eq(0))), balanceRule.law("InflightBalance: a nil one holds 0", ({InflightBalance, InflightBalance_nil}) => any(InflightBalance_nil.not(), InflightBalance.eq(0))), balanceRule.law("CreditBalance: a nil one holds 0", ({CreditBalance, CreditBalance_nil}) => any(CreditBalance_nil.not(), CreditBalance.eq(0))), balanceRule.law("InflightCreditBalance: a nil one holds 0", ({InflightCreditBalance, InflightCreditBalance_nil}) => any(InflightCreditBalance_nil.not(), InflightCreditBalance.eq(0))), balanceRule.law("DebitBalance: a nil one holds 0", ({DebitBalance, DebitBalance_nil}) => any(DebitBalance_nil.not(), DebitBalance.eq(0))), balanceRule.law("InflightDebitBalance: a nil one holds 0", ({InflightDebitBalance, InflightDebitBalance_nil}) => any(InflightDebitBalance_nil.not(), InflightDebitBalance.eq(0)))]
