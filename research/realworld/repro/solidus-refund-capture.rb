# Repro (by reading the source; Spree::Payment and Spree::Refund are ActiveRecord models that need a Rails app and a
# database to run) for payment/solidus/Payment, law "refunds never exceed the payment amount".
# Solidus v4.8.0, https://github.com/solidusio/solidus/tree/8acbcba84621fa0d2b8c06acb6ccfdc36ada4bc9/core (BSD-3-Clause).
#
# The run the search found, shortened (amounts in cents; default configuration):
#   1. A payment of 6 is authorized: authorize! fires started_processing then pend (payment/processing.rb:37-50), so
#      its state is "pending" (state_machines/payment.rb:35-37).
#   2. A Spree::Refund of 6 is created for it. Its validations pass:
#        refund.rb:15     amount > 0
#        refund.rb:89-93  6 <= payment.credit_allowed, which is `amount - refunds.sum(:amount)` = 6 - 0 (payment.rb:93-95)
#        refund.rb:95-109 "pending" is in Spree::Config.refundable_payment_states, default %w[completed pending]
#                         (app_configuration.rb:288-290); outside it the refund is still allowed unless
#                         require_refundable_payment_state, default false (:296-298)
#   3. capture!(2) on the payment (processing.rb:73-91): not completed, amount positive, started_processing! (pending
#      is a `from` state, payment.rb:28), the gateway's capture, `capture_events.create!(amount: 2)`, then
#      `update!(amount: captured_amount)` sets the payment's amount to 2, and complete! makes it completed.
#   Now refunds.sum(:amount) = 6 and amount = 2: credit_allowed is -4, the refunds exceed the payment's amount, which
#   refund.rb:89-93 exists to prevent ("greater_than_allowed").
# The search's own run reaches the same through a refund on a "processing" payment (allowed with a deprecation
# warning under the default require_refundable_payment_state = false), then pend, then a partial capture.
#
# Nothing below runs Solidus; it replays the arithmetic of the three lines that matter, as excerpted above.
amount, refunds = 6, 0
credit_allowed = -> { amount - refunds }
refund = 6
raise "refund refused" unless refund > 0 && refund <= credit_allowed.call
refunds += refund
captured = 2
amount = captured # update!(amount: captured_amount)
puts "amount #{amount}, refunds #{refunds}, credit_allowed #{credit_allowed.call}"
