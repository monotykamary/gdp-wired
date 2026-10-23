// Solidus v4.8.0, Spree::StockItem with the stock movements and location calls that change it (core/app/models/spree).
// BSD-3-Clause, (c) Solidus contributors.
// https://github.com/solidusio/solidus/blob/8acbcba84621fa0d2b8c06acb6ccfdc36ada4bc9/core/app/models/spree/stock_item.rb
//
// One variant's stock item at one stock location: count_on_hand (may go negative only while backorderable), the
// backorderable flag, and the inventory units waiting on it as backordered. A save! that fails validation raises and
// its transaction (with_lock; ActiveRecord's save around after_create) rolls back: nothing changes, which the step
// says as "every part keeps its value". Line numbers are stock_item.rb's unless another file is named.
import {Int, bool, int, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'solidusio/solidus', commit: '8acbcba84621fa0d2b8c06acb6ccfdc36ada4bc9', licence: 'BSD-3-Clause', author: 'Solidus contributors', language: 'Ruby'}
const models = 'core/app/models/spree'

export const stockItem = () => rule('Solidus stock item')
  // `track`: the variant's should_track_inventory? (delegated, :15), fixed for a run.
  .params({track: bool})
  // One call: adjust_count_on_hand(value), set_count_on_hand(value), reduce_count_on_hand_to_zero, a StockMovement of
  // `value` (StockLocation#move / restock / unstock, stock_location.rb:85-107), restock_backordered(q)
  // (stock_location.rb:89-95), an update of backorderable to `b`; and, from outside, an inventory unit at this location
  // becoming backordered (the packer) or leaving that state (a canceled shipment).
  .inputs({op: oneOf('adjust', 'set', 'zero', 'move', 'restockBackordered', 'backorderable', 'unitBackordered', 'unitCanceled'), value: int, q: nat, b: bool})
  // :13 count_on_hand, the backorderable column; `units`: backordered_inventory_units (:28-30, inventory_unit.rb:41-57).
  // Ghosts: `filled` units filled by process_backorders, `received` the increases of count_on_hand that processed them.
  .ints({count: 0})
  .state({backorderable: bool.from(false), units: 0, filled: 0, received: 0})
  .flags(({op, value, b, track, count, backorderable}) => {
    // :13 `validates :count_on_hand, numericality: {greater_than_or_equal_to: 0}, unless: :backorderable?`.
    const valid = (c: typeof count, bo: typeof backorderable) => bo.or(c.atLeast(0))
    return {
      // :37-45 adjust_count_on_hand: count += value, process the increase, save!; a StockMovement does the same when
      // the variant tracks inventory (stock_movement.rb:23-26), else nothing.
      adjusts: op.is('adjust').or(op.is('move').and(track)).and(valid(count.plus(value), backorderable)),
      // :50-55 set_count_on_hand; :70-72 reduce_count_on_hand_to_zero sets 0 if the count is above 0.
      sets: op.is('set').and(valid(Int.of(0).plus(value), backorderable)).or(op.is('zero').and(count.gt(0))),
      // An update of backorderable is validated too.
      flips: op.is('backorderable').and(valid(count, b)),
    }
  })
  .step(({op, value, q, b, count, backorderable, units, filled, received, adjusts, sets}) => {
    const target = when(op.is('zero'), Int.of(0), Int.of(0).plus(value))
    const next = when(adjusts, count.plus(value), when(sets, target, when(op.is('restockBackordered'), count.plus(q), count)))
    // :96-100 process_backorders(count_on_hand - count_on_hand_was): when positive, the first that many backordered
    // units are filled (fill_backorder); restock_backordered uses update_columns and processes nothing.
    const rise = next.minus(count).clamped
    const processes = adjusts.or(sets)
    const fills = when(processes, when(units.lt(rise), units, rise), 0)
    return {
      count: next,
      backorderable: when(op.is('backorderable').and(Int.of(0).atMost(count).or(b)), b, backorderable),
      units: when(op.is('unitBackordered'), units.plus(1), when(op.is('unitCanceled'), units.minus(1), units.minus(fills))),
      filled: filled.plus(fills),
      received: when(processes, received.plus(rise), received),
    }
  })

const r = stockItem()
const cite = (file: string, lines: string, exp: string) => ({...src, path: `${models}/${file}`, lines, export: exp})
export const items: RealItem[] = [{
  id: 'inventory/solidus/stockItem',
  domain: 'inventory',
  source: cite('stock_item.rb', '13-100', 'Spree::StockItem'),
  also: [cite('stock_movement.rb', '9-27', 'Spree::StockMovement'), cite('stock_location.rb', '85-107', 'Spree::StockLocation#move, #restock_backordered'), cite('inventory_unit.rb', '41-57', 'backordered_for_stock_item')],
  summary: 'A stock item\'s count on hand moves by adjustments, sets and stock movements; it may go negative only while backorderable, and stock received fills waiting backordered units first.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'backordered inventory units are rows of another table, created by the packer and canceled with their shipment: here a count changed by two environment requests'},
    {gap: 'scope', blocks: 'part', detail: 'the backorderable flag starts false (StockLocation#propagate_variant uses the location\'s backorderable_default); one stock item'},
  ],
  // A liveness law (every backordered unit is eventually filled as stock arrives) was left out: units can keep being
  // backordered from outside without bound, so it is not a property of this code.
  laws: [
    invariant(r, r.law('a stock item that is not backorderable never has a negative count', ({count, backorderable}) => backorderable.or(count.atLeast(0))),
      'safety', 'docs', 'stock_item.rb:13 validates :count_on_hand, numericality: {greater_than_or_equal_to: 0}, unless: :backorderable?'),
    invariant(r, r.law('backordered units filled never exceed the stock received', ({filled, received}) => filled.atMost(received)),
      'safety', 'docs', 'stock_item.rb:94-95 "If stock was -20 and is now -15 (increase of 5 units), then we should process 5 inventory orders"'),
    stepLaw(r, r.stepLaw('stock received fills waiting backordered units first', ({units, filled, count}, after) => {
      const rise = after.count.minus(count).clamped
      return after.filled.minus(filled).eq(when(units.lt(rise), units, rise))
    }, ({adjusts, sets}) => adjusts.or(sets)),
    'step', 'docs', 'stock_item.rb:34-35 "Adjusts the count on hand by a given value. @note This will cause backorders to be processed."'),
    stepLaw(r, r.stepLaw('a stock movement of a variant that does not track inventory never changes the count', ({count}, after) => after.count.eq(count),
      ({op, track}) => op.is('move').and(track.not())),
    'step', 'docs', 'stock_movement.rb:24 `return unless stock_item.should_track_inventory?`'),
  ],
}]
