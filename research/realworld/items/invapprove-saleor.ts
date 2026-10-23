// Saleor 3.23.44, warehouse stock allocation (saleor/warehouse/management.py, models.py). BSD-3-Clause, (c) Saleor
// Commerce. https://github.com/saleor/saleor/blob/b2587a12ea15edf3432aaa4c6a5065c9c9ca049f/saleor/warehouse/management.py
//
// One product variant's stock in one warehouse (Stock: quantity, quantity_allocated) and the order lines' allocations
// against it (Allocation: one row per line and stock, quantity_allocated). A function under
// @traced_atomic_transaction that raises rolls back: nothing changes, which the step says as "every part keeps its
// value". deallocate_stock and decrease_allocations are not atomic themselves: their writes stand when they raise.
// Line numbers are management.py's unless models.py is named.
import {Int, bool, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'saleor/saleor', commit: 'b2587a12ea15edf3432aaa4c6a5065c9c9ca049f', licence: 'BSD-3-Clause', author: 'Saleor Commerce', language: 'Python'}

export const allocations = () => rule('Saleor stock allocations')
  // `track`: the variant's track_inventory (get_order_lines_with_track_inventory, :715-731), fixed for a run; `d`: the
  // order line a liveness law watches (not the code's).
  .params({track: bool, d: nat})
  // One call: which function, the order line(s) and quantities (OrderLineInfo.quantity), increase_stock's `allocate`,
  // decrease_stock's `allow_stock_to_be_exceeded`. `dealloc2` is decrease_allocations for two lines at once.
  .inputs({op: oneOf('allocate', 'dealloc', 'dealloc2', 'increase', 'decrease', 'releaseOrder'), line: nat, q: nat, line2: nat, q2: nat, allocate: bool, exceed: bool})
  // models.py:532-533 Stock.quantity and quantity_allocated (IntegerField); `allocSum`: the sum of the Allocation rows'
  // quantity_allocated, which allocate_stocks (:156-169) and decrease_stock (:621-634) query as the allocated
  // quantity (a ghost kept equal to that sum by construction). `exceeded`: fulfilments that went through only because
  // allow_stock_to_be_exceeded was set (ghost).
  .ints({quantity: 0, qa: 0})
  .state({allocSum: 0, exceeded: 0})
  // models.py:573-597 Allocation, unique per (order_line, stock): a row, and its quantity_allocated.
  .maps({Row: bool.from(false), Alloc: 0})
  .assume(({op, line, line2}) => op.is('dealloc2').implies(line.eq(line2).not()))
  .flags(({op, line, q, track, quantity, allocSum, Row, Alloc, exceed}) => {
    // :320-356 _create_allocations: available = quantity - allocated (- reservations, not checked here); allocate
    // min(needed, available) while positive; short of the line's quantity, InsufficientStock is raised (:197-198) and
    // the transaction rolls back. A quantity of 0 allocates nothing and raises nothing. bulk_create (:201) of a second
    // row for a line and stock breaks the unique constraint and rolls back too.
    const avail = quantity.minus(allocSum)
    const taken = when(Alloc.at(line).lt(q), Alloc.at(line), q) // :396 min(quantity - deallocated, allocation)
    // :683-699: after decrease_allocations, the line's quantity against quantity - allocated.
    const short = quantity.minus(allocSum.minus(taken)).lt(q)
    return {
      allocates: op.is('allocate').and(track, q.atLeast(1), avail.atLeast(q), Row.at(line).not()),
      // :568-583 decrease_allocations: only lines with an allocation row (get_order_lines_to_deallocate, :734-760).
      deallocs: op.is('dealloc').and(Row.at(line)),
      decreases: op.is('decrease').and(track.not().or(short.not(), exceed)),
      goesOver: op.is('decrease').and(track, short, exceed),
    }
  })
  .step(({op, line, q, line2, q2, allocate, track, quantity, qa, allocSum, exceeded, Row, Alloc, allocates, deallocs, decreases, goesOver}) => {
    const a1 = Alloc.at(line), a2 = Alloc.at(line2)
    const x1 = when(a1.lt(q), a1, q), x2 = when(a2.lt(q2), a2, q2)
    const pair = op.is('dealloc2')
    const r1 = pair.and(Row.at(line)), r2 = pair.and(Row.at(line2))
    const d1 = when(r1, x1, 0), d2 = when(r2, x2, 0)
    // decrease_stock (:612) deallocates the line first (decrease_allocations), inside its own transaction.
    const dec = decreases.and(Row.at(line))
    const released = op.is('releaseOrder')
    return {
      // :486-494 increase_stock: Stock.increase_stock (models.py:541-545), and with `allocate` the line's allocation
      // (created, or += quantity) and Stock.quantity_allocated += quantity. :700-702: decrease_stock's
      // `stock.quantity = stock.quantity - line_info.quantity`.
      quantity: when(op.is('increase'), quantity.plus(q), when(decreases.and(track), quantity.minus(q), quantity)),
      qa: when(allocates, qa.plus(q),
        // :403-405 one Stock instance per allocation, each `F("quantity_allocated") - quantity_to_deallocate`, and
        // :449 Stock.objects.bulk_update(stocks_to_update, ...): for two lines on one stock the list holds the stock
        // twice, and Django's bulk_update writes only the first of duplicate objects (its CASE WHEN on the pk takes
        // the first match). The first appended is the first line's, if it deallocated anything.
        when(deallocs, qa.minus(x1),
          when(pair, qa.minus(when(d1.gt(0), d1, d2)),
            when(op.is('increase').and(allocate), qa.plus(q),
              when(dec, qa.minus(x1),
                // :779-807 deallocate_stock_for_orders: _reduce_quantity_allocated_for_stocks sums per stock (:509-516).
                when(released, qa.minus(a1), qa)))))),
      allocSum: when(allocates, allocSum.plus(q), when(deallocs.or(dec), allocSum.minus(x1), when(pair, allocSum.minus(d1).minus(d2),
        when(op.is('increase').and(allocate), allocSum.plus(q), when(released, allocSum.minus(a1), allocSum))))),
      exceeded: when(goesOver, exceeded.plus(1), exceeded),
      Row: Row.set(line, Row.at(line).or(allocates, op.is('increase').and(allocate))),
      Alloc: Alloc.each(k => when(k.eq(line), when(allocates, q, when(deallocs.or(dec), a1.minus(x1), when(op.is('increase').and(allocate), a1.plus(q), when(released.or(r1), a1.minus(when(released, a1, x1)), a1)))),
        when(r2.and(k.eq(line2)), a2.minus(x2), Alloc.at(k)))),
    }
  })

const r = allocations()
const cite = (lines: string, exp: string, path = 'saleor/warehouse/management.py') => ({...src, path, lines, export: exp})
export const items: RealItem[] = [{
  id: 'inventory/saleor/allocations',
  domain: 'inventory',
  source: cite('88-810', 'allocate_stocks, deallocate_stock, increase_stock, decrease_allocations, decrease_stock, deallocate_stock_for_orders'),
  also: [cite('527-597', 'Stock, Allocation', 'saleor/warehouse/models.py'), cite('1-30', 'stock_select_for_update_for_existing_qs, allocation_with_stock_qs_select_for_update', 'saleor/warehouse/lock_objects.py')],
  summary: 'Order lines allocate a variant\'s stock (all of a line or nothing, against quantity minus what is allocated); deallocation, fulfilment and order release return it; Stock.quantity_allocated keeps the total.',
  expressible: 'partial',
  gaps: [
    {gap: 'unbounded-collection', blocks: 'part', detail: 'one warehouse: allocate_stocks fills a line from the channel\'s stocks sorted by its allocation strategy (sort_stocks, :268-313); batches are one line, or two for decrease_allocations'},
    {gap: 'external', blocks: 'part', detail: 'checkout reservations (check_reservations, :243-265), preorders, channel and shipping-zone stock filters, and stock quantity set by staff mutations are left out'},
    {gap: 'other', blocks: 'part', detail: 'Django\'s bulk_update with a duplicate object (the first one wins) is modelled from Django\'s documented behaviour, not from code in the repo'},
  ],
  laws: [
    invariant(r, r.law("the stock's allocated count is the sum of its allocations", ({qa, allocSum}) => qa.eq(allocSum)),
      'safety', 'inferred', 'models.py:533 quantity_allocated is kept by every function with F() updates mirroring the Allocation rows (:211-213, :403-404, :493, :515)'),
    invariant(r, r.law('allocations never exceed the stock unless a fulfilment was let exceed it', ({quantity, allocSum, exceeded}) => exceeded.eq(0).implies(quantity.atLeast(allocSum))),
      'safety', 'docs', 'management.py:111 "If there is less quantity in stocks then rise InsufficientStock exception"; :598 "If allow_stock_to_be_exceeded flag is True then quantity could be < 0"'),
    stepLaw(r, r.stepLaw('an allocation takes all of the line or nothing', ({line, q, Alloc}, after) => after.Alloc.at(line).eq(Alloc.at(line)).or(after.Alloc.at(line).eq(q)),
      ({op}) => op.is('allocate')),
    'step', 'docs', 'management.py:107-111 "allocate as many items as needed ... until allocated all required quantity ... If there is less quantity in stocks then rise InsufficientStock"'),
    stepLaw(r, r.stepLaw('a deallocation returns to the stock exactly what it takes from the allocations', ({qa, allocSum}, after) => qa.minus(after.qa).eq(Int.of(allocSum).minus(after.allocSum)),
      ({op}) => op.is('dealloc').or(op.is('dealloc2'), op.is('releaseOrder'))),
    'step', 'docs', 'management.py:369 "deallocate as many items as needed of available in stock for order line"; :498-505 "Reduce quantity allocated for stocks from allocations"'),
    leadsTo(r, r.leadsTo("every line's allocation can be released", {
      from: ({Alloc, d}) => Alloc.at(d).gt(0),
      to: ({Alloc, d}) => Alloc.at(d).eq(0),
      helpful: ({d}) => ({op: 5, line: d}),
    }), 'docs', 'management.py:769 deallocate_stock_for_orders "Remove all allocations for given orders."'),
  ],
}]
