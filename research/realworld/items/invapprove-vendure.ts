// Vendure v2.3.4, StockMovementService with the DefaultStockLocationStrategy (packages/core). MIT, (c) 2018 Michael
// Bromley: v2.3.4 predates Vendure's move to GPL-3.0 (v3), and its LICENSE is MIT.
// https://github.com/vendure-ecommerce/vendure/blob/ff1d8e63533192f264f596ced72e9225ac2127c4/packages/core/src/service/services/stock-movement.service.ts
//
// One product variant's stock level at the single default location (StockLevel: stockOnHand, stockAllocated), and the
// Allocation movements recorded per order line. Allocations, sales, cancellations and releases each save a
// StockMovement and, for a variant that tracks inventory, change the level. Line numbers are stock-movement.service.ts's
// unless another file is named.
import {bool, int, nat, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'vendure-ecommerce/vendure', commit: 'ff1d8e63533192f264f596ced72e9225ac2127c4', licence: 'MIT', author: 'Michael Bromley', language: 'TypeScript'}
const core = 'packages/core/src'

export const stockMovements = () => rule('Vendure stock movements')
  // `track`: trackInventoryForVariant (:357-362), the variant's flag or the global setting, fixed for a run; `d`: the
  // order line a liveness law watches (not the code's).
  .params({track: bool, d: nat})
  // One call: adjustProductVariantStock (`n`: the new stockOnHand), or one OrderLineInput {orderLineId, quantity} of
  // createAllocationsForOrderLines, createSalesForOrder, createCancellationsForOrderLines, createReleasesForOrderLines.
  .inputs({op: oneOf('adjust', 'allocate', 'sale', 'cancel', 'release'), line: nat, q: nat, n: int})
  // entity/stock-level/stock-level.entity.ts: stockOnHand, stockAllocated (integers); getStockLevel (stock-level.service.ts:33-52)
  // creates the level at 0, 0. `released`: the quantity released and sold so far (a ghost).
  .ints({onHand: 0, allocated: 0})
  // Whether the StockLevel row exists: getStockLevel (stock-level.service.ts:33-52, called by adjustProductVariantStock)
  // and updateStockOnHandForLocation (:83-107) create it; updateStockAllocatedForLocation (:113-132) changes nothing
  // while it is missing. (Stated first without it, the rule allocated against a level that wasn't there: the
  // conformance harness, repro/conform-vendure.ts, showed the original leaving stockAllocated at 0.)
  .state({level: bool.from(false)})
  // The quantity of each line's Allocation records (entity/stock-movement/allocation.entity.ts): saved by
  // createAllocationsForOrderLines and never removed (a sale, cancellation or release saves another record); `Has`: the
  // line has any (one of quantity 0 counts: the strategy still returns its location). `Freed`: sold and released (ghost).
  .maps({Allocs: 0, Has: bool.from(false), Freed: 0})
  .step(({op, line, q, n, track, level, onHand, allocated, Allocs, Has, Freed}) => {
    // default-stock-location-strategy.ts:79-106 getLocationsBasedOnAllocations: walks the line's allocations, taking
    // min(allocation.quantity, unallocated) until the quantity asked is reached: min(q, the line's allocations); no
    // allocation (or q = 0) gives no location, so no movement.
    const x = when(Allocs.at(line).lt(q), Allocs.at(line), q)
    // No allocation (or q = 0) gives no location and no update; an allocation of 0 gives its location with 0, which still calls the level updates with change 0, creating a
    // missing row for stockOnHand (:96-104 saves a new StockLevel even for a change of 0).
    const found = Has.at(line).and(q.gt(0))
    const sale = op.is('sale').and(track, found), release = op.is('release').and(track, found), cancel = op.is('cancel').and(track, found)
    return {
      level: level.or(op.is('adjust'), sale, cancel),
      // :89-123: delta = new - old, then stock-level.service.ts:83-107 stockOnHand + change; :175-182 a sale lowers
      // stockOnHand by the quantity sold; :258-265 a cancellation raises it.
      onHand: when(op.is('adjust'), n, when(sale, onHand.minus(x), when(cancel, onHand.plus(x), onHand))),
      // :143-173 allocation: default-stock-location-strategy.ts:46-53 forAllocation is the first location with the
      // whole quantity, and stockAllocated += quantity (stock-level.service.ts:113-132); :175-182 a sale and :311-321 a
      // release lower it by what the strategy found.
      allocated: when(op.is('allocate').and(track, level), allocated.plus(q), when(sale.and(level).or(release.and(level)), allocated.minus(x), allocated)),
      Allocs: Allocs.set(line, when(op.is('allocate'), Allocs.at(line).plus(q), Allocs.at(line))),
      Has: Has.set(line, Has.at(line).or(op.is('allocate'))),
      Freed: Freed.set(line, when(sale.or(release), Freed.at(line).plus(x), Freed.at(line))),
    }
  })

const r = stockMovements()
const cite = (path: string, lines: string, exp: string) => ({...src, path: `${core}/${path}`, lines, export: exp})
export const items: RealItem[] = [{
  id: 'inventory/vendure/stockMovements',
  domain: 'inventory',
  source: cite('service/services/stock-movement.service.ts', '80-365', 'StockMovementService'),
  also: [cite('service/services/stock-level.service.ts', '33-133', 'StockLevelService'), cite('config/catalog/default-stock-location-strategy.ts', '37-106', 'DefaultStockLocationStrategy')],
  summary: 'Placing an order allocates stock (stockAllocated += quantity); fulfilment sells it (both stockAllocated and stockOnHand go down); releases free allocated stock and cancellations return sold stock, each by up to what the line\'s allocations hold.',
  // A liveness law (every allocated line can be released) was dropped: further allocations of the same line (order
  // modification) raise what is left to release without bound, so it is not a property of this code.
  expressible: 'partial',
  gaps: [
    {gap: 'unbounded-collection', blocks: 'part', detail: 'one variant at the one location the default strategy uses; a call with one order line (the services loop over lines, each read and written on its own)'},
    {gap: 'external', blocks: 'part', detail: 'whether a line may be allocated, sold, released or cancelled, and for which quantity, is decided by OrderService and the OrderProcess, not here; the saleable-stock check (ProductVariantService.getSaleableStockLevel) runs when a line is added to an order, not at allocation'},
  ],
  laws: [
    invariant(r, r.law('stock allocated never goes negative', ({allocated}) => allocated.atLeast(0)),
      'safety', 'docs', 'stock-movement.service.ts:309-312 a release "reduced, indicating that this stock is once again available to buy": it frees stock that was allocated'),
    invariant(r, r.law("a line's sales and releases never free more than it allocated", ({Allocs, Freed, d}) => Freed.at(d).atMost(Allocs.at(d))),
      'safety', 'inferred', 'default-stock-location-strategy.ts:79-106 "getLocationsBasedOnAllocations": sales and releases are taken from the line\'s allocations'),
    // Stated first for every state, this law was refuted: a sale before the line's stock level row exists creates the
    // row with stockOnHand = -quantity while the stockAllocated update finds no row and does nothing (the original does
    // this, repro/conform-vendure.ts). A law error: a variant's level is created with the variant
    // (adjustProductVariantStock), so the documented behaviour is about a level that exists.
    stepLaw(r, r.stepLaw('once the stock level exists, a sale takes from the allocated stock exactly what it takes from stock on hand', ({onHand, allocated}, after) => onHand.minus(after.onHand).eq(allocated.minus(after.allocated)),
      ({op, level}) => op.is('sale').and(level)),
    'step', 'docs', 'stock-movement.service.ts:180-183 "the stockAllocated value is reduced and the stockOnHand value is also reduced by the OrderLine quantity"'),
    stepLaw(r, r.stepLaw('stock of a variant that does not track inventory moves only by adjustment', ({onHand, allocated}, after) => after.onHand.eq(onHand).and(after.allocated.eq(allocated)),
      ({op, track}) => track.not().and(op.is('adjust').not())),
    'step', 'docs', 'stock-movement.service.ts:143-147 "For ProductVariants which are configured to track stock levels, the ProductVariant.stockAllocated value is increased"'),
  ],
}]
