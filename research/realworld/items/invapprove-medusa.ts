// Medusa v2.22.0, the inventory module's reservations (packages/modules/inventory). MIT, (c) MedusaJS (the module is
// outside the Enterprise paths ENTERPRISE-LICENSE.md lists).
// https://github.com/medusajs/medusa/blob/205aff40bacfa0049e0b9d3a7913a674738bff31/packages/modules/inventory/src/services/inventory-module.ts
//
// One inventory item's levels, one per location (stocked_quantity, reserved_quantity; available = stocked - reserved,
// repositories/inventory-level.ts:44-52 and utils/apply-decorators.ts:16-20), and its reservation items. A call that
// throws (a MedusaError) runs in one transaction (@InjectTransactionManager): nothing changes, which the step says as
// "every part keeps its value". Line numbers are inventory-module.ts's unless another file is named.
import {Int, bool, forall, int, maybe, nat, no, oneOf, rule, when} from '../../../core/dsl.ts'
import {type RealItem, invariant, leadsTo, stepLaw} from '../lib.ts'

const src = {repo: 'medusajs/medusa', commit: '205aff40bacfa0049e0b9d3a7913a674738bff31', licence: 'MIT', author: 'MedusaJS', language: 'TypeScript'}
const mod = 'packages/modules/inventory/src'

export const reservations = () => rule('Medusa inventory reservations')
  // `d`: the reservation a liveness law watches (not the code's).
  .params({d: nat})
  // One call. `loc`, `q`, `back`: a reservation's location_id, quantity and allow_backorder (createReservationItems; a
  // batch of two at one location is `q2`, `back2`); `id`: the reservation updated, deleted or restored; `newQ`,
  // `newLoc`, `newBack`: an update's optional quantity, location_id and allow_backorder (UpdateReservationItemInput);
  // `adj`: adjustInventory's adjustment, or the stocked_quantity of createInventoryLevels / updateInventoryLevels.
  .inputs({
    op: oneOf('level', 'create', 'create2', 'update', 'delete', 'softDelete', 'restore', 'adjust', 'setStocked'),
    loc: nat, q: nat, back: bool, q2: nat, back2: bool, id: nat, newQ: maybe(nat), newLoc: maybe(nat), newBack: maybe(bool), adj: int,
  })
  // The next reservation id (ids are generated: a create never reuses one).
  .state({next: 0})
  .maps({
    // models/inventory-level.ts:4-15: a level per (item, location), unique (:28-33); stocked and reserved default 0.
    Lvl: bool.from(false), Stocked: int.from(0), Reserved: int.from(0),
    // models/reservation-item.ts:4-21: quantity, location_id, allow_backorder, and the row's state (soft deleted:
    // deleted_at set; hard deleted: gone).
    Res: oneOf('none', 'live', 'deleted').from('none'), ResQty: 0, ResLoc: 0, ResBack: bool.from(false),
    // Ghost: the quantity of the live reservations at each location, as the reservation table says.
    Live: int.from(0),
  })
  .flags(({op, loc, q, back, q2, back2, id, newQ, newLoc, newBack, Lvl, Stocked, Reserved, Res, ResQty, ResLoc, ResBack}) => {
    const avail = (k: typeof loc) => Stocked.at(k).minus(Reserved.at(k))
    // :173-191 ensureInventoryLevels with validateQuantityAtLocation: a missing level throws (:160-171); unless
    // allow_backorder, `available_quantity < quantity` throws. Each item of a batch is checked against the level as
    // read before the batch (:183-185), not against what the batch's earlier items reserve.
    const fits = (k: typeof loc, n: typeof q, b: typeof back) => b.or(avail(k).atLeast(n))
    const rq = ResQty.at(id), rl = ResLoc.at(id)
    // :656-672: the location checked is `data.location_id ?? reservation.location_id`; the quantity is
    // `data.quantity ? data.quantity - reservation.quantity : 0`, at least 0; backorder `data.allow_backorder ||
    // reservation.allow_backorder`.
    const at = newLoc.match({none: () => rl, some: l => l})
    const more = newQ.match({none: () => 0, some: n => n.minus(rq)})
    const backs = newBack.match({none: () => ResBack.at(id), some: b => b.or(ResBack.at(id))})
    return {
      // createInventoryLevels_ (:388-407): the unique index refuses a second level at a location.
      levels: op.is('level').and(Lvl.at(loc).not()),
      creates: op.is('create').and(Lvl.at(loc), fits(loc, q, back)),
      creates2: op.is('create2').and(Lvl.at(loc), fits(loc, q, back), fits(loc, q2, back2)),
      // :596-606: an id not found (soft-deleted rows are filtered out) throws; then :674-680 ensureInventoryLevels.
      updates: op.is('update').and(Res.at(id).is('live'), Lvl.at(at), backs.or(avail(at).atLeast(more))),
      // :725-741 / :752-769: the reservations listed (live ones) adjust their levels.
      deletes: op.is('delete').and(Res.at(id).is('live')),
      softDeletes: op.is('softDelete').and(Res.at(id).is('live')),
      // :780-796: restore, then list the ids (now live, and any that were live already) and add them back.
      restores: op.is('restore').and(Res.at(id).is('none').not()),
      // :969-1001 adjustInventory_: a missing level throws; stocked_quantity += adjustment.
      adjusts: op.is('adjust').and(Lvl.at(loc)),
      // :516-552 updateInventoryLevels_: reserved_quantity is sanitized away (:197-209); stocked_quantity is set.
      sets: op.is('setStocked').and(Lvl.at(loc)),
    }
  })
  .step(({op, loc, q, back, q2, back2, id, newQ, newLoc, newBack, adj, next, Lvl, Stocked, Reserved, Res, ResQty, ResLoc, ResBack, Live,
    levels, creates, creates2, updates, deletes, softDeletes, restores, adjusts, sets}) => {
    const rq = ResQty.at(id), rl = ResLoc.at(id)
    const at = newLoc.match({none: () => rl, some: l => l})
    const moves = newLoc.match({none: () => no, some: l => l.eq(rl).not()})
    // :617-652: moving adds `update.quantity || reservation.quantity` at the new location (and subtracts the old
    // quantity at the old one); otherwise a defined quantity that differs adds `update.quantity - reservation.quantity`.
    const movedQty = newQ.match({none: () => rq, some: n => when(n.eq(0), rq, n)})
    const qty = newQ.match({none: () => rq, some: n => n}) // the row's new quantity (reservationItemService_.update)
    const loc2 = at
    // :684-702: the adjustments are applied only to the levels ensureInventoryLevels returned (:674-680), which are the
    // levels at the checked location: on a move, the old location's adjustment is computed and never applied.
    const updDelta = when(moves, Int.of(movedQty), Int.of(qty).minus(rq))
    const isLive = Res.at(id).is('live'), wasDeleted = Res.at(id).is('deleted')
    return {
      next: when(creates, next.plus(1), when(creates2, next.plus(2), next)),
      Lvl: Lvl.set(loc, Lvl.at(loc).or(levels)),
      Stocked: Stocked.set(loc, when(levels.or(sets), adj, when(adjusts, Stocked.at(loc).plus(adj), Stocked.at(loc)))),
      Reserved: Reserved.each(k => {
        const r = Reserved.at(k)
        return when(creates.and(k.eq(loc)), r.plus(q),
          when(creates2.and(k.eq(loc)), r.plus(q).plus(q2),
            when(updates.and(k.eq(loc2)), r.plus(updDelta),
              // :1179-1229: a deletion subtracts each listed reservation's quantity, a restore adds it.
              when(deletes.or(softDeletes).and(k.eq(rl)), r.minus(rq),
                when(restores.and(isLive.or(wasDeleted)).and(k.eq(rl)), r.plus(rq), r)))))
      }),
      Live: Live.each(k => {
        const l = Live.at(k)
        return when(creates.and(k.eq(loc)), l.plus(q),
          when(creates2.and(k.eq(loc)), l.plus(q).plus(q2),
            when(updates, when(k.eq(rl), l.minus(rq), l).plus(when(k.eq(loc2), qty, 0)),
              when(deletes.or(softDeletes).and(k.eq(rl)), l.minus(rq),
                when(restores.and(wasDeleted).and(k.eq(rl)), l.plus(rq), l)))))
      }),
      // :282 reservationItemService_.create; :682 update; delete (hard) and softDelete; restore.
      Res: Res.each(k => when(creates.and(k.eq(next)).or(creates2.and(k.eq(next).or(k.eq(next.plus(1))))), 'live',
        // :725-735: a hard delete removes the row, soft deleted or not (only live rows adjust a level).
        when(k.eq(id).and(op.is('delete')), 'none',
          when(softDeletes.and(k.eq(id)), 'deleted', when(restores.and(k.eq(id)), 'live', Res.at(k)))))),
      ResQty: ResQty.each(k => when(creates.or(creates2).and(k.eq(next)), q, when(creates2.and(k.eq(next.plus(1))), q2, when(updates.and(k.eq(id)), qty, ResQty.at(k))))),
      ResLoc: ResLoc.each(k => when(creates.or(creates2).and(k.eq(next)).or(creates2.and(k.eq(next.plus(1)))), loc, when(updates.and(k.eq(id)), at, ResLoc.at(k)))),
      ResBack: ResBack.each(k => when(creates.or(creates2).and(k.eq(next)), back, when(creates2.and(k.eq(next.plus(1))), back2,
        when(updates.and(k.eq(id)), newBack.match({none: () => ResBack.at(k), some: b => b}), ResBack.at(k))))),
    }
  })

const r = reservations()
const cite = (path: string, lines: string, exp: string) => ({...src, path: `${mod}/${path}`, lines, export: exp})
export const items: RealItem[] = [{
  id: 'inventory/medusa/reservations',
  domain: 'inventory',
  source: cite('services/inventory-module.ts', '102-1229', 'InventoryModuleService'),
  also: [cite('repositories/inventory-level.ts', '33-54', 'InventoryLevelRepository.getAvailableQuantity'), cite('models/inventory-level.ts', '4-33', 'InventoryLevel'),
    cite('models/reservation-item.ts', '4-21', 'ReservationItem'), cite('utils/apply-decorators.ts', '12-24', 'applyHook')],
  summary: 'Reservations hold stock at a location: creating or growing one checks the level\'s available quantity unless it allows backorders; deleting, soft-deleting and restoring one moves reserved_quantity back.',
  expressible: 'partial',
  gaps: [
    {gap: 'other', blocks: 'part', detail: 'quantities are BigNumber decimals (fractional quantities are tested); the rule uses integers, and a request\'s quantities are naturals (the module itself does not check signs)'},
    {gap: 'unbounded-collection', blocks: 'part', detail: 'a batch of any length (createReservationItems, updateReservationItems, delete by line item or location) is one item or, for creation, two at one location; one inventory item'},
    {gap: 'external', blocks: 'part', detail: 'soft delete and restore are MikroORM\'s (deleted_at filtered out of list): restore of an id already live is assumed to leave it live and the list to return it'},
  ],
  laws: [
    stepLaw(r, r.stepLaw('a reservation created without backorder never takes more than is available', ({loc, Stocked}, after) => after.Reserved.at(loc).atMost(Stocked.at(loc)),
      ({creates, back}) => creates.and(back.not())),
    'step', 'tests', 'inventory-module-service.spec.ts:147 "should check inventory levels before creating reservation"'),
    stepLaw(r, r.stepLaw('a batch created without backorder never takes more than is available', ({loc, Stocked}, after) => after.Reserved.at(loc).atMost(Stocked.at(loc)),
      ({creates2, back, back2}) => creates2.and(back.not(), back2.not())),
    'step', 'inferred', 'createReservationItems takes an array (spec.ts:182 "should create reservationItems from array"); the availability check is meant to hold for what it reserves'),
    // At the location the reservation ends up at: within the stock, or no higher than before (an update that lowers an
    // already oversold level is fine).
    stepLaw(r, r.stepLaw('an update without backorder never takes more than is available where the reservation ends up', ({id, Stocked, Reserved}, after) => {
      const at = after.ResLoc.at(id)
      return after.Reserved.at(at).atMost(Stocked.at(at)).or(after.Reserved.at(at).atMost(Reserved.at(at)))
    }, ({updates, id, newBack, ResBack}) => updates.and(ResBack.at(id).not(), newBack.match({none: () => no, some: b => b}).not())),
    'step', 'tests', 'spec.ts:584 "should throw error when increasing reserved quantity beyond availability"'),
    invariant(r, r.law('the reserved quantity at a location is what its live reservations hold', ({Reserved, Live}) => forall(k => Reserved.at(k).eq(Live.at(k)))),
      'safety', 'docs', 'inventory-module.ts:197 "reserved_quantity should solely be handled through creating & updating reservation items"'),
    stepLaw(r, r.stepLaw('only reservations change the reserved quantity', ({Reserved}, after) => forall(k => after.Reserved.at(k).eq(Reserved.at(k))),
      ({op}) => op.is('adjust').or(op.is('setStocked'), op.is('level'))),
    'access', 'docs', 'inventory-module.ts:197-198 "We sanitize the inputs here to prevent that from being used to update it"'),
    leadsTo(r, r.leadsTo('every live reservation can be released', {
      from: ({Res, d}) => Res.at(d).is('live'),
      to: ({Res, d}) => Res.at(d).is('live').not(),
      helpful: ({d}) => ({op: 4, id: d}),
    }), 'tests', 'spec.ts:637 "should delete reservation items by id"'),
  ],
}]
