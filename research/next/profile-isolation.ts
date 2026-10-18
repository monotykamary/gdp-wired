import {prove} from '../../core/machine.ts'
import {all, any, bit, get, ite, n, not, same, x, type Law} from '../../core/machine.ts'
import {admitFlagged} from '../../core/models.ts'
import {product} from './relational.ts'
const base = admitFlagged()
const mine = all(same(x('who'), n(0)), same(x('acct'), x('Bacct')), same(x('day'), x('Bday')), same(x('hour'), x('Bhour')), same(x('dom'), x('Bdom')))
const others = all(same(x('who'), n(1)), not(same(x('acct'), x('Bacct'))), not(same(x('day'), x('Bday'))), not(same(x('hour'), x('Bhour'))), not(same(x('dom'), x('Bdom'))))
const m = product(base, base, {name: 'isolation', params: ['Bacct', 'Bday', 'Bhour', 'Bdom'], inputs: ['who'], bInputs: {ok: ite(same(x('who'), n(1)), n(0), x('ok'))}, assume: all(bit('who'), any(mine, others))})
const sees: Law = {name: 'sees', holds: same(get('a_Acct', x('Bacct')), get('b_Acct', x('Bacct')))}
const atB = (k: string, key: string): Law => ({name: k, holds: same(get(`a_${k}`, x(key)), get(`b_${k}`, x(key)))})
const p = prove(m, sees, [sees, atB('Day', 'Bday'), atB('Hour', 'Bhour'), atB('Dom', 'Bdom')])
console.log('proven', p.proven, 'obligations', p.obligations.length)
