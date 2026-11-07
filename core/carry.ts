// Syntax-derived proposals only. Neither a copied guard nor a co-write is a trusted
// transition fact: counts.ts applies its ordinary scope/sample filter and kernel proof.
import {type C, type E, type Law, type Machine, all, any, not, same, less, n, x, walk} from './machine.ts'
import {scope, substC, substE} from '../kernel/kernel.ts'

// Shared with comparisons(): keep its existing IF-leaf / truncated-subtraction behavior.
export function storedInputs(m: Machine): Map<string, string> {
  const out = new Map<string, string>()
  const leaves = (e: E, to: string): void => { if (e.op === 'var') { if (m.inputs.includes(e.name) && !out.has(e.name)) out.set(e.name, to) } else if (e.op === 'if') { leaves(e.then, to); leaves(e.else, to) } }
  for (const [v, e] of Object.entries(m.step.state ?? {})) leaves(e.op === 'sub' ? e.a : e, v)
  return out
}
const json = (v: unknown) => JSON.stringify(v)
const eq = (a: unknown, b: unknown) => json(a) === json(b)
const yes: C = same(n(0), n(0)), no: C = not(yes)
const vars = (t: unknown): string[] => { const out = new Set<string>(); walk(t, o => { if (o.op === 'var' && typeof o.name === 'string') out.add(o.name) }); return [...out] }
const flat = (c: C, op: 'and' | 'or'): C[] => c.op === op ? c.xs.flatMap(q => flat(q, op)) : [c]
// Partial evaluation at an entry guard also recognizes the DSL's Boolean-map encoding.
function simplify(c: C, at: C = yes, value = true): C {
  if (eq(c, at)) return value ? yes : no
  if (c.op === 'not') { const q = simplify(c.x, at, value); return eq(q, yes) ? no : eq(q, no) ? yes : q.op === 'not' ? q.x : not(q) }
  if (c.op === 'and' || c.op === 'or') {
    const unit = c.op === 'and' ? yes : no, zero = c.op === 'and' ? no : yes
    const qs = flat(c, c.op).map(q => simplify(q, at, value))
    if (qs.some(q => eq(q, zero)) || qs.some(q => qs.some(r => eq(q, not(r))))) return zero
    const xs = [...new Map(qs.filter(q => !eq(q, unit)).map(q => [json(q), q])).values()]
    return xs.length === 0 ? unit : xs.length === 1 ? xs[0]! : {op: c.op, xs}
  }
  if ((c.op === '=' || c.op === '<' || c.op === '<=') && c.a.op === 'const' && c.b.op === 'const')
    return (c.op === '=' ? c.a.value === c.b.value : c.op === '<' ? c.a.value < c.b.value : c.a.value <= c.b.value) ? yes : no
  return c
}
function atGuard(e: E, guard: C): E {
  if (e.op !== 'if') return e
  const c = simplify(e.c, guard), a = atGuard(e.then, guard), b = atGuard(e.else, guard)
  return eq(c, yes) ? a : eq(c, no) ? b : {op: 'if', c, then: a, else: b}
}
type Cell = Extract<E, {op: 'get'}>
function positive(c: C): Cell | undefined {
  // The cube engine writes 0 + 1 <= 0 + cell; compare that same atom, not its spelling.
  const bare = (e: E): E => e.op === 'add' && eq(e.a, n(0)) ? bare(e.b) : e.op === 'add' && eq(e.b, n(0)) ? bare(e.a) : e
  if (c.op === '<=') { const a = bare(c.a), b = bare(c.b); if (eq(a, n(1)) && b.op === 'get') return b }
  if (c.op === '=') { const a = bare(c.a), b = bare(c.b); if (eq(b, n(1)) && a.op === 'get') return a }
  if (c.op === 'not' && c.x.op === '=') { const a = bare(c.x.a), b = bare(c.x.b); if (eq(b, n(0)) && a.op === 'get') return a }
  return undefined
}
// Small CNF expansion, bounded independently of proof/search budgets; incomplete is fine.
function clauses(c: C, flags: Record<string, C>, bound: Set<string>, depth = 0, fuel = {left: 4096}): C[][] {
  if (depth > 24 || --fuel.left < 0) return []
  if (c.op === 'flag') { const q = flags[c.name]; return q ? clauses(q, flags, bound, depth + 1, fuel) : [[c]] }
  if (c.op === 'all') { for (const k of [c.key, ...(c.keys ?? [])]) bound.add(k); return clauses(c.c, flags, bound, depth + 1, fuel) }
  if (c.op === 'not' && c.x.op === 'flag') { const q = flags[c.x.name]; return q && q.op !== 'all' ? clauses(not(q), flags, bound, depth + 1, fuel) : [[c]] }
  if (c.op === 'not' && c.x.op === 'not') return clauses(c.x.x, flags, bound, depth + 1, fuel)
  if (c.op === 'not' && (c.x.op === 'and' || c.x.op === 'or')) return clauses({op: c.x.op === 'and' ? 'or' : 'and', xs: c.x.xs.map(not)}, flags, bound, depth + 1, fuel)
  if (c.op === 'and') {
    const out: C[][] = []
    for (const q of c.xs) { if (out.length >= 64 || fuel.left <= 0) break; out.push(...clauses(q, flags, bound, depth + 1, fuel).slice(0, 64 - out.length)) }
    return out
  }
  if (c.op === 'or') {
    let out: C[][] = [[]]
    for (const q of c.xs) { const cs = clauses(q, flags, bound, depth + 1, fuel); if (!cs.length || out.length * cs.length > 64) return []; out = out.flatMap(a => cs.map(b => [...a, ...b])) }
    return out
  }
  return [[c]]
}
// Linear packed-key matching: match by coefficient, not association or variable names.
function linear(e: E, k = 1, out = new Map<string, number>()): Map<string, number> | undefined {
  if (e.op === 'var') { out.set(e.name, (out.get(e.name) ?? 0) + k); return out }
  if (e.op === 'const') return e.value === 0 ? out : undefined
  if (e.op === 'mul') return linear(e.a, k * e.k, out)
  return e.op === 'add' && linear(e.a, k, out) ? linear(e.b, k, out) : undefined
}
function match(pattern: E, actual: E): Record<string, E> | undefined {
  const p = linear(pattern), a = linear(actual)
  if (!p || !a || p.size !== a.size || new Set(p.values()).size !== p.size || new Set(a.values()).size !== a.size) return
  const out: Record<string, E> = {}
  for (const [v, k] of p) { const w = [...a].find(([, j]) => j === k); if (!w) return; out[v] = x(w[0]) }
  return out
}
export function carryCandidates(m: Machine, occupied: readonly Law[] = [], audit: GlobalAudit = {rows:[],work:0,exhausted:false}): Law[] {
  const flags = m.step.flags ?? {}, copies = storedInputs(m), out = new Map<string, Law>()
  // Bound unsuccessful generation as well as output; local to this invocation.
  let work = 0
  const more = () => { if(work>=8192){audit.exhausted=true;return false}audit.work=++work;return out.size<128 }
  const taken = new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...(m.inputMaps ?? [])])
  walk(m, o => { if (typeof o.name === 'string') taken.add(o.name); if (typeof o.key === 'string') taken.add(o.key) })
  const fresh = () => { let s = 'carryKey'; while (taken.has(s)) s += 'X'; taken.add(s); return s }
  const add = (holds: C, bound: Set<string>, family: string) => {
    if (out.size >= 128) return // proposal cap only; never a proof/search budget
    const ks = vars(holds).filter(v => bound.has(v)), signature = json([ks, holds])
    let h = 14695981039346656037n
    for (let i = 0; i < signature.length; i++) h = BigInt.asUintN(64, (h ^ BigInt(signature.charCodeAt(i))) * 1099511628211n)
    const name = `carry:${family}:${h.toString(16)}`
    const l: Law = {name, holds, ...(ks.length ? {forall: ks[0]!, ...(ks.length > 1 ? {keys: ks.slice(1)} : {})} : {})}
    if (occupied.some(l => l.name === name)) return
    try { scope(m, [l]) } catch { return }
    const prev = out.get(name)
    if (prev && !eq(prev, l)) { out.delete(name); return }
    out.set(name, l)
  }
  const bridges: {from: Cell, to: Cell}[] = []
  bridges: for (const law of occupied) for (const row of clauses(law.holds, {}, new Set())) {
    if (!more()) return [...out.values()]
    for (const a of row) if (a.op === 'not') { const from = positive(a.x); if (from) for (const b of row) { const to = positive(b); if (to && to.map !== from.map && bridges.length < 64) { bridges.push({from, to}); if (bridges.length === 64) break bridges } } }
  }
  for (const [mode, w] of Object.entries(m.step.state ?? {})) {
    if (!more()) return [...out.values()]
    if (w.op !== 'if' || w.then.op !== 'const') continue
    const sub = {vars: {} as Record<string, E>, maps: {} as Record<string, (key: E) => E>, flags: {}}
    for (const [input, target] of copies) {
      const e = m.step.state?.[target]
      if (e?.op === 'if' && eq(e.c, w.c) && eq(e.then, x(input))) sub.vars[input] = x(target)
    }
    if (!Object.keys(sub.vars).length) continue
    for (const [target, update] of Object.entries(m.step.maps ?? {})) if ('each' in update) {
      const e = atGuard(update.value, w.c), cell = e.op === 'get' ? e : e.op === 'if' && eq(e.then, n(1)) && eq(e.else, n(0)) ? positive(e.c) : undefined
      if (cell && m.inputMaps?.includes(cell.map) && eq(cell.key, x(update.each))) sub.maps[cell.map] = key => ({op: 'get', map: target, key})
    }
    const bound = new Set<string>(), active = same(x(mode), w.then)
    const source = clauses(all(w.c, ...(m.assume ? [m.assume] : [])), flags, bound)
    for (const row of source) {
      if (!more()) return [...out.values()]
      const variants = [row]
      for (let i = 0; i < row.length; i++) { const c = positive(row[i]!); if (!c) continue
        for (const b of bridges) if (c.map === b.from.map) { if (!more()) return [...out.values()]; const vs = match(b.from.key, c.key); if (vs) variants.push(row.map((q, j): C => j === i ? {op: '<=', a: n(1), b: substE(b.to, {vars: vs, maps: {}, flags: {}})} : q)) }
      }
      for (const rs of variants) {
        if (!more()) return [...out.values()]
        const raw = any(...rs), names = vars(raw)
        // The entry's old control state is not the new stored state. Unretained inputs
        // make this whole CNF clause unavailable; never erase a disjunct to strengthen it.
        if (names.some(v => v in m.state) || !names.some(v => v in sub.vars) && !Object.keys(sub.maps).some(mp => json(raw).includes(`"map":${json(mp)}`))) continue
        if (rs.some(q => q.op === 'flag' || q.op === 'not' && q.x.op === 'flag')) continue
        const c = substC(raw, sub)
        add(any(not(active), c), bound, 'guard')
      }
    }
  }
  // Co-written monotone point and interval maps. Keep the source interval and input
  // bounds; no protocol names, guessed domain constants, or invariant seeds.
  const inserts = (map: string, key: E, value: E): C[][] => {
    if (value.op !== 'if' || !eq(value.then, n(1)) || !eq(value.else, n(0))) return []
    const c = simplify(value.c), branches = clauses(not(c), {}, new Set()).map(row => row.map(q => simplify(not(q))))
    return branches.filter(row => !row.some(q => json(q).includes(json({op: 'get', map, key}))))
  }
  for (const [mp, point] of Object.entries(m.step.maps ?? {})) {
    if (!more()) return [...out.values()]
    if ('each' in point) continue
    const ps = vars(point.key)
    if (!ps.length || ps.some(v => !m.inputs.includes(v))) continue
    for (const g of inserts(mp, point.key, point.value)) for (const [other, interval] of Object.entries(m.step.maps ?? {})) {
      if (!more()) return [...out.values()]
      if (!('each' in interval)) continue
      for (const row of inserts(other, x(interval.each), interval.value)) {
        if (!more()) return [...out.values()]
        if (!g.every(q => row.some(r => eq(q, r)))) continue
        const rest = row.filter(q => !g.some(r => eq(q, r)))
        const lo = rest.find((q): q is C & {op: '<='} => q.op === '<=' && eq(q.b, x(interval.each)))
        const hi = rest.find((q): q is C & {op: '<'} => q.op === '<' && eq(q.a, x(interval.each)))
        if (!lo || !hi || rest.length !== 2 || hi.b.op !== 'add' || !eq(hi.b.a, lo.a)) continue
        const z = fresh(), names = ps.map(() => fresh()), vs = Object.fromEntries(ps.map((p, i) => [p, x(names[i]!)])), bound = new Set([...names, z])
        const s = {vars: {...vs, [interval.each]: {op: 'add', a: lo.a, b: x(z)} as E}, maps: {}, flags: {}}
        const domains = m.assume ? clauses(m.assume, {}, new Set()).filter(r => vars(r).every(v => ps.includes(v) || m.params.includes(v))).map(r => any(...r)) : []
        const hyp = all(...domains, {op: '<', a: x(z), b: hi.b.b}, {op: '<=', a: n(1), b: {op: 'get', map: mp, key: point.key}})
        // Substitute the interval key before the point variables (substitution is simultaneous).
        const cell = substE(substE({op: 'get', map: other, key: x(interval.each)}, s), {vars: vs, maps: {}, flags: {}})
        add(any(not(substC(hyp, {vars: vs, maps: {}, flags: {}})), {op: '<=', a: n(1), b: cell}), bound, 'co-write')
      }
    }
  }
  // New rules are appended; existing guarded/co-write candidates and their order survive.
  // Only unconditional transition input bounds are used. m.pre is param-only by scope.
  const pre=flat(m.pre??yes,'and'),transition=flat(m.assume??yes,'and')
  const paramOnly=(e:unknown)=>vars(e).every(v=>m.params.includes(v))&&!json(e).includes('"op":"get"')&&!json(e).includes('"op":"flag"')
  const bounds=transition.filter((c):c is C & {op:'<'}=>c.op==='<'&&c.a.op==='var'&&m.inputs.includes(c.a.name)&&paramOnly(c.b))
  for(const [target,update]of Object.entries(m.step.state??{}))for(const b of bounds){
    if(!more())return [...out.values()]
    const input=(b.a as E & {op:'var'}).name,bound=b.b,allowedInputs=new Set(bounds.filter(q=>eq(q.b,bound)).map(q=>(q.a as E & {op:'var'}).name))
    const safe=(e:E)=>boundKnown(e,bound,pre)
    let copied=false
    const leaves=(e:E,depth=0):boolean=>{if(!more()||depth>48)return false;if(e.op==='if')return leaves(e.then,depth+1)&&leaves(e.else,depth+1);if(e.op==='var'&&e.name===target)return true;if(e.op==='var'&&allowedInputs.has(e.name)){copied=true;return true}return safe(e)}
    if(!safe(m.state[target]!)){audit.rows.push({rule:'range',target,input,accepted:false,reason:'initial bound not established'});continue}
    const accepted=leaves(update)&&copied
    audit.rows.push({rule:'range',target,input,accepted,reason:accepted?'all leaves preserve exact source bound':'unsafe or unbounded update leaf'})
    if(accepted)add({op:'<',a:x(target),b:bound},new Set(),'global-range')
  }
  const guarded=[...out.values()]
  for(const l of guarded){
    if(!more())return [...out.values()]
    if(l.holds.op!=='or'||l.holds.xs.length!==2)continue
    const [g,body]=l.holds.xs
    if(g?.op!=='not'||g.x.op!=='='||g.x.a.op!=='var'||g.x.b.op!=='const'||!body)continue
    const mode=g.x.a.name,entry=m.step.state?.[mode]
    if(entry?.op!=='if'||!eq(entry.then,g.x.b))continue
    const qs=flat(body,'or'),negative=qs.flatMap(q=>{const atom=q.op==='not'?q.x:not(q),cell=positiveExact(atom);return cell?[{atom,cell,clause:q}]:[]}),positive=qs.flatMap(q=>positiveExact(q)?[{atom:q,cell:positiveExact(q)!}]:[])
    if(negative.length!==1||positive.length!==1)continue
    const domain=negative[0]!,range=positive[0]!
    if(domain.cell.map===range.cell.map||qs.some(q=>q!==domain.clause&&q!==range.atom&&json(q).includes('"op":"get"')))continue
    const update=m.step.maps?.[domain.cell.map],persistent=m.step.maps?.[range.cell.map]
    if(!update||!('each'in update)||!persistent||m.maps?.[domain.cell.map]!==0||domain.cell.key.op!=='var')continue
    const entryFacts=factsWith(new Map(),entry.c,true),entryValue=foldE(update.value,entryFacts,more)
    let sourceCell:Cell|undefined
    if(entryValue?.op==='get'&&m.inputMaps?.includes(entryValue.map)&&eq(entryValue.key,x(update.each)))sourceCell=entryValue
    else if(entryValue?.op==='if'&&eq(entryValue.then,n(1))&&eq(entryValue.else,n(0))){
      const p=positiveExact(entryValue.c)
      if(p&&m.inputMaps?.includes(p.map)&&eq(p.key,x(update.each))){
        const inverse=substC(domain.atom,{vars:{[domain.cell.key.name]:x(update.each)},maps:{[domain.cell.map]:key=>({op:'get',map:p.map,key})},flags:{}})
        // No Eq1/>=1/nonzero normalization is permitted across the copy.
        if(eq(inverse,entryValue.c))sourceCell=p
      }
    }
    if(!sourceCell){audit.rows.push({rule:'frame',target:l.name,accepted:false,reason:'copy predicate is not exact'});continue}
    const oldCell:Cell={op:'get',map:range.cell.map,key:'each'in persistent?x(persistent.each):persistent.key},atOld=replaceCell(range.atom,range.cell,oldCell),post=replaceCell(range.atom,range.cell,persistent.value)
    const retained=foldC(post,factsWith(new Map(),atOld,true),more)
    if(!retained||!eq(retained,yes)){audit.rows.push({rule:'frame',target:l.name,accepted:false,reason:'consequent positivity not preserved'});continue}
    const fields=vars(body).filter(v=>v in m.state),oldDomain:Cell={op:'get',map:domain.cell.map,key:x(update.each)},oldAtom=substC(domain.atom,{vars:{[domain.cell.key.name]:x(update.each)},maps:{},flags:{}})
    const outside=factsWith(new Map(),entry.c,false)
    const framed=(e:E,fs:Facts,depth=0):boolean=>{
      if(!more()||depth>48)return false
      const value=foldE(e,fs,more);if(!value)return false
      if(value.op==='if')return framed(value.then,factsWith(fs,value.c,true),depth+1)&&framed(value.else,factsWith(fs,value.c,false),depth+1)
      const after=foldC(replaceCell(oldAtom,oldDomain,value),fs,more)
      if(after&&eq(after,no))return true
      const prior=foldC(oldAtom,fs,more)
      if(!eq(value,oldDomain)&&(!prior||!eq(prior,yes)))return false
      return fields.every(v=>{const post=foldE(m.step.state?.[v]??x(v),fs,more);return !!post&&eq(post,x(v))})
    }
    const accepted=framed(update.value,outside)
    audit.rows.push({rule:'frame',target:l.name,accepted,reason:accepted?'empty init, exact entry copy, clear-or-frame, persistent positive target':'outside-entry path unframed'})
    if(accepted)add(body,new Set([l.forall,...(l.keys??[])].filter((v):v is string=>!!v)),'global-frame')
  }
  // Appended point/point proposals: syntax is eligibility, never a transition fact.
  // Accept only the two exact Boolean retention shapes; no arbitrary self read.
  const insertion=(map:string,key:E,value:E):C|undefined=>{
    if(!more()||value.op!=='if'||!eq(value.then,n(1))||!eq(value.else,n(0)))return
    const branches=flat(simplify(value.c),'or'),prior=same({op:'get',map,key},n(1))
    if(branches.length!==2)return
    for(let i=0;i<2;i++){
      const guard=branches[i]!,retained=branches[1-i]!
      if(eq(retained,prior)||eq(retained,simplify(all(not(guard),prior))))return guard
    }
    return
  }
  // Complete, bounded expansion of plain flags only. In particular an OR keeps
  // every arm, and quantified/opaque/cyclic flags cannot supply a free binder.
  const plain=(c:C,depth=0):C|undefined=>{
    if(!more()||depth>24||c.op==='all')return
    if(c.op==='flag'){const q=flags[c.name];return q?plain(q,depth+1):undefined}
    if(c.op==='not'){const q=plain(c.x,depth+1);return q?not(q):undefined}
    if(c.op==='and'||c.op==='or'){
      const xs:C[]=[];for(const x of c.xs){const q=plain(x,depth+1);if(!q)return;xs.push(q)}
      return {op:c.op,xs}
    }
    return c
  }
  for(const [source,point]of Object.entries(m.step.maps??{})){
    if(!more())return [...out.values()]
    if('each'in point||m.maps?.[source]!==0)continue
    const ps=vars(point.key),affine=linear(point.key)
    if(!ps.length||!affine||[...affine.values()].some(k=>!Number.isSafeInteger(k)||k<=0)||ps.some(p=>!m.inputs.includes(p)))continue
    const domains=bounds.filter(b=>ps.includes((b.a as E & {op:'var'}).name))
    if(ps.some(p=>!domains.some(b=>eq(b.a,x(p)))))continue
    const guard=insertion(source,point.key,point.value),expanded=guard&&plain(guard)
    if(!expanded)continue
    const names=ps.map(()=>fresh()),at={vars:Object.fromEntries(ps.map((p,i)=>[p,x(names[i]!)])),maps:{},flags:{}},bound=new Set(names)
    // Only necessary unit conjuncts are eligible, never one selected OR arm.
    for(const atom of flat(expanded,'and')){
      if(!more())return [...out.values()]
      if(atom.op!=='=')continue
      const dest=eq(atom.b,n(1))&&atom.a.op==='get'?atom.a:eq(atom.a,n(1))&&atom.b.op==='get'?atom.b:undefined
      if(!dest||dest.map===source||!Object.hasOwn(m.maps??{},dest.map)||!linear(dest.key)||vars(dest.key).some(p=>!ps.includes(p)&&!m.params.includes(p)))continue
      const update=m.step.maps?.[dest.map]
      if(!update||'each'in update||!insertion(dest.map,update.key,update.value))continue
      const hyp=all(...domains,{op:'<=',a:n(1),b:{op:'get',map:source,key:point.key}}),size=out.size
      add(substC(any(not(hyp),same(dest,n(1))),at),bound,'point-guard')
      if(out.size>size)audit.rows.push({rule:'point-guard',target:source,accepted:true,reason:'exact insertion guard, persistent-one destination, source bounds; proposal only'})
    }
  }
  return [...out.values()]
}

// Eligibility checks only. Output clauses are never normalized or trusted.
export type GlobalAudit={rows:{rule:string,target:string,input?:string,accepted:boolean,reason:string}[],work:number,exhausted:boolean}
type Facts=Map<string,{c:C,value:boolean}>
function factsWith(fs:Facts,c:C,value:boolean):Facts{
 const out=new Map(fs)
 const add=(q:C,v:boolean,depth=0):void=>{if(depth>48)return;out.set(json(q),{c:q,value:v});if(q.op==='not')add(q.x,!v,depth+1);else if(q.op==='and'&&v||q.op==='or'&&!v)for(const x of q.xs)add(x,v,depth+1)}
 add(c,value);return out
}
function positiveExact(c:C):Cell|undefined{
 if(c.op==='='&&eq(c.b,n(1))&&c.a.op==='get')return c.a
 if(c.op==='='&&eq(c.a,n(1))&&c.b.op==='get')return c.b
 if(c.op==='<='&&eq(c.a,n(1))&&c.b.op==='get')return c.b
 if(c.op==='not'&&c.x.op==='='&&eq(c.x.b,n(0))&&c.x.a.op==='get')return c.x.a
 if(c.op==='not'&&c.x.op==='='&&eq(c.x.a,n(0))&&c.x.b.op==='get')return c.x.b
 return undefined
}
function replaceCell(c:C,old:Cell,value:E):C{return substC(c,{vars:{},maps:{[old.map]:key=>eq(key,old.key)?value:{op:'get',map:old.map,key}},flags:{}})}
function boundKnown(e:E,b:E,pre:C[]):boolean{
 if(pre.some(c=>c.op==='<'&&eq(c.a,e)&&eq(c.b,b)))return true
 if(e.op!=='const'||e.value<0)return false
 if(b.op==='const')return e.value<b.value
 return pre.some(c=>(c.op==='<'||c.op==='<=')&&c.a.op==='const'&&eq(c.b,b)&&e.value<(c.op==='<'?c.a.value+1:c.a.value))
}
function foldE(e:E,fs:Facts,tick:()=>boolean,depth=0):E|undefined{
 if(!tick()||depth>48)return
 for(const {c,value}of fs.values())if(value&&c.op==='='){
  if(eq(c.a,e)&&c.b.op==='const')return c.b
  if(eq(c.b,e)&&c.a.op==='const')return c.a
 }
 if(e.op==='if'){
  const c=foldC(e.c,fs,tick,depth+1);if(!c)return
  if(eq(c,yes))return foldE(e.then,fs,tick,depth+1)
  if(eq(c,no))return foldE(e.else,fs,tick,depth+1)
  const a=foldE(e.then,fs,tick,depth+1),b=foldE(e.else,fs,tick,depth+1);if(!a||!b)return
  return eq(a,b)?a:{op:'if',c,then:a,else:b}
 }
 if(e.op==='get'){const key=foldE(e.key,fs,tick,depth+1);return key?{...e,key}:undefined}
 if(e.op==='add'||e.op==='sub'||e.op==='min'||e.op==='max'||e.op==='prod'){
  const a=foldE(e.a,fs,tick,depth+1),b=foldE(e.b,fs,tick,depth+1);if(!a||!b)return
  if(a.op==='const'&&b.op==='const')return n(e.op==='add'?a.value+b.value:e.op==='sub'?Math.max(0,a.value-b.value):e.op==='min'?Math.min(a.value,b.value):e.op==='max'?Math.max(a.value,b.value):a.value*b.value)
  return {...e,a,b}
 }
 if(e.op==='mul'){const a=foldE(e.a,fs,tick,depth+1);return a?(a.op==='const'?n(e.k*a.value):{...e,a}):undefined}
 return e
}
function foldC(c:C,fs:Facts,tick:()=>boolean,depth=0):C|undefined{
 if(!tick()||depth>48)return
 const f=fs.get(json(c));if(f)return f.value?yes:no
 if(c.op==='not'){const q=foldC(c.x,fs,tick,depth+1);return q?(eq(q,yes)?no:eq(q,no)?yes:q.op==='not'?q.x:not(q)):undefined}
 if(c.op==='and'||c.op==='or'){
  const unit=c.op==='and'?yes:no,zero=c.op==='and'?no:yes,qs:C[]=[]
  for(const x of flat(c,c.op)){const q=foldC(x,fs,tick,depth+1);if(!q)return;if(eq(q,zero))return zero;if(!eq(q,unit))qs.push(q)}
  if(qs.some(q=>qs.some(r=>eq(q,not(r))||eq(r,not(q)))))return zero
  const unique=[...new Map(qs.map(q=>[json(q),q])).values()];return !unique.length?unit:unique.length===1?unique[0]:{op:c.op,xs:unique}
 }
 if(c.op==='='||c.op==='<'||c.op==='<='){
  const a=foldE(c.a,fs,tick,depth+1),b=foldE(c.b,fs,tick,depth+1);if(!a||!b)return
  if(eq(a,b))return c.op==='<'?no:yes
  if(a.op==='const'&&b.op==='const')return(c.op==='='?a.value===b.value:c.op==='<'?a.value<b.value:a.value<=b.value)?yes:no
  return {...c,a,b}
 }
 return c
}

export function scanPrefixes(m: Machine, occupied: readonly Law[] = []): Law[] {
  const flags = m.step.flags ?? {}, packets: Law[][] = []
  let work = 0
  const more = () => ++work <= 8192 && packets.length < 64
  const eq = (a: unknown, b: unknown) => JSON.stringify(a) === JSON.stringify(b)
  const sub = (c: C, from: string, to: E) => substC(c, {vars: {[from]: to}, maps: {}, flags: {}})
  const parts = (c: C): C[] => c.op === 'and' ? c.xs.flatMap(parts) : [c]
  const closure = (c: C, seen = new Set<string>()): C[] => {
    const rs = [c]
    walk(c, o => {
      if (o.op === 'flag' && typeof o.name === 'string' && !seen.has(o.name)) {
        seen.add(o.name)
        const f = flags[o.name]
        if (f && f.op !== 'all') rs.push(...closure(f, seen))
      }
    })
    return rs
  }
  // Stable structural discriminator; collisions are detected below, not trusted away.
  const tag = (s: string) => {
    let h = 14695981039346656037n
    for (let i = 0; i < s.length; i++) h = BigInt.asUintN(64, (h ^ BigInt(s.charCodeAt(i))) * 1099511628211n)
    return h.toString(16)
  }
  scan: for (const [counter, w] of Object.entries(m.step.state ?? {})) {
    if (!more()) break
    if (w.op !== 'if' || !eq(w.then, {op: 'add', a: x(counter), b: n(1)}) || w.else.op !== 'if' || !eq(w.else.then, n(0)) || !eq(w.else.else, x(counter))) continue
    const related = closure(w.c), atoms = related.flatMap(parts)
    const activities = atoms.filter((c): c is C & {op: '='} => c.op === '=' && c.a.op === 'var' && c.a.name !== counter && c.a.name in m.state && eq(m.state[c.a.name], n(0)) && eq(c.b, n(1)))
    for (const c of related) for (const node of parts(c)) {
      if (node.op !== 'not' || node.x.op !== 'flag') continue
      const rowName = node.x.name, row = flags[rowName]
      if (row?.op !== 'all' || row.keys?.length) continue
      const members = parts(c).filter(q => q.op === '=' && q.a.op === 'get' && eq(q.a.key, x(counter)) && q.a.map in (m.maps ?? {}) && eq(q.b, n(1)))
      for (const member of members) for (const activity of activities) {
        if (!more()) break scan
        const taken = new Set([...m.params, ...m.inputs, ...Object.keys(m.state), ...Object.keys(m.maps ?? {}), ...Object.keys(flags)])
        walk([m], o => { if (typeof o.name === 'string') taken.add(o.name); if (typeof o.key === 'string') taken.add(o.key) })
        let fresh = 'scanKey'
        while (taken.has(fresh) || fresh === row.key) fresh += 'X'
        const base = `scan-prefix:${counter}:${rowName}:${tag(JSON.stringify({member, activity, row}))}`
        packets.push([
          {name: base + ':entry', holds: any(not(same(activity.a, n(0))), same(x(counter), n(0)))},
          {name: base, forall: fresh, keys: [row.key], holds: any(not(all(activity, less(x(fresh), x(counter)), sub(member, counter, x(fresh)))), sub(row.c, counter, x(fresh)))},
        ])
      }
    }
  }
  const blocked = new Set(occupied.map(l => l.name)), byName = new Map<string, string>()
  for (const packet of packets) for (const l of packet) {
    const signature = JSON.stringify(l), previous = byName.get(l.name)
    if (previous !== undefined && previous !== signature) blocked.add(l.name)
    byName.set(l.name, signature)
  }
  const unique = new Map<string, Law>()
  for (const packet of packets) {
    // Skip the whole family if either name conflicts, including with a caller.
    if (packet.some(l => blocked.has(l.name))) continue
    for (const l of packet) unique.set(l.name, l)
  }
  return [...unique.values()]
}
