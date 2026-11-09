import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs'
import {spawnSync} from 'node:child_process'
import {createHash} from 'node:crypto'
import {checkCountedLaws,checkMC,countedObligations,mcGoal} from '../../kernel/kernel.ts'
import {encode} from '../../lean-kernel/emit.ts'
const log=readFileSync('evidence/capture-paxos_epr.log','utf8');const b64=log.match(/ARCHIVE_BEGIN\n([A-Za-z0-9+/=\r\n]+)\nARCHIVE_END/)![1]!
mkdirSync('/tmp/paxos-diagnostic',{recursive:true});writeFileSync('/tmp/paxos-diagnostic/archive.tar.xz',Buffer.from(b64,'base64'))
const t=spawnSync('tar',['-xJf','/tmp/paxos-diagnostic/archive.tar.xz','-C','/tmp/paxos-diagnostic']);if(t.status!==0)throw Error(String(t.stderr))
const dir='/tmp/paxos-diagnostic/'; const files=readdirSync(dir); console.log('FILES',files)
const packet=files.find(x=>x.endsWith('.json')&&!x.endsWith('.result.json'))!;const lf=files.find(x=>x.endsWith('.lean'))!
const raw=readFileSync(dir+packet,'utf8'),lean=readFileSync(dir+lf,'utf8');const sha=(x:string)=>createHash('sha256').update(x).digest('hex')
console.log('PACKET_SHA',sha(raw),'LEAN_SHA',sha(lean)); if(sha(raw)!=='dc0e230fab5d0081a2c9d4f56b525ef314a2e78780647d3cb2fafaf3a512f386'||sha(lean)!=='e31b4c24e46e021c0b0187d1c2b71736530c16e47db15c18eb4d8cd77cfc15b1')throw Error('hash mismatch')
const x=JSON.parse(raw,(_k,v)=>v?.__map?new Map(v.__map):v?.__set?new Set(v.__set):v);const c=x.counted;
console.log('TS_ACCEPTS',checkCountedLaws(c.machine,c.laws,c.proof));console.log('LAW_INDEX',JSON.stringify(c.laws.map((l:any,i:number)=>({i,name:l.name,forall:l.forall,keys:l.keys}))));
for(const {goal,decls} of countedObligations(c.machine,c.laws,c.proof.instances))console.log('TS_OBLIGATION',goal.name,checkMC(goal.hyps,decls,c.proof.certs[goal.name]));
const header=lean.split('theorem verified_check :')[0]!;
const diagnostic=`
-- Retained definitions only. No original failed theorem, no replacement proof.
def s := verified_machine
def ds := verified_decls
def ps := verified_proof.map (·.e)
#reduce ("global", [("sOk", sOk s), ("preAvoids", avoids (s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)) s.f.m.pre), ("preReads", !readsC s.f.m.pre), ("terms", sTermsOk s (flagVars s.f.flags)), ("facts", factsOk s), ("distinct", cDistinct (cMaps ds ++ cPosts ds)), ("apart", cApart s ds)])
#reduce ("decls", ds.zipIdx |>.map (fun (d,i) => (i,cDeclOk s ds ps d)))
#reduce ("entries", verified_proof.zipIdx |>.map (fun (ce,i) => (i, cEntryOk s ds ps ce.e, witsOk s ps ce.start, witsOk s ps ce.step, checkMC (cStartGoal s ds ce.e) (cStartDecls s ds) ce.start, checkMC (cStepGoal s ds ps ce.e) (cStepDecls s ds) ce.step)))
`;
const deep=`
def e12 := (verified_proof[12]).e
#reduce ("entry12", [("avoidsVars", avoids (s.extVars ++ flagVars s.f.flags) e12.law.holds), ("avoidsMaps", avoidsMaps (s.carried.filter (fun mp => !(stateMaps s ds).contains mp) ++ cPosts ds) e12.law.holds), ("skNotVars", !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains e12.sk), ("skNotLaws", ps.all (fun e => !occC e12.sk e.law.holds)), ("skNotPre", !occC e12.sk s.f.m.pre), ("skNotInit", s.f.m.init.all (fun p => !occE e12.sk p.2)), ("skFresh", skFresh s e12.sk), ("key2Ok", key2Ok s ps e12)])
#reduce ("entry12vars", s.extVars ++ flagVars s.f.flags, e12)
def ce20 := verified_proof[20]
def k20 := ce20.step
def ds20 := cStepDecls s ds
def h20 := cStepGoal s ds ps ce20.e
#reduce ("step20", [("namedIn", namedIn h20 k20.hyps h20), ("declkeys", ds20.all (fun d => d.j != d.key && d.lo != d.key)), ("readsOk", readsOk k20.hyps ds20 k20.reads), ("readWitness", k20.reads.all (fun r => k20.insts.all (fun i => i.wit != r.1 && !occE i.wit r.2.2))), ("toCounts", (toCounts ds20 k20.reads).isSome), ("counted", match toCounts ds20 k20.reads with | some cs => checkCountedW (k20.hyps ++ k20.reads.map (readHyp ds20) ++ pickHyps ds20 k20.reads k20.picks) cs k20.insts k20.tab k20.tree k20.lemmas | none => false)])
#reduce ("missingHyps20", k20.hyps.zipIdx |>.filter (fun (h,_) => !namedIn h20 [h] h20))
`;
const detail=`
#reduce ("key2_detail", e12.keys2.map (fun g => (g, e12.law.key != some g, skFresh s g, !(s.extVars ++ flagVars s.f.flags ++ s.f.m.init.map (·.1) ++ s.f.m.step.map (·.1)).contains g, !occC g s.f.m.pre, s.f.m.init.all (fun p => !occE g p.2), ps.zipIdx |>.filter (fun (e,_) => !((!occC g e.law.holds || e.keys2.contains g) && e.sk != g)) |>.map (fun (e,i) => (i,e.law.key,e.keys2,e.sk)))))
def cs20 := (toCounts ds20 k20.reads).getD []
def hs20 := k20.hyps ++ k20.reads.map (readHyp ds20) ++ pickHyps ds20 k20.reads k20.picks ++ (countHyps cs20 k20.insts).getD []
#reduce ("count_detail", countedOkW cs20 k20.insts, (countHyps cs20 k20.insts).isSome, wfTab 0 k20.tab, k20.lemmas.zipIdx |>.map (fun (l,i) => (i,checkLemma k20.tab hs20 l)), checkTLemmas k20.tab hs20 k20.lemmas [] k20.tree)
`;
console.log('LAW12',JSON.stringify(c.laws[12]));console.log('LAW20',JSON.stringify(c.laws[20]));console.log('NAME_MAP',lean.split('\n').find(l=>l.startsWith('--   (variables')));
const line=lean.split('\n').find(l=>l.startsWith('--   (variables'))!; const ns=line.match(/variables (.*); maps (.*)\)$/)!;
const names=(x:string)=>x.split(', ').map(s=>s.replace(/^\d+ /,'')); const vs=names(ns[1]!),ms=names(ns[2]!);
const ob=countedObligations(c.machine,c.laws,c.proof.instances).find(o=>o.goal.name===c.laws[20].name+' @step')!;
const cert=c.proof.certs[ob.goal.name];const goal=mcGoal(ob.goal.hyps,ob.decls,cert)!;const en=encode({name:'retained-step20',goal,tree:cert.tree},false,true,vs,ms);
const last=`
#reduce ("key29_sources", s.f.flags.filter (fun p => occC 29 p.2), s.qflags.filter (fun q => occC 29 q.2.2), s.every.filter (fun w => occE 29 w.2.2 || w.2.1 == 29))
def expected20 : List C := ${en.hyps}
def direct20 : Goal := ⟨${en.tab}, expected20⟩
def directTree20 : Tree := ${en.tree}
#reduce ("bridge20", hs20 == expected20, checkGoal direct20 directTree20)
#reduce ("differing_hyps20", (hs20.zip expected20).zipIdx |>.filter (fun (p,_) => p.1 != p.2))
`;
writeFileSync('/tmp/paxos-diagnostic.lean',header+diagnostic+deep+detail+last);console.log('DIAGNOSTIC_SHA',sha(header+diagnostic+deep+detail+last));
