import PaxosEprTreesRepair
import PaxosEprTreesLinear10Patches
namespace Bapa.PaxosEprTreesLinear10
open Kern Cert
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def replaceAt : List Bool → Tree → Tree → Tree
 | [], replacement, _ => replacement
 | b::bs, replacement, .split r y n =>
   if b then .split r (replaceAt bs replacement y) n else .split r y (replaceAt bs replacement n)
 | _, _, old => old

def patched (i : Nat) (t : Tree) : Tree :=
 (PaxosEprTreesLinear10Patches.patches i).foldl (fun old (path,new) => replaceAt path new old) t

def repair (i : Nat) (goal : List C) (ds : List CDecl) (k : CCert) : Except String CCert :=
 (PaxosEprTreesRepair.repair i goal ds k).map (fun base => {base with tree := patched i base.tree})

theorem non_tree_fields_preserved (i : Nat) (goal : List C) (ds : List CDecl)
 (k k' : CCert) (h : repair i goal ds k = .ok k') :
 k'.hyps = k.hyps ∧ k'.reads = k.reads ∧ k'.insts = k.insts ∧
 k'.tab = k.tab ∧ k'.picks = k.picks ∧ k'.lemmas = k.lemmas := by
 cases hb : PaxosEprTreesRepair.repair i goal ds k with
 | error e => simp [repair, hb, Except.map] at h
 | ok base =>
   simp [repair, hb, Except.map] at h
   subst k'
   exact PaxosEprTreesRepair.non_tree_fields_preserved i goal ds k base hb
#print axioms non_tree_fields_preserved
end Bapa.PaxosEprTreesLinear10
