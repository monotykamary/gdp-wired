import Lean
/-!
What retiring the usual certificate's Lean path would delete: the twin's library (lean-kernel/*.lean) against the
declarations an export needs. `lean --run Retire.lean <proofs.lean>...` (LEAN_PATH with the library's .olean files):
every name a given export reads (its text's identifiers, in `Kern` and `Cert` as it opens them) is a root, and so is
every declaration it reaches through types and proofs; what no root reaches is printed per file, as declarations
(definitions, theorems, inductives as written: not their constructors, recursors or projections) and the lines they
span.
-/
open Lean

def modules : List Name := [`Cert, `Kernel, `Cyclic, `Progress, `StepLaw, `Steps, `Sets, `History, `Live, `Ghost, `Refine, `Bridge, `BridgeRules, `Data]

def idents (s : String) : List String := Id.run do
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\''
  let mut out : Array String := #[]
  let mut cur := ""
  for c in s.toList do
    if isId c then cur := cur.push c
    else if cur != "" then out := out.push cur; cur := ""
  if cur != "" then out := out.push cur
  return out.toList

partial def close (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then close env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => close env rest seen
    | some ci => close env (ci.getUsedConstantsAsSet.toList ++ rest) seen

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (modules.map fun m => { module := m }).toArray {} 0
  let ours (n : Name) : Option Name := (env.getModuleIdxFor? n).bind fun i =>
    let m := env.header.moduleNames[i.toNat]!
    if modules.contains m then some m else none
  let mut roots : List Name := []
  for f in args do
    let text ← IO.FS.readFile f
    for t in idents text do
      for n in [t.toName, `Kern ++ t.toName, `Cert ++ t.toName] do
        if (ours n).isSome then roots := n :: roots
  let reached := close env roots {}
  -- per file: (declarations, lines) in all, and those no root reaches
  let mut all : Std.HashMap Name (Nat × Nat) := {}
  let mut gone : Std.HashMap Name (Nat × Nat) := {}
  let mut names : Std.HashMap Name (Array Name) := {}
  for (n, ci) in env.constants.toList do
    let some m := ours n | continue
    -- (what was written: definitions, theorems, inductives; not their constructors, recursors or projections)
    let written := match ci with
      | .thmInfo _ | .inductInfo _ | .opaqueInfo _ => true
      | .defnInfo _ => !env.isProjectionFn n
      | _ => false
    unless written && !n.isInternal do continue
    let some r := declRangeExt.find? env n | continue
    let lines := r.range.endPos.line - r.range.pos.line + 1
    let (a, b) := all.getD m (0, 0)
    all := all.insert m (a + 1, b + lines)
    unless reached.contains n do
      let (c, d) := gone.getD m (0, 0)
      gone := gone.insert m (c + 1, d + lines)
      names := names.insert m ((names.getD m #[]).push n)
  IO.println s!"roots {roots.length} names, reached {reached.size} constants"
  let mut tot := (0, 0, 0, 0)
  for m in modules do
    let (a, b) := all.getD m (0, 0)
    let (c, d) := gone.getD m (0, 0)
    tot := (tot.1 + a, tot.2.1 + b, tot.2.2.1 + c, tot.2.2.2 + d)
    IO.println s!"{m}: {a} declarations, {b} lines; unreached {c} declarations, {d} lines"
  IO.println s!"all: {tot.1} declarations, {tot.2.1} lines; unreached {tot.2.2.1} declarations, {tot.2.2.2} lines"
  for m in modules do
    let ns := (names.getD m #[]).qsort (fun a b => a.toString < b.toString)
    if ns.size > 0 then IO.println s!"unreached in {m}: {ns.toList.map (·.toString) |>.take 400}"
