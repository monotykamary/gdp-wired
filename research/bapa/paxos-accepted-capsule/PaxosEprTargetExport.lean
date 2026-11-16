import PaxosEprAdapterAudit
namespace Bapa.PaxosEprTargetExport
open Kern
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def seq (xs : List α) (f : α → String) : String :=
  "[" ++ String.intercalate ", " (xs.map f) ++ "]"
private def pair (a b : String) : String := "(" ++ a ++ ", " ++ b ++ ")"
mutual
private def expr : E → String
  | .var i => s!"(.var {i})"
  | .const n => s!"(.const {n})"
  | .add a b => "(.add " ++ expr a ++ " " ++ expr b ++ ")"
  | .sub a b => "(.sub " ++ expr a ++ " " ++ expr b ++ ")"
  | .mul k a => s!"(.mul {k} " ++ expr a ++ ")"
  | .min a b => "(.min " ++ expr a ++ " " ++ expr b ++ ")"
  | .max a b => "(.max " ++ expr a ++ " " ++ expr b ++ ")"
  | .prod a b => "(.prod " ++ expr a ++ " " ++ expr b ++ ")"
  | .ite c a b => "(.ite " ++ cond c ++ " " ++ expr a ++ " " ++ expr b ++ ")"
  | .get m k => s!"(.get {m} " ++ expr k ++ ")"
  | .tup a b => "(.tup " ++ expr a ++ " " ++ expr b ++ ")"
  | .proj n a => s!"(.proj {n} " ++ expr a ++ ")"
private def cond : C → String
  | .le a b => "(.le " ++ expr a ++ " " ++ expr b ++ ")"
  | .lt a b => "(.lt " ++ expr a ++ " " ++ expr b ++ ")"
  | .eq a b => "(.eq " ++ expr a ++ " " ++ expr b ++ ")"
  | .and a b => "(.and " ++ cond a ++ " " ++ cond b ++ ")"
  | .or a b => "(.or " ++ cond a ++ " " ++ cond b ++ ")"
  | .not a => "(.not " ++ cond a ++ ")"
end
private def emitMachine (s : SMachine) : String :=
  let m := s.f.m
  "{ f := {m := {inputs := " ++ seq m.inputs toString ++
  ", init := " ++ seq m.init (fun p => pair (toString p.1) (expr p.2)) ++
  ", maps0 := " ++ seq m.maps0 (fun p => pair (toString p.1) (toString p.2)) ++
  ", step := " ++ seq m.step (fun p => pair (toString p.1) (expr p.2)) ++
  ", writes := " ++ seq m.writes (fun p => pair (toString p.1) (pair (expr p.2.1) (expr p.2.2))) ++
  ", pre := " ++ cond m.pre ++ ", assume := " ++ cond m.assume ++ "}, flags := " ++
  seq s.f.flags (fun p => pair (toString p.1) (cond p.2)) ++ "}, carried := " ++
  seq s.carried toString ++ ", every := " ++ seq s.every (fun p => pair (toString p.1) (pair (toString p.2.1) (expr p.2.2))) ++
  ", qflags := " ++ seq s.qflags (fun p => pair (toString p.1) (pair (seq p.2.1 toString) (cond p.2.2))) ++
  ", wits := " ++ seq s.wits (fun p => pair (toString p.1) (seq p.2 toString)) ++ ", facts := [], pfacts := []}"
private def decl (d : CDecl) : String :=
  s!"⟨{d.mp}, {d.post}, {d.j}, {d.key}, " ++ expr d.below ++ ", " ++ expr d.body ++ s!", {d.lo}, {d.base}⟩"
#eval (show IO Unit from do
  let out := (← IO.getEnv "SUPERCOMPUTER_OUTPUT_DIR").getD "."
  let s ← match PaxosEprAdapterAudit.targetMachine with
    | .ok s => pure s
    | .error _ => throw (IO.userError "target machine refused")
  let ds ← match PaxosEprAdapterAudit.targetDecls with
    | .ok ds => pure ds
    | .error _ => throw (IO.userError "target declarations refused")
  unless s.facts.isEmpty && s.pfacts.isEmpty do throw (IO.userError "nonempty facts require explicit serialization")
  IO.FS.writeFile (out ++ "/PaxosEprTargetDefs.lean")
    ("import CountMachine\nnamespace Bapa.PaxosEprTarget\nopen Kern\ndef machine : SMachine :=\n" ++ emitMachine s ++
    "\ndef declarations : List CDecl :=\n" ++ seq ds decl ++ "\nend Bapa.PaxosEprTarget\n"))
end Bapa.PaxosEprTargetExport
