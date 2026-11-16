import PaxosEprLiteralGlobal
import PaxosEprLiteralEntry0
import PaxosEprLiteralEntry1
import PaxosEprLiteralEntry2
import PaxosEprLiteralEntry3
import PaxosEprLiteralEntry4
import PaxosEprLiteralEntry5
import PaxosEprLiteralEntry6
import PaxosEprLiteralEntry7
import PaxosEprLiteralEntry8
import PaxosEprLiteralEntry9
import PaxosEprLiteralEntry10
import PaxosEprLiteralEntry11
import PaxosEprLiteralEntry12
import PaxosEprLiteralEntry13
import PaxosEprLiteralEntry14
import PaxosEprLiteralEntry15
import PaxosEprLiteralEntry16
import PaxosEprLiteralEntry17
import PaxosEprLiteralEntry18
import PaxosEprLiteralEntry19
import PaxosEprLiteralEntry20
import PaxosEprLiteralEntry21
import PaxosEprLiteralEntry22
import PaxosEprLiteralEntry23
import PaxosEprLiteralEntry24
namespace Bapa.PaxosEprLiteral
open Kern Bapa.PaxosEprCountedGate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem entries_checked : family.all (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family) = true := by
 change (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry0 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry1 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry2 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry3 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry4 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry5 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry6 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry7 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry8 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry9 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry10 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry11 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry12 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry13 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry14 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry15 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry16 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry17 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry18 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry19 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry20 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry21 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry22 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry23 && (entryGate PaxosEprTarget.machine PaxosEprTarget.declarations family entry24 && true))))))))))))))))))))))))) = true
 rw [entry0_checked,entry1_checked,entry2_checked,entry3_checked,entry4_checked,entry5_checked,entry6_checked,entry7_checked,entry8_checked,entry9_checked,entry10_checked,entry11_checked,entry12_checked,entry13_checked,entry14_checked,entry15_checked,entry16_checked,entry17_checked,entry18_checked,entry19_checked,entry20_checked,entry21_checked,entry22_checked,entry23_checked,entry24_checked]
 rfl
theorem family_checked : checkCMachine PaxosEprTarget.machine PaxosEprTarget.declarations family = true := combine _ _ _ global_checked entries_checked
theorem original_source_safety : ∀ ρ M, CReach PaxosEprAtomicSource.machine PaxosEprAtomicSource.declarations ρ M → PaxosEprAtomicSource.safety.Holds ρ (withCnt PaxosEprAtomicSource.declarations ρ M) := PaxosEprSafetyGate.source_from_checked_family family family_checked entries_exact
#print axioms family_checked
#print axioms original_source_safety
end Bapa.PaxosEprLiteral
