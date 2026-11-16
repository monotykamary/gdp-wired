import PaxosEprTreeRepairChecks
open Kern Bapa.PaxosEprTreeRepairChecks
#eval targetEntries.toOption.map (fun es => es.zipIdx.map (fun (e,i) =>
 s!"LAW{i}: key={reprStr e.law.key}, further={reprStr e.keys2}, holds={(jc e.law.holds).compress}"))
