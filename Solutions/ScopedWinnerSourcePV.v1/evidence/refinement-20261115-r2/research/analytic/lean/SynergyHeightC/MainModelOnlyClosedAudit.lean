/- Exact final closed-root audit. A module import can contain unused C proofs;
this declaration census makes no independent fresh-build or runtime-cost claim. -/
import SynergyHeightC.MainRationalClosed
import SynergyHeightC.MainModelOnlyAudit
open Lean Elab
namespace SynergyHeightC.MainModelOnlyClosedAudit
set_option autoImplicit false
set_option maxHeartbeats 0
run_elab do
  let root := `SynergyHeightC.MainRationalClosed.kernel_only_profile_point
  let (seen,missing) := MainModelOnlyAudit.visit (←getEnv) root {} #[]
  let names := seen.toArray
  let forbidden := names.filter fun name=>
    let s := name.toString
    s=="ScopedC.ArraySourceCalls.SourceCall" || s=="ScopedC.SourceCalls.SourceCall" ||
    s=="ScopedIO.WorldSource.SourceCall" || s.startsWith "SourceMainBudgetV1." ||
    s=="SynergyHeightC.FullContractPointExecute.run" || s.startsWith "SynergyHeightC.MainObserved"
  unless missing.isEmpty do throwError "unavailable dependency declarations: {missing}"
  unless forbidden.isEmpty do throwError "source execution or observed output consumed: {forbidden}"
  let ax ← Lean.collectAxioms root
  logInfo m!"CLOSED_MODEL_ONLY_DEPENDENCIES {(Json.mkObj [
    ("root",toJson root.toString),("declarations",toJson names.size),
    ("missing",toJson missing.size),("forbidden_source_execution",toJson forbidden.size),
    ("axioms",toJson (ax.toList.map Name.toString)),
    ("scope",toJson "Exact transitive declaration type/body/inductive-constructor closure. Module-import closure contains unrelated C proofs; no fresh independent N+ build is claimed.")]).compress}"
end SynergyHeightC.MainModelOnlyClosedAudit
#print axioms SynergyHeightC.MainRationalClosed.kernel_only_profile_point
