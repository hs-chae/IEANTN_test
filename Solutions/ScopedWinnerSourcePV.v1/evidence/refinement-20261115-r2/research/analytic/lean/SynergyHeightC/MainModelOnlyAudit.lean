/- Read-only declaration dependency census for the kernel-only comparator.
This does not establish a source-first execution claim. -/
import SynergyHeightC.MainModelOnlyProfile
import Lean.Util.CollectAxioms
open Lean Elab
namespace SynergyHeightC.MainModelOnlyAudit
set_option autoImplicit false
set_option maxHeartbeats 0

partial def visit (env : Environment) (name : Name) (seen : NameSet)
    (missing : Array Name) : NameSet × Array Name := Id.run do
  if seen.contains name then return (seen,missing)
  let mut seen := seen.insert name
  let mut missing := missing
  let some info := env.checked.get.find? name
    | return (seen,missing.push name)
  let mut dependencies := info.type.getUsedConstants
  if let some body := info.value? true then
    dependencies := dependencies ++ body.getUsedConstants
  if let .inductInfo inductiveInfo := info then
    dependencies := dependencies ++ inductiveInfo.ctors.toArray
  for dependency in dependencies do
    let result := visit env dependency seen missing
    seen := result.1
    missing := result.2
  return (seen,missing)

run_elab do
  let roots := #[`SynergyHeightC.MainModelOnlyProfile.model_finite_sum_330,
    `SynergyHeightC.MainModelOnlyProfile.model_rational_ray,
    `SynergyHeightC.MainModelOnlyProfile.model_rational_point]
  let env ← getEnv
  for root in roots do
    let (seen,missing) := visit env root {} #[]
    let names := seen.toArray
    let forbidden := names.filter fun name=>
      let s := name.toString
      s=="ScopedC.ArraySourceCalls.SourceCall" || s=="ScopedC.SourceCalls.SourceCall" ||
      s=="ScopedIO.WorldSource.SourceCall" || s.startsWith "SourceMainBudgetV1." ||
      s=="SynergyHeightC.FullContractPointExecute.run"
    unless missing.isEmpty do throwError "unavailable dependency declarations: {missing}"
    unless forbidden.isEmpty do throwError "C source execution unexpectedly consumed: {forbidden}"
    let ax ← Lean.collectAxioms root
    logInfo m!"MODEL_ONLY_DEPENDENCIES {(Json.mkObj [
      ("root",toJson root.toString),("declarations",toJson names.size),
      ("missing",toJson missing.size),("forbidden_source_execution",toJson forbidden.size),
      ("axioms",toJson (ax.toList.map Name.toString)),
      ("scope",toJson "Exact transitive type/body/inductive-constructor closure; no generic source-facing heuristic")]).compress}"
end SynergyHeightC.MainModelOnlyAudit
#print axioms SynergyHeightC.MainModelOnlyProfile.model_finite_sum_330
#print axioms SynergyHeightC.MainModelOnlyProfile.model_rational_ray
#print axioms SynergyHeightC.MainModelOnlyProfile.model_rational_point
