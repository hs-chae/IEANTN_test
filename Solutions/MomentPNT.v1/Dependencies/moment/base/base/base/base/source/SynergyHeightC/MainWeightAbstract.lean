/- Abstract the four functions in the EXISTING checked domain expression.
This preserves its matcher and decision-instance expressions exactly. The new
definition and all proofs undergo mandatory ordinary kernel checking. -/
import SynergyHeightC.MainWeightModel
import Lean
open Lean Meta Elab
namespace SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 200000

run_elab do
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "mandatory kernel type checking is disabled"
  let env ← getEnv
  let some (.defnInfo source) := env.find? ``cellDomain
    | throwError "expected actual checked domain definition"
  let names := #[``SynergyAnalytic.HeightPoint.logCell,``PointExecuteAPI.modelOutputs,
    ``term,``adjustedC]
  let types ← names.mapM (fun n=>inferType (mkConst n))
  withLocalDeclD `grid types[0]! fun grid =>
    withLocalDeclD `evaluate types[1]! fun evaluate =>
      withLocalDeclD `calculate types[2]! fun calculate =>
        withLocalDeclD `adjust types[3]! fun adjust => do
          let params := #[grid,evaluate,calculate,adjust]
          let body := source.value.replace fun e=>
            match e with
            | .const n _ =>
                match names.findIdx? (fun name=>name==n) with
                | some i=>some params[i]!
                | none=>none
            | _=>none
          let value ← mkLambdaFVars params body
          let type ← inferType value
          let targetName := Name.str source.name.getPrefix "abstractDomain"
          addDecl (.defnDecl {
            name := targetName
            levelParams := []
            type := type
            value := value
            hints := .abbrev
            safety := .safe
          })



/-- Compare the functions before applying the expensive numerical argument.
The lambda bodies are the exact same source expression after abstraction. -/
theorem actual_domain_function_exact : cellDomain=
    abstractDomain SynergyAnalytic.HeightPoint.logCell PointExecuteAPI.modelOutputs
      term adjustedC := by rfl

theorem actual_domain_exact (i : Nat) : cellDomain i=
    abstractDomain SynergyAnalytic.HeightPoint.logCell PointExecuteAPI.modelOutputs
      term adjustedC i := congrFun actual_domain_function_exact i

#print axioms actual_domain_function_exact
#print axioms actual_domain_exact
end SynergyHeightC.MainWeightModel
