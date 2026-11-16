/- Abstract only the three functions in the existing exact cell expression.
No arithmetic, source algorithm or numerical proposition is replaced. -/
import SynergyHeightC.MainWeightAbstract
open Lean Meta Elab
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
run_elab do
  if Lean.debug.skipKernelTC.get (← getOptions) then
    throwError "mandatory kernel type checking is disabled"
  let env ← getEnv
  let some (.defnInfo source) := env.find? ``cell
    | throwError "expected actual source cell"
  let names := #[``SynergyAnalytic.HeightPoint.logCell,``PointExecuteAPI.modelOutputs,``term]
  let types ← names.mapM (fun n=>inferType (mkConst n))
  withLocalDeclD `grid types[0]! fun grid =>
    withLocalDeclD `evaluate types[1]! fun evaluate =>
      withLocalDeclD `calculate types[2]! fun calculate => do
        let params := #[grid,evaluate,calculate]
        let body := source.value.replace fun e=>
          match e with
          | .const n _ =>
              match names.findIdx? (fun name=>name==n) with
              | some i=>some params[i]!
              | none=>none
          | _=>none
        let value ← mkLambdaFVars params body
        let type ← inferType value
        addDecl (.defnDecl {
          name := Name.str source.name.getPrefix "abstractCell"
          levelParams := []
          type := type
          value := value
          hints := .abbrev
          safety := .safe
        })

theorem actual_cell_function_exact : cell=
    abstractCell SynergyAnalytic.HeightPoint.logCell PointExecuteAPI.modelOutputs term := by rfl

theorem abstract_cell_from_data
    (grid : Nat→Option ProofBox) (evaluate : ProofBox→Option (ProofBox×ProofBox))
    (calculate : ProofBox→ProofBox→ProofBox→ProofBox→ProofBox)
    {i : Nat} {left right c d : ProofBox}
    (hl : grid i=some left) (hr : grid (i+1)=some right)
    (hm : evaluate right=some (c,d)) :
    abstractCell grid evaluate calculate i=some (calculate left right c d) := by
  unfold abstractCell
  simp only [hl,hr,hm,Bind.bind,Option.bind,Pure.pure]

theorem cell_from_data {i : Nat} {left right c d : ProofBox}
    (hl : SynergyAnalytic.HeightPoint.logCell i=some left)
    (hr : SynergyAnalytic.HeightPoint.logCell (i+1)=some right)
    (hm : PointExecuteAPI.modelOutputs right=some (c,d)) :
    cell i=some (term left right c d) :=
  (congrFun actual_cell_function_exact i).trans
    (abstract_cell_from_data SynergyAnalytic.HeightPoint.logCell
      PointExecuteAPI.modelOutputs term hl hr hm)

theorem cell_from_pair_data {i : Nat} {left right : ProofBox} {pair : ProofBox×ProofBox}
    (hl : SynergyAnalytic.HeightPoint.logCell i=some left)
    (hr : SynergyAnalytic.HeightPoint.logCell (i+1)=some right)
    (hm : PointExecuteAPI.modelOutputs right=some pair) :
    cell i=some (term left right pair.1 pair.2) := by
  rcases pair with ⟨c,d⟩
  exact cell_from_data hl hr hm

#print axioms actual_cell_function_exact
#print axioms cell_from_data
#print axioms cell_from_pair_data
end SynergyHeightC.MainWeightModel
