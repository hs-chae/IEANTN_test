/- Construct the actual checked main emitter trace in one concrete I/O model.
The numerical words come from the actual same-source point outputs, with all
UInt512 guards proved. This is not a statement that all real host writes succeed. -/
import SynergyHeightC.CompleteIOModel
import SynergyHeightC.MainOutputRanges
import SourceMainWeightsV1.All
namespace SynergyHeightC.MainIOTrace
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO
open SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

@[irreducible] noncomputable def cWord (i : Nat) : Int := (adjustedC (modelPair i).1).hi
@[irreducible] noncomputable def dWord (i : Nat) : Int := (modelPair i).2.hi

theorem cWord_function_exact : cWord=(fun i=>(adjustedC (modelPair i).1).hi) := by
  unfold cWord
  rfl

theorem dWord_function_exact : dWord=(fun i=>(modelPair i).2.hi) := by
  unfold dWord
  rfl

theorem source_input_function_exact : MainInputPointComposition.input=
    (fun i=>gridInput (i+1)) :=
  (congrArg (fun get : Nat → ProofBox=>fun i=>get (i+1)) gridInput_function_exact).symm

theorem words_of_outputs {i : Nat} (hi : i < 768) {c d : ProofBox}
    (outputs : PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d)) :
    (adjustedC c).hi=cWord i ∧ d.hi=dWord i := by
  obtain ⟨left,right,model,domain⟩ := domain_spec (i:=i) (SourceMainWeightsV1.All.all_domains i hi)
  have sameInput := congrFun source_input_function_exact i
  have actual : PointExecuteAPI.modelOutputs (gridInput (i+1))=some (c,d) :=
    (congrArg PointExecuteAPI.modelOutputs sameInput).symm.trans outputs
  have pair : (c,d)=modelPair i := Option.some.inj (actual.symm.trans model)
  have cHigh := congrArg (fun pair : ProofBox × ProofBox=>(adjustedC pair.1).hi) pair
  have dHigh := congrArg (fun pair : ProofBox × ProofBox=>pair.2.hi) pair
  exact ⟨cHigh.trans (congrFun cWord_function_exact i).symm,
    dHigh.trans (congrFun dWord_function_exact i).symm⟩

theorem word_ranges (i : Nat) (hi : i < 768) :
    SynergyC.Word512.Range (cWord i) ∧ SynergyC.Word512.Range (dWord i) := by
  have range := row_output_ranges (i:=i) hi (SourceMainWeightsV1.All.all_domains i hi)
  exact ⟨Eq.mpr (congrArg SynergyC.Word512.Range (congrFun cWord_function_exact i)) range.1,
    Eq.mpr (congrArg SynergyC.Word512.Range (congrFun dWord_function_exact i)) range.2⟩

noncomputable def streams (initial : Stream) : Nat → Stream
  | 0 => initial
  | i+1 => CompleteIOModel.appendWord
      (CompleteIOModel.appendWord (streams initial i) (cWord i)) (dWord i)

theorem budget_stdout (total : ProofBox) (i : Nat) (c d : ProofBox) :
    (MainBudgetExecute.afterBudget total i c d).globals.lookup "stdout"=none := by rfl

theorem checked_rows (platform : WorldIO.Platform) (initial : Stream) :
    MainWorldLoop.CheckedRowCalls platform CompleteIOModel.policy (streams initial) := by
  intro i hi
  obtain ⟨c,d,model,body⟩ := MainWorldAllIterations.actual_rows i hi
  have words := words_of_outputs (i:=i) (c:=c) (d:=d) hi model
  have ranges := word_ranges i hi
  have cRange : SynergyC.Word512.Range (adjustedC c).hi := by rw [words.1]; exact ranges.1
  have dRange : SynergyC.Word512.Range d.hi := by rw [words.2]; exact ranges.2
  let state := MainBudgetExecute.afterBudget (SourceMainBudgetV1.Data.total i) i c d
  let middle : WorldIO.World := ⟨state,CompleteIOModel.appendWord (streams initial i) (adjustedC c).hi⟩
  let after : WorldIO.World := ⟨state,CompleteIOModel.appendWord
    (CompleteIOModel.appendWord (streams initial i) (adjustedC c).hi) d.hi⟩
  refine ⟨c,d,middle,after,model,?_,?_,?_⟩
  · exact CompleteIOModel.emitU_success platform state (adjustedC c).hi cRange
      (streams initial i) (budget_stdout _ _ _ _)
  · exact CompleteIOModel.emitU_success platform state d.hi dRange
      (CompleteIOModel.appendWord (streams initial i) (adjustedC c).hi) (budget_stdout _ _ _ _)
  · change CompleteIOModel.appendWord
      (CompleteIOModel.appendWord (streams initial i) (adjustedC c).hi) d.hi=
        CompleteIOModel.appendWord
          (CompleteIOModel.appendWord (streams initial i) (cWord i)) (dWord i)
    rw [words.1,words.2]

#print axioms source_input_function_exact
#print axioms words_of_outputs
#print axioms word_ranges
#print axioms budget_stdout
#print axioms checked_rows
end SynergyHeightC.MainIOTrace
