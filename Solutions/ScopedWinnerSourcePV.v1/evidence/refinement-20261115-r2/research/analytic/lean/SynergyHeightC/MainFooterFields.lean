/- The actual main's emitted upper words come from its own post-budget memory. -/
import SynergyHeightC.MainFooterState
import SynergyHeightC.EmitUReturnFacts
namespace SynergyHeightC.MainFooterFields
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem c_lookup (total : ProofBox) (i : Nat) (c d : ProofBox) :
    getVar (MainBudgetExecute.afterBudget total i c d) "c"=some ⟨21,0,[]⟩ := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,MainFooterState.span_length,List.lookup]

theorem d_lookup (total : ProofBox) (i : Nat) (c d : ProofBox) :
    getVar (MainBudgetExecute.afterBudget total i c d) "D"=some ⟨22,0,[]⟩ := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,MainFooterState.span_length,List.lookup]

theorem c_heap (total : ProofBox) (i : Nat) (c d : ProofBox) :
    (MainBudgetExecute.afterBudget total i c d).heap[21]?=some
      ({type:="I",cells:=[some (SynergyC.SourceIntervalMath.represented
        (MainWeightModel.adjustedC c))]} : Object) := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,MainFooterState.span_length]

theorem d_heap (total : ProofBox) (i : Nat) (c d : ProofBox) :
    (MainBudgetExecute.afterBudget total i c d).heap[22]?=some
      ({type:="I",cells:=[some (SynergyC.SourceIntervalMath.represented d)]} : Object) := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,MainFooterState.span_length]

theorem eval_c (pure : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 1 (MainBudgetExecute.afterBudget total i c d) (.var "c")=
      some (SynergyC.SourceIntervalMath.represented (MainWeightModel.adjustedC c),
        MainBudgetExecute.afterBudget total i c d) := by
  rw [evalExpr]
  simp [c_lookup,c_heap,Machine.read,Machine.nested,Machine.initialized,
    SynergyC.SourceIntervalMath.represented,SynergyC.ZeroBody.interval,SynergyC.Word512.value]

theorem eval_d (pure : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 1 (MainBudgetExecute.afterBudget total i c d) (.var "D")=
      some (SynergyC.SourceIntervalMath.represented d,MainBudgetExecute.afterBudget total i c d) := by
  rw [evalExpr]
  simp [d_lookup,d_heap,Machine.read,Machine.nested,Machine.initialized,
    SynergyC.SourceIntervalMath.represented,SynergyC.ZeroBody.interval,SynergyC.Word512.value]

theorem eval_c_hi (pure : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (MainBudgetExecute.afterBudget total i c d)
      (.field "." (.var "c") "hi")=some
      (SynergyC.Word512.value (MainWeightModel.adjustedC c).hi,
        MainBudgetExecute.afterBudget total i c d) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (eval_c pure total i c d) rfl

theorem eval_d_hi (pure : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (MainBudgetExecute.afterBudget total i c d)
      (.field "." (.var "D") "hi")=some
      (SynergyC.Word512.value d.hi,MainBudgetExecute.afterBudget total i c d) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (eval_d pure total i c d) rfl

theorem world_d_hi (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (world : ScopedIO.WorldIO.World)
    (total : ProofBox) (i : Nat) (c d : ProofBox)
    (same : world.app=MainBudgetExecute.afterBudget total i c d) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform
      (.field "." (.var "D") "hi") world world (SynergyC.Word512.value d.hi) := by
  cases world with
  | mk app stream =>
      change app=MainBudgetExecute.afterBudget total i c d at same
      subst app
      exact .pure (eval_d_hi pure total i c d)

theorem world_increment (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (world : ScopedIO.WorldIO.World)
    (total : ProofBox) (i : Nat) (c d : ProofBox) (bound : i+1<2^32)
    (same : world.app=MainBudgetExecute.afterBudget total i c d) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform
      (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1))) world
      ⟨MainFooterState.afterIncrement total i c d,world.stream⟩
      (FullMainPrefix.unsigned32 (i+1)) := by
  cases world with
  | mk app stream =>
      change app=MainBudgetExecute.afterBudget total i c d at same
      subst app
      exact .pure (MainFooterState.actual_increment pure total i c d bound)

#print axioms eval_c_hi
#print axioms eval_d_hi
#print axioms world_increment
end SynergyHeightC.MainFooterFields
