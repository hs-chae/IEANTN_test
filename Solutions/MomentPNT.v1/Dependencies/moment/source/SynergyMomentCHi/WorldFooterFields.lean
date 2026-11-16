/- Actual high-only moment footer fields, with arbitrary next total and both
low words left initialized and opaque. No output or source execution premise. -/
import SynergyMomentCHi.WorldFooterState
import SynergyHeightC.EmitUReturnFacts
namespace SynergyMomentCHi.WorldFooterFields
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

theorem c_lookup (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    getVar (BudgetProposed.afterProposed total next i c d) "c"=some ⟨21,0,[]⟩ := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,WorldFooterState.span_length,List.lookup]

theorem d_lookup (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    getVar (BudgetProposed.afterProposed total next i c d) "D"=some ⟨22,0,[]⟩ := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,WorldFooterState.span_length,List.lookup]

theorem c_heap (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    (BudgetProposed.afterProposed total next i c d).heap[21]?=some
      ({type:="I",cells:=[some (SynergyC.SourceIntervalMath.represented
        (patched c))]} : Object) := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,WorldFooterState.span_length]

theorem d_heap (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    (BudgetProposed.afterProposed total next i c d).heap[22]?=some
      ({type:="I",cells:=[some (SynergyC.SourceIntervalMath.represented d)]} : Object) := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,WorldFooterState.span_length]

theorem eval_c (pure : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 1 (BudgetProposed.afterProposed total next i c d) (.var "c")=
      some (SynergyC.SourceIntervalMath.represented (patched c),
        BudgetProposed.afterProposed total next i c d) := by
  rw [evalExpr]
  simp [c_lookup,c_heap,Machine.read,Machine.nested,Machine.initialized,
    SynergyC.SourceIntervalMath.represented,SynergyC.ZeroBody.interval,SynergyC.Word512.value]

theorem eval_d (pure : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 1 (BudgetProposed.afterProposed total next i c d) (.var "D")=
      some (SynergyC.SourceIntervalMath.represented d,BudgetProposed.afterProposed total next i c d) := by
  rw [evalExpr]
  simp [d_lookup,d_heap,Machine.read,Machine.nested,Machine.initialized,
    SynergyC.SourceIntervalMath.represented,SynergyC.ZeroBody.interval,SynergyC.Word512.value]

theorem eval_c_hi (pure : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (BudgetProposed.afterProposed total next i c d)
      (.field "." (.var "c") "hi")=some
      (SynergyC.Word512.value (patched c).hi,
        BudgetProposed.afterProposed total next i c d) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (eval_c pure total next i c d) rfl

theorem eval_d_hi (pure : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    evalExpr SynergyC.Header.layout pure 2 (BudgetProposed.afterProposed total next i c d)
      (.field "." (.var "D") "hi")=some
      (SynergyC.Word512.value d.hi,BudgetProposed.afterProposed total next i c d) :=
  ExpressionTemplates.field SynergyC.Header.layout pure (eval_d pure total next i c d) rfl

theorem world_d_hi (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (world : ScopedIO.WorldIO.World)
    (total next : ProofBox) (i : Nat) (c d : ProofBox)
    (same : world.app=BudgetProposed.afterProposed total next i c d) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform
      (.field "." (.var "D") "hi") world world (SynergyC.Word512.value d.hi) := by
  cases world with
  | mk app stream =>
      change app=BudgetProposed.afterProposed total next i c d at same
      subst app
      exact .pure (eval_d_hi pure total next i c d)

theorem world_increment (pure : Machine.Call) (service : ScopedIO.WorldIO.Call)
    (platform : ScopedIO.WorldIO.Platform) (world : ScopedIO.WorldIO.World)
    (total next : ProofBox) (i : Nat) (c d : ProofBox) (bound : i+1<2^32)
    (same : world.app=BudgetProposed.afterProposed total next i c d) :
    ScopedIO.WorldSource.Eval SynergyC.Header.layout pure service platform
      (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1))) world
      ⟨WorldFooterState.afterIncrement total next i c d,world.stream⟩
      (FullMainPrefix.unsigned32 (i+1)) := by
  cases world with
  | mk app stream =>
      change app=BudgetProposed.afterProposed total next i c d at same
      subst app
      exact .pure (WorldFooterState.actual_increment pure total next i c d bound)

#print axioms eval_c_hi
#print axioms eval_d_hi
#print axioms world_increment
end SynergyMomentCHi.WorldFooterFields
