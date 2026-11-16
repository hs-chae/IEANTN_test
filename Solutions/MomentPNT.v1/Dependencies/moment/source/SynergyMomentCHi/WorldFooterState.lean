/- New high-only moment entry: source footer and scope restoration for an arbitrary
proved next accumulator, without assuming a numerical prefix or Model.term. -/
import SynergyMomentCHi.BudgetProposed
import SynergyHeightC.MainFooterState
import SynergyHeightC.FullMainEdges
import ScopedC.PoolExpressions
import SynergyC.SmallWord
namespace SynergyMomentCHi.WorldFooterState
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical SynergyHeightC SynergyMomentC
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

def indexAddress : Address := ⟨18,0,[]⟩

def afterIncrement (total next : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  {BudgetProposed.afterProposed total next i c d with
    heap:=(BudgetProposed.afterProposed total next i c d).heap.set 18
      ({type:="unsigned int",cells:=[some (FullMainPrefix.unsigned32 (i+1))]} : Object)}

theorem actual_footer (kind : Kind) : (loopStatements kind).drop 9=[
    .eval (.call (.var "emitU") [.field "." (.var "c") "hi"]),
    .eval (.call (.var "emitU") [.field "." (.var "D") "hi"]),
    .eval (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))] := by cases kind <;> rfl

theorem span_length : FullMainPrefix.afterSpan.heap.length=17 := by rfl

theorem index_lookup (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    Machine.getVar (BudgetProposed.afterProposed total next i c d) "i"=some indexAddress := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,indexAddress,span_length,List.lookup]

theorem index_heap (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    (BudgetProposed.afterProposed total next i c d).heap[18]?=
      some ({type:="unsigned int",cells:=[some (FullMainPrefix.unsigned32 i)]} : Object) := by
  simp [BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,span_length]

theorem source_read_i (call : Machine.Call) (fuel : Nat) (total next : ProofBox) (i : Nat)
    (c d : ProofBox) :
    evalExpr SynergyC.Header.layout call (fuel+1) (BudgetProposed.afterProposed total next i c d)
      (.var "i")=some (FullMainPrefix.unsigned32 i,BudgetProposed.afterProposed total next i c d) := by
  rw [evalExpr]
  simp [index_lookup,index_heap,indexAddress,Machine.read,Machine.nested,
    Machine.initialized,FullMainPrefix.unsigned32]

theorem source_lvalue_i (call : Machine.Call) (fuel : Nat) (total next : ProofBox) (i : Nat)
    (c d : ProofBox) :
    evalLValue SynergyC.Header.layout call (fuel+1) (BudgetProposed.afterProposed total next i c d)
      (.var "i")=some (indexAddress,true,BudgetProposed.afterProposed total next i c d) := by
  rw [evalLValue]
  simp [index_lookup,index_heap,indexAddress]

theorem binary_increment (s : State) (i : Nat) (bound : i+1<2^32) :
    binaryValue SynergyC.Header.layout s "+" (FullMainPrefix.unsigned32 i)
      (.integer ⟨⟨true,32⟩,1⟩)=some (FullMainPrefix.unsigned32 (i+1)) :=
  PoolCalls.binary_add_one s i bound

theorem increment_rhs (call : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    evalExpr SynergyC.Header.layout call 2 (BudgetProposed.afterProposed total next i c d)
      (.binary "+" (.var "i") (.nat 1))=
      some (FullMainPrefix.unsigned32 (i+1),BudgetProposed.afterProposed total next i c d) :=
  ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (source_read_i call 0 total next i c d) rfl (binary_increment _ i bound)

theorem actual_index_store (total next : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    Machine.write SynergyC.Header.layout (BudgetProposed.afterProposed total next i c d)
      indexAddress true (FullMainPrefix.unsigned32 (i+1))=
      some (FullMainPrefix.unsigned32 (i+1),afterIncrement total next i c d) := by
  have range : SynergyC.SmallWord.Range ((i+1:Nat):Int) := by
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast bound⟩
  have converted := SynergyC.SmallWord.cast_small_int
    (BudgetProposed.afterProposed total next i c d) range
  change castValue SynergyC.Header.layout (BudgetProposed.afterProposed total next i c d)
    100 "unsigned int" (FullMainPrefix.unsigned32 (i+1))=
      some (FullMainPrefix.unsigned32 (i+1)) at converted
  unfold Machine.write
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have type : addressType SynergyC.Header.layout (BudgetProposed.afterProposed total next i c d)
      indexAddress=some "unsigned int" := by
    simp [addressType,indexAddress,index_heap,typeAt]
  rw [type]
  simp only [Bind.bind,Option.bind]
  rw [converted]
  simp [indexAddress,index_heap,afterIncrement]

theorem actual_increment (call : Machine.Call) (total next : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    evalExpr SynergyC.Header.layout call 3 (BudgetProposed.afterProposed total next i c d)
      (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))=
      some (FullMainPrefix.unsigned32 (i+1),afterIncrement total next i c d) := by
  rw [evalExpr,increment_rhs call total next i c d bound]
  simp only [Bind.bind,Option.bind]
  rw [source_lvalue_i call 1 total next i c d]
  simp only [Bind.bind,Option.bind]
  exact actual_index_store total next i c d bound

theorem restores_loop_state (total next : ProofBox) (i : Nat) (c d : ProofBox) :
    Machine.popScope (FullMainEdges.loopState total i) (afterIncrement total next i c d)=
      FullMainEdges.loopState next (i+1) := by
  simp [Machine.popScope,afterIncrement,BudgetProposed.afterProposed,Budget.storeInterval,Budget.afterW,
    Budget.afterFD,Budget.afterFC,Budget.afterC,Budget.before,
    MainBudgetExecute.storeInterval,MainBudgetExecute.before,
    MainBudgetExecute.afterW,MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,
    MainBudgetExecute.afterC,MainBudgetExecute.before,PointExecuteAPI.filled,
    FullMainFrame.base,FullMainFrame.throughLeft,FullMainEdges.loopState,Machine.allocate,
    span_length,List.append_assoc,List.take_append]

#print axioms actual_increment
#print axioms restores_loop_state
end SynergyMomentCHi.WorldFooterState
