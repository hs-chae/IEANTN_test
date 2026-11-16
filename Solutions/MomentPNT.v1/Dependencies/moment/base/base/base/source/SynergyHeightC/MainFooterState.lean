/- Actual main-loop footer locations and stack restoration after the index store. -/
import SynergyHeightC.MainBudgetExecute
import SynergyHeightC.FullMainEdges
import ScopedC.PoolExpressions
import SynergyC.SmallWord
namespace SynergyHeightC.MainFooterState
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000

def nextTotal (total : ProofBox) (i : Nat) (c d : ProofBox) : ProofBox :=
  ProofBox.add total (MainWeightModel.term (MainBudgetExecute.left i) (MainBudgetExecute.right i) c d)

def indexAddress : Address := ⟨18,0,[]⟩

def afterIncrement (total : ProofBox) (i : Nat) (c d : ProofBox) : State :=
  {MainBudgetExecute.afterBudget total i c d with
    heap:=(MainBudgetExecute.afterBudget total i c d).heap.set 18
      ({type:="unsigned int",cells:=[some (FullMainPrefix.unsigned32 (i+1))]} : Object)}

theorem actual_footer : PointExecuteAPI.loopStatements.drop 9=[
    .eval (.call (.var "emitU") [.field "." (.var "c") "hi"]),
    .eval (.call (.var "emitU") [.field "." (.var "D") "hi"]),
    .eval (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))] := by rfl

theorem span_length : FullMainPrefix.afterSpan.heap.length=17 := by rfl

theorem index_lookup (total : ProofBox) (i : Nat) (c d : ProofBox) :
    Machine.getVar (MainBudgetExecute.afterBudget total i c d) "i"=some indexAddress := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,Machine.getVar,indexAddress,span_length,List.lookup]

theorem index_heap (total : ProofBox) (i : Nat) (c d : ProofBox) :
    (MainBudgetExecute.afterBudget total i c d).heap[18]?=
      some ({type:="unsigned int",cells:=[some (FullMainPrefix.unsigned32 i)]} : Object) := by
  simp [MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,MainBudgetExecute.afterW,
    MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,MainBudgetExecute.afterC,
    MainBudgetExecute.before,PointExecuteAPI.filled,FullMainFrame.base,FullMainFrame.throughLeft,
    Machine.allocate,span_length]

theorem source_read_i (call : Machine.Call) (fuel : Nat) (total : ProofBox) (i : Nat)
    (c d : ProofBox) :
    evalExpr SynergyC.Header.layout call (fuel+1) (MainBudgetExecute.afterBudget total i c d)
      (.var "i")=some (FullMainPrefix.unsigned32 i,MainBudgetExecute.afterBudget total i c d) := by
  rw [evalExpr]
  simp [index_lookup,index_heap,indexAddress,Machine.read,Machine.nested,
    Machine.initialized,FullMainPrefix.unsigned32]

theorem source_lvalue_i (call : Machine.Call) (fuel : Nat) (total : ProofBox) (i : Nat)
    (c d : ProofBox) :
    evalLValue SynergyC.Header.layout call (fuel+1) (MainBudgetExecute.afterBudget total i c d)
      (.var "i")=some (indexAddress,true,MainBudgetExecute.afterBudget total i c d) := by
  rw [evalLValue]
  simp [index_lookup,index_heap,indexAddress]

theorem binary_increment (s : State) (i : Nat) (bound : i+1<2^32) :
    binaryValue SynergyC.Header.layout s "+" (FullMainPrefix.unsigned32 i)
      (.integer ⟨⟨true,32⟩,1⟩)=some (FullMainPrefix.unsigned32 (i+1)) :=
  PoolCalls.binary_add_one s i bound

theorem increment_rhs (call : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    evalExpr SynergyC.Header.layout call 2 (MainBudgetExecute.afterBudget total i c d)
      (.binary "+" (.var "i") (.nat 1))=
      some (FullMainPrefix.unsigned32 (i+1),MainBudgetExecute.afterBudget total i c d) :=
  ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (source_read_i call 0 total i c d) rfl (binary_increment _ i bound)

theorem actual_index_store (total : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    Machine.write SynergyC.Header.layout (MainBudgetExecute.afterBudget total i c d)
      indexAddress true (FullMainPrefix.unsigned32 (i+1))=
      some (FullMainPrefix.unsigned32 (i+1),afterIncrement total i c d) := by
  have range : SynergyC.SmallWord.Range ((i+1:Nat):Int) := by
    exact ⟨Int.natCast_nonneg _,by exact_mod_cast bound⟩
  have converted := SynergyC.SmallWord.cast_small_int
    (MainBudgetExecute.afterBudget total i c d) range
  change castValue SynergyC.Header.layout (MainBudgetExecute.afterBudget total i c d)
    100 "unsigned int" (FullMainPrefix.unsigned32 (i+1))=
      some (FullMainPrefix.unsigned32 (i+1)) at converted
  unfold Machine.write
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have type : addressType SynergyC.Header.layout (MainBudgetExecute.afterBudget total i c d)
      indexAddress=some "unsigned int" := by
    simp [addressType,indexAddress,index_heap,typeAt]
  rw [type]
  simp only [Bind.bind,Option.bind]
  rw [converted]
  simp [indexAddress,index_heap,afterIncrement]

theorem actual_increment (call : Machine.Call) (total : ProofBox) (i : Nat) (c d : ProofBox)
    (bound : i+1<2^32) :
    evalExpr SynergyC.Header.layout call 3 (MainBudgetExecute.afterBudget total i c d)
      (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))=
      some (FullMainPrefix.unsigned32 (i+1),afterIncrement total i c d) := by
  rw [evalExpr,increment_rhs call total i c d bound]
  simp only [Bind.bind,Option.bind]
  rw [source_lvalue_i call 1 total i c d]
  simp only [Bind.bind,Option.bind]
  exact actual_index_store total i c d bound

theorem restores_loop_state (total : ProofBox) (i : Nat) (c d : ProofBox) :
    Machine.popScope (FullMainEdges.loopState total i) (afterIncrement total i c d)=
      FullMainEdges.loopState (nextTotal total i c d) (i+1) := by
  simp [Machine.popScope,afterIncrement,MainBudgetExecute.afterBudget,MainBudgetExecute.storeInterval,
    MainBudgetExecute.afterW,MainBudgetExecute.afterFD,MainBudgetExecute.afterFC,
    MainBudgetExecute.afterC,MainBudgetExecute.before,PointExecuteAPI.filled,
    FullMainFrame.base,FullMainFrame.throughLeft,FullMainEdges.loopState,Machine.allocate,
    span_length,nextTotal,List.append_assoc,List.take_append]

#print axioms actual_increment
#print axioms restores_loop_state
end SynergyHeightC.MainFooterState
