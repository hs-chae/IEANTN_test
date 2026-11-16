/- Source store and unsigned-index update for each of the eight output words. -/
import SynergyHeightC.EmitUWrites
namespace SynergyHeightC.EmitULoopStep
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyHeightC.EmitUStorage SynergyHeightC.EmitUExpressions
open SynergyHeightC.EmitUArrayAccess SynergyHeightC.EmitUWrites
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem actual_store (call : Machine.Call) (caller : State) (x : Int)
    (hx : SynergyC.Word512.Range x) (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call 6 (frame caller x i)
      (.binary "=" (.index (.var "words") (.var "i")) rhs)=
      some (EmitUWord64.value (EmitUWord64.part x i),frameAt caller x (i+1) i) := by
  rw [evalExpr,eval_rhs call 1 caller x hx i hi]
  simp only [Bind.bind,Option.bind]
  rw [lvalue_element call 3 caller x i hi]
  simp only [Bind.bind,Option.bind]
  exact store_word caller x i hi

theorem frameAt_heap (caller : State) (x : Int) (completed index : Nat) :
    (frameAt caller x completed index).heap=caller.heap++[
      {type:="U",cells:=[some (SynergyC.Word512.value x)]},arrayObject x completed,
      {type:="unsigned int",cells:=[some (indexValue index)]}] := by
  simp [frameAt,array,EmitUFrames.parameter,Machine.allocate,indexValue,List.append_assoc]

theorem frameAt_get_i (caller : State) (x : Int) (completed index : Nat) :
    Machine.getVar (frameAt caller x completed index) "i"=some (iAddress caller) := by
  simp [frameAt,array,EmitUFrames.parameter,Machine.allocate,Machine.getVar,
    iAddress,List.length_append,List.lookup]

theorem read_index (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int)
    (completed index : Nat) :
    evalExpr SynergyC.Header.layout call (fuel+1) (frameAt caller x completed index)
      (.var "i")=some (indexValue index,frameAt caller x completed index) := by
  rw [evalExpr]
  simp [frameAt_get_i,frameAt_heap,iAddress,Machine.read,Machine.nested,
    Machine.initialized,indexValue]

theorem lvalue_index (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int)
    (completed index : Nat) :
    evalLValue SynergyC.Header.layout call (fuel+1) (frameAt caller x completed index)
      (.var "i")=some (iAddress caller,true,frameAt caller x completed index) := by
  rw [evalLValue]
  simp [frameAt_get_i,frameAt_heap,iAddress]

theorem cast_index (s : State) (i : Nat) (hi : i≤8) :
    castValue SynergyC.Header.layout s 100 "unsigned int" (indexValue i)=
      some (indexValue i) := by
  interval_cases i <;> rfl

theorem binary_increment (s : State) (i : Nat) (hi : i<8) :
    binaryValue SynergyC.Header.layout s "+" (indexValue i)
      (.integer ⟨⟨true,32⟩,1⟩)=some (indexValue (i+1)) := by
  interval_cases i <;> rfl

theorem eval_increment_rhs (call : Machine.Call) (caller : State) (x : Int)
    (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call 2 (frameAt caller x (i+1) i)
      (.binary "+" (.var "i") (.nat 1))=
      some (indexValue (i+1),frameAt caller x (i+1) i) := by
  exact ExpressionTemplates.binary SynergyC.Header.layout call
    (by decide) (by decide) (by decide) (by decide)
    (read_index call 0 caller x (i+1) i) rfl
    (binary_increment _ i hi)

theorem write_index (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    Machine.write SynergyC.Header.layout (frameAt caller x (i+1) i) (iAddress caller)
      true (indexValue (i+1))=some (indexValue (i+1),frame caller x (i+1)) := by
  unfold Machine.write
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have type : addressType SynergyC.Header.layout (frameAt caller x (i+1) i) (iAddress caller)=
      some "unsigned int" := by
    simp [addressType,iAddress,frameAt_heap,typeAt]
  rw [type]
  simp only [Bind.bind,Option.bind]
  rw [cast_index _ (i+1) (by omega)]
  simp [frameAt_heap,iAddress,frameAt,frame,array,EmitUFrames.parameter,Machine.allocate,
    List.append_assoc,indexValue,List.set_append_right
      (s:=caller.heap) (caller.heap.length+2) _ (by omega)]

theorem actual_increment (call : Machine.Call) (caller : State) (x : Int)
    (i : Nat) (hi : i<8) :
    evalExpr SynergyC.Header.layout call 3 (frameAt caller x (i+1) i)
      (.binary "=" (.var "i") (.binary "+" (.var "i") (.nat 1)))=
      some (indexValue (i+1),frame caller x (i+1)) := by
  rw [evalExpr,eval_increment_rhs call caller x i hi]
  simp only [Bind.bind,Option.bind]
  rw [lvalue_index call 1 caller x (i+1) i]
  simp only [Bind.bind,Option.bind]
  exact write_index caller x i hi

#print axioms actual_store
#print axioms actual_increment
end SynergyHeightC.EmitULoopStep
