/- Bounds, type and exact lvalues of the actual emitU stores. -/
import SynergyHeightC.EmitUExpressions
namespace SynergyHeightC.EmitUArrayAccess
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyHeightC.EmitUStorage SynergyHeightC.EmitUExpressions
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def elementAddress (caller : State) (i : Nat) : Address := ⟨caller.heap.length+1,i,[]⟩

theorem element_type (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    Machine.addressType SynergyC.Header.layout (frame caller x i) (elementAddress caller i)=
      some "uint64_t" := by
  simp [Machine.addressType,elementAddress,heap_shape,arrayObject,partial_length,hi,Machine.typeAt]

theorem lvalue_i (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) :
    evalLValue SynergyC.Header.layout call (fuel+1) (frame caller x i) (.var "i")=
      some (iAddress caller,true,frame caller x i) := by
  rw [evalLValue]
  simp [get_i,heap_shape,iAddress]

theorem lvalue_element (call : Machine.Call) (fuel : Nat) (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    evalLValue SynergyC.Header.layout call (fuel+2) (frame caller x i)
      (.index (.var "words") (.var "i"))=
        some (elementAddress caller i,true,frame caller x i) := by
  rw [evalLValue,eval_words]
  simp only [Bind.bind,Option.bind,wordsAddress,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [eval_i]
  simp only [Bind.bind,Option.bind,asNat,indexValue,Int.natCast_nonneg,↓reduceIte,Int.toNat_natCast,Nat.zero_add]
  change (do let _ ← Machine.addressType SynergyC.Header.layout (frame caller x i) (elementAddress caller i)
             pure (elementAddress caller i,true,frame caller x i))=_
  rw [element_type _ _ _ hi]
  rfl

theorem current_uninitialized (x : Int) (i : Nat) (hi : i<8) :
    (partialCells x i)[i]?=some none := by
  interval_cases i <;> rfl

theorem store_progress (x : Int) (i : Nat) (hi : i<8) :
    (partialCells x i).set i (some (EmitUWord64.value (EmitUWord64.part x i)))=
      partialCells x (i+1) := by
  interval_cases i <;> rfl

#print axioms element_type
#print axioms lvalue_element
#print axioms current_uninitialized
#print axioms store_progress
end SynergyHeightC.EmitUArrayAccess
