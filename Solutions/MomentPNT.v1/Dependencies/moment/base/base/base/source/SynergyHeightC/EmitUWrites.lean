/- Actual typed stores of the source eight-word loop. -/
import SynergyHeightC.EmitUArrayAccess
namespace SynergyHeightC.EmitUWrites
open ScopedC ScopedC.Machine
open SynergyHeightC.EmitUStorage SynergyHeightC.EmitUExpressions SynergyHeightC.EmitUArrayAccess
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def frameAt (caller : State) (x : Int) (completed index : Nat) : State :=
  allocate (array caller x completed) "unsigned int" "i" (some (indexValue index))

theorem diagonal (caller : State) (x : Int) (i : Nat) : frameAt caller x i i=frame caller x i := by rfl

theorem cast_own_part (s : State) (x : Int) (i : Nat) :
    Machine.castValue SynergyC.Header.layout s 100 "uint64_t" (EmitUWord64.value (EmitUWord64.part x i))=
      some (EmitUWord64.value (EmitUWord64.part x i)) := by
  change (do let v ← Scalar.make EmitUWord64.type (EmitUWord64.part x i); pure (Value.integer v))=_
  have range : Scalar.InRange EmitUWord64.type (EmitUWord64.part x i) := by
    change 0<64 ∧ 0≤EmitUWord64.part x i ∧ EmitUWord64.part x i<2^64
    exact ⟨by decide,EmitUWord64.part_range x i⟩
  rw [Scalar.make_exact range]
  rfl

theorem array_entry (caller : State) (x : Int) (i : Nat) :
    (frame caller x i).heap[caller.heap.length+1]?=some (arrayObject x i) := by
  simp [heap_shape]

def storedArray (x : Int) (i : Nat) : Object :=
  {arrayObject x i with cells := ((partialCells x i).set i (some (EmitUWord64.value (EmitUWord64.part x i))))}

theorem replace_array (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    {frame caller x i with heap:=(frame caller x i).heap.set (caller.heap.length+1) (storedArray x i)}=
      frameAt caller x (i+1) i := by
  simp [frameAt,frame,array,EmitUFrames.parameter,Machine.allocate,indexValue,
    List.append_assoc,List.set_append_right (s:=caller.heap) (caller.heap.length+1) _ (by omega),
    storedArray,arrayObject,store_progress x i hi]

theorem store_word (caller : State) (x : Int) (i : Nat) (hi : i<8) :
    Machine.write SynergyC.Header.layout (frame caller x i) (elementAddress caller i) true
      (EmitUWord64.value (EmitUWord64.part x i))=
        some (EmitUWord64.value (EmitUWord64.part x i),frameAt caller x (i+1) i) := by
  unfold Machine.write
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [element_type _ _ _ hi]
  simp only [Bind.bind,Option.bind]
  rw [cast_own_part]
  simp only [Bind.bind,Option.bind]
  have entry : (frame caller x i).heap[(elementAddress caller i).object]?=some (arrayObject x i) :=
    array_entry caller x i
  rw [entry]
  simp only [Bind.bind,Option.bind,elementAddress]
  rw [show (arrayObject x i).cells[i]?=some none from current_uninitialized x i hi]
  simp only [Bind.bind,Option.bind]
  change some (EmitUWord64.value (EmitUWord64.part x i),
    {frame caller x i with heap := (frame caller x i).heap.set (caller.heap.length+1) (storedArray x i)}) = _
  exact congrArg (fun state : State => some (EmitUWord64.value (EmitUWord64.part x i),state))
    (replace_array caller x i hi)

#print axioms cast_own_part
#print axioms replace_array
#print axioms store_word
end SynergyHeightC.EmitUWrites
