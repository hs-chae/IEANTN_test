/- The original printS writes exactly one previously uninitialized char cell
at the end of its decimal prefix. No prefilled buffer is assumed. -/
import ScopedIO.PrintSRead
import ScopedC.UnsignedLiteralControl

namespace ScopedIO.PrintSBuffer
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem unwritten {ds : List Nat} (capacity : ds.length < 1024) :
    (digitCells ds)[ds.length]? = some none := by
  simp [digitCells,List.getElem?_append,capacity]

theorem append_digit {ds : List Nat} (capacity : ds.length < 1024) (d : Nat) :
    (digitCells ds).set ds.length (some (DecimalDigits.digit d)) = digitCells (ds++[d]) := by
  have remaining : 1024-ds.length = (1024-(ds.length+1))+1 := by omega
  simp [digitCells,List.set_append,remaining,List.replicate_succ,List.append_assoc]

theorem cast_digit (s : State) (d : Nat) (decimal : d < 10) :
    castValue Header.layout s 100 "char" (DecimalDigits.digit d) =
      some (DecimalDigits.digit d) := by
  interval_cases d <;> rfl

theorem store_prefix (s : State) (a : Value) (ds : List Nat)
    (slot count first d : Nat) (capacity : ds.length < 1024) :
    {frame s a ds slot count first with
      heap := (frame s a ds slot count first).heap.set (s.heap.length+1)
        {type := "char",cells := (digitCells ds).set ds.length
          (some (DecimalDigits.digit d)),isArray := true}} =
      frame s a (ds++[d]) slot count first := by
  rw [append_digit capacity]
  simp [frame,buffer,parameter,allocate,List.set_append,Nat.add_assoc]

theorem write_digit (s : State) (a : Value) (ds : List Nat)
    (slot count first d : Nat) (capacity : ds.length < 1024) (decimal : d < 10) :
    write Header.layout (frame s a ds slot count first)
      ⟨s.heap.length+1,ds.length,[]⟩ true (DecimalDigits.digit d) =
      some (DecimalDigits.digit d,frame s a (ds++[d]) slot count first) := by
  have old := unwritten capacity
  have size := cells_length (show ds.length ≤ 1024 by omega)
  have bounds : ds.length < (digitCells ds).length := by omega
  have cell : (digitCells ds)[ds.length] = none :=
    (List.getElem?_eq_some_iff.mp old).choose_spec
  simp only [write,addressType,PrintSRead.buffer_object,typeAt,Bind.bind,Option.bind,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,List.isEmpty_nil,bounds]
  rw [cast_digit _ _ decimal]
  simp only [Option.bind,PrintSRead.buffer_object,old]
  simpa only [pure] using congrArg (fun t => some (DecimalDigits.digit d,t))
    (store_prefix s a ds slot count first d capacity)

theorem capacity_guard (service : Call) (s : State) (a : Value) (ds : List Nat)
    (slot count first : Nat) (bound : count < 2^32) :
    SourceCalls.Eval Header.layout service (.binary ">=" (.var "count") (.nat 1024))
      (frame s a ds slot count first) (frame s a ds slot count first)
      (boolean Header.layout (decide (count ≥ 1024))) := by
  have binary := UnsignedLiteralControl.literal_lift (frame s a ds slot count first)
    ">=" count 1024 bound (by norm_num)
  rw [UnsignedLiteralControl.binary_ge _ count 1024 bound (by norm_num)] at binary
  exact ⟨3,ExpressionTemplates.binary Header.layout service
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (LocalBinding.eval service 1 (count_at s a ds slot count first)
      (by decide) (by decide) (by decide) (by decide)) (by rfl) binary⟩

end ScopedIO.PrintSBuffer
