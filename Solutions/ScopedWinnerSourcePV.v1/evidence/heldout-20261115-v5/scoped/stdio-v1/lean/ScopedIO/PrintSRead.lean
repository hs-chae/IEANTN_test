/- Typed reads and actual putchar execution from printS's own digit array.
The generation-loop invariant must establish the written prefix separately. -/
import ScopedIO.PrintSFrames
import ScopedIO.WorldSourceWith

namespace ScopedIO.PrintSRead
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedIO.PrintSFrames ScopedIO.WorldIO
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem buffer_object (s : State) (a : Value) (ds : List Nat) (slot count first : Nat) :
    (frame s a ds slot count first).heap[s.heap.length+1]? =
      some {type := "char",cells := digitCells ds,isArray := true} := by
  simp [frame,buffer,parameter,allocate,List.getElem?_append,Nat.add_assoc]

theorem written_cell {ds : List Nat} {k : Nat} (hk : k < ds.length) :
    (digitCells ds)[k]? = some (some (DecimalDigits.digit ds[k])) := by
  unfold digitCells
  rw [List.getElem?_append_left (by simpa using hk)]
  simp [hk]

theorem array_value (pureCall : Machine.Call) (fuel : Nat) (s : State) (a : Value)
    (ds : List Nat) (slot count first : Nat) :
    evalExpr Header.layout pureCall (fuel+1) (frame s a ds slot count first) (.var "digits") =
      some (.pointer ⟨s.heap.length+1,0,[]⟩ true,frame s a ds slot count first) := by
  rw [evalExpr]
  have lookup : getVar (frame s a ds slot count first) "digits" =
      some ⟨s.heap.length+1,0,[]⟩ := by
    simp [getVar,frame,buffer,parameter,allocate,List.lookup,Nat.add_assoc]
  simp [lookup,buffer_object]

theorem index_value (pureCall : Machine.Call) (fuel : Nat) (s : State) (a : Value)
    (ds : List Nat) (slot k first : Nat) (hk : k < ds.length) :
    evalExpr Header.layout pureCall (fuel+3) (frame s a ds slot k first)
      (.index (.var "digits") (.var "count")) =
      some (DecimalDigits.digit ds[k],frame s a ds slot k first) := by
  have countValue := LocalBinding.eval pureCall fuel (count_at s a ds slot k first)
    (by decide) (by decide) (by decide) (by decide)
  have cell := written_cell hk
  have kb : k < (digitCells ds).length := (List.getElem?_eq_some_iff.mp cell).choose
  have cv : (digitCells ds)[k] = some (DecimalDigits.digit ds[k]) :=
    (List.getElem?_eq_some_iff.mp cell).choose_spec
  rw [evalExpr,evalLValue,array_value]
  simp only [Bind.bind,Option.bind,List.isEmpty_nil,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  rw [countValue]
  simp [Bind.bind,Option.bind,asNat,word,unsigned32,addressType,buffer_object,
    Machine.read,cell,cv,kb,typeAt,nested,initialized,DecimalDigits.digit,Nat.zero_add]

theorem digit_argument (d : Nat) (hd : d < 10) :
    TextWorldIO.characterArgument (DecimalDigits.digit d) = some (48+d) := by
  interval_cases d <;> rfl

/-- All I/O policies are retained: this is the byte actually read from the
application array, with the documented successful/failed putchar result. -/
theorem source_putchar (p : WorldIO.Platform) (fault : WorldIO.FaultPolicy)
    (pureCall : Machine.Call) (s : State) (a : Value) (ds : List Nat)
    (slot k first : Nat) (hk : k < ds.length) (hd : ds[k] < 10) (stream : Stream) :
    WorldSource.Eval Header.layout pureCall (TextWorldIO.external p fault) p
      (.call (.var "putchar") [.index (.var "digits") (.var "count")])
      ⟨frame s a ds slot k first,stream⟩
      {app := frame s a ds slot k first,
       stream := writeBytes stream [48+ds[k]]
         (fault.succeed "putchar" ⟨frame s a ds slot k first,stream⟩)
         (fault.count "putchar" ⟨frame s a ds slot k first,stream⟩)}
      (signed32 (if fault.succeed "putchar" ⟨frame s a ds slot k first,stream⟩
        then 48+ds[k] else -1)) := by
  apply WorldSource.Eval.call
    (WorldSource.Arguments.cons (WorldSource.Eval.pure (index_value pureCall 0 s a ds slot k first hk))
      (WorldSource.Arguments.nil _))
  change TextWorldIO.external p fault "putchar" [DecimalDigits.digit ds[k]] _ = _
  have result := TextWorldIO.putchar_result p fault (digit_argument ds[k] hd)
    (⟨frame s a ds slot k first,stream⟩ : World)
  simpa [TextWorldIO.external,RuntimeCore.call,RuntimeCore.binaryName] using result

end ScopedIO.PrintSRead
