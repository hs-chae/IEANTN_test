/- Original printS typed local assignments. Conversion of a signed literal to
an unsigned local is established by the C machine, rather than assumed to be
an identity conversion. This component does not close the generation loop. -/
import ScopedIO.PrintSFrames

namespace ScopedIO.PrintSAssignments
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
open ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem write_cast {s : State} {name type : String} {old input output : Value}
    {slot : Nat} (atLocal : LocalBinding.At s name type old slot)
    (convert : castValue Header.layout s 100 type input = some output) :
    write Header.layout s ⟨slot,0,[]⟩ true input =
      some (output,LocalAssignment.changed s slot type output) := by
  simp [write,addressType,typeAt,atLocal.memory,convert,LocalAssignment.changed,
    PoolCalls.storeObject]

theorem evaluate_cast (service : Call) (fuel : Nat) {s middle : State} {rhs : Expr}
    {name type : String} {old input output : Value} {slot : Nat}
    (right : evalExpr Header.layout service (fuel+1) s rhs = some (input,middle))
    (atLocal : LocalBinding.At middle name type old slot)
    (convert : castValue Header.layout middle 100 type input = some output) :
    evalExpr Header.layout service (fuel+2) s (.binary "=" (.var name) rhs) =
      some (output,LocalAssignment.changed middle slot type output) := by
  rw [evalExpr,right]
  simp only [Bind.bind,Option.bind]
  rw [LocalAssignment.lvalue service fuel atLocal]
  exact write_cast atLocal convert

theorem first_at (s : State) (a : Value) (ds : List Nat)
    (slot count first : Nat) :
    LocalBinding.At (frame s a ds slot count first) "first" "unsigned int"
      (word first) (s.heap.length+4) := by
  simpa [frame,buffer,parameter,allocate,word,unsigned32,Nat.add_assoc] using
    (LocalBinding.allocate_head
      (allocate (allocate (buffer s a ds) "unsigned int" "count"
        (some (word count))) "N" "x" (some (.natObject slot)))
      "first" "unsigned int" (word first) rfl)

theorem changed_first (s : State) (a : Value) (ds : List Nat)
    (slot count first next : Nat) :
    LocalAssignment.changed (frame s a ds slot count first) (s.heap.length+4)
      "unsigned int" (word next) = frame s a ds slot count next := by
  simp [LocalAssignment.changed,storeObject,frame,buffer,parameter,allocate,
    word,unsigned32,List.set_append,Nat.add_assoc]

theorem first_zero_source (service : Call) (s : State) (a : Value) (ds : List Nat)
    (slot count first : Nat) :
    SourceCalls.Eval Header.layout service (.binary "=" (.var "first") (.nat 0))
      (frame s a ds slot count first) (frame s a ds slot count 0) (word 0) := by
  refine ⟨2,?_⟩
  rw [←changed_first s a ds slot count first 0]
  exact evaluate_cast service 0 (by rfl) (first_at s a ds slot count first) rfl

end ScopedIO.PrintSAssignments
