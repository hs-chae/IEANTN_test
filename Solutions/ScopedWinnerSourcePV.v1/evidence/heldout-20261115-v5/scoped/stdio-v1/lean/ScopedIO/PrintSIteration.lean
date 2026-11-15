/- One complete original generation-body iteration. The five actual lower
C calls remain proof-backed finite events, with the store/increment between
the first three calls and the last two. Full-loop composition is separate. -/
import ScopedIO.PrintSDivision
import ScopedIO.PrintSReverse
import ScopedC.CallEventLists

namespace ScopedIO.PrintSIteration
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def body : Stmt := .sequence [
  .eval (.binary "=" (.var "first") (.nat 0)),
  .branch (.binary ">=" (.var "count") (.nat 1024)) (.eval (.call (.var "fail") [])) .skip,
  .eval (.binary "=" (.index (.var "digits") (.var "count")) PrintSDigitRHS.expression),
  .eval (.binary "=" (.var "count") (.binary "+" (.var "count") (.nat 1))),
  .eval (.binary "=" (.var "x")
    (.call (.var "nd") [.var "x",.call (.var "nu") [.nat 10]]))]

def finalCursor (l : PoolLayout) (c : Cursor) (n : Nat) : Cursor :=
  PrintSDivision.q2 l (PrintSDigitCalls.c3 l c n) n

def finalSlot (l : PoolLayout) (c : Cursor) (n : Nat) : Nat :=
  (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state.nats.values.length

def Answers (service : Call) {code : List Function}
    (events : List (CallEvents.Event Header.layout code 3)) : Prop :=
  ∀ e∈events,service e.name e.args e.before = some (e.value,e.after)

theorem final_trace (l : PoolLayout) (c : Cursor) (n : Nat) :
    finalCursor l c n = CursorFrames.advance l c [10,n%10,4294967295,10,n/10] := rfl

theorem final_shape (l : PoolLayout) (c : Cursor) (n : Nat) :
    (finalCursor l c n).state.heap.length = c.state.heap.length ∧
      (finalCursor l c n).state.env = c.state.env := by
  rw [final_trace]
  exact CursorEffects.shape _ _ _

theorem body_run (service : Call) (l : PoolLayout) (c : Cursor)
    (a : Value) (ds : List Nat) (slot first n : Nat) (capacity : ds.length < 1024)
    (nu0 : service "nu" [DecimalDigits.integer 10]
      (frame c.state a ds slot ds.length 0) =
      some (.natObject c.state.nats.values.length,
        frame (PrintSDigitCalls.c1 l c).state a ds slot ds.length 0))
    (nr1 : service "nr" [.natObject slot,.natObject c.state.nats.values.length]
      (frame (PrintSDigitCalls.c1 l c).state a ds slot ds.length 0) =
      some (.natObject (PrintSDigitCalls.c1 l c).state.nats.values.length,
        frame (PrintSDigitCalls.c2 l c n).state a ds slot ds.length 0))
    (sm2 : service "small" [.natObject (PrintSDigitCalls.c1 l c).state.nats.values.length]
      (frame (PrintSDigitCalls.c2 l c n).state a ds slot ds.length 0) =
      some (unsigned32 (n%10),frame (PrintSDigitCalls.c3 l c n).state a ds slot ds.length 0))
    (nu3 : service "nu" [DecimalDigits.integer 10]
      (frame (PrintSDigitCalls.c3 l c n).state a (ds++[n%10]) slot (ds.length+1) 0) =
      some (.natObject (PrintSDigitCalls.c3 l c n).state.nats.values.length,
        frame (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state a
          (ds++[n%10]) slot (ds.length+1) 0))
    (nd4 : service "nd"
      [.natObject slot,.natObject (PrintSDigitCalls.c3 l c n).state.nats.values.length]
      (frame (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state a
        (ds++[n%10]) slot (ds.length+1) 0) =
      some (.natObject (finalSlot l c n),
        frame (finalCursor l c n).state a (ds++[n%10]) slot (ds.length+1) 0)) :
    Run Header.layout service body (frame c.state a ds slot ds.length first)
      (.continuing (frame (finalCursor l c n).state a
        (ds++[n%10]) (finalSlot l c n) (ds.length+1) 0)) := by
  have firstRun := PrintSAssignments.first_zero_source service c.state a ds slot ds.length first
  have guardRun : Run Header.layout service
      (.branch (.binary ">=" (.var "count") (.nat 1024)) (.eval (.call (.var "fail") [])) .skip)
      (frame c.state a ds slot ds.length 0)
      (.continuing (frame c.state a ds slot ds.length 0)) := by
    have check := PrintSBuffer.capacity_guard service c.state a ds slot ds.length 0
      (show ds.length < 2^32 by omega)
    have smaller : decide (ds.length ≥ 1024) = false := by simp [show ¬ ds.length ≥ 1024 by omega]
    rw [smaller] at check
    apply Loops.StmtRun.branch check
    exact Loops.StmtRun.skip _
  have rhs := PrintSDigitRHS.actual_expression service l c a ds slot ds.length 0 n nu0 nr1 sm2
  have storeRun : Eval Header.layout service
      (.binary "=" (.index (.var "digits") (.var "count")) PrintSDigitRHS.expression)
      (frame c.state a ds slot ds.length 0)
      (frame (PrintSDigitCalls.c3 l c n).state a (ds++[n%10]) slot ds.length 0)
      (DecimalDigits.digit (n%10)) :=
    ⟨7,PrintSDigitExpression.store_expression service 3
      (frame c.state a ds slot ds.length 0) (PrintSDigitCalls.c3 l c n).state
      a ds slot 0 (n%10) PrintSDigitRHS.expression capacity (by omega) rhs⟩
  have increment := UnsignedLocalSteps.increment service
    (count_at (PrintSDigitCalls.c3 l c n).state a (ds++[n%10]) slot ds.length 0)
    (show ds.length+1 < 2^32 by omega)
    (by decide) (by decide) (by decide) (by decide)
  rw [PrintSReverse.changed_count] at increment
  have quotient := PrintSDivision.actual_assignment service l (PrintSDigitCalls.c3 l c n)
    a (ds++[n%10]) slot (ds.length+1) 0 n nu3 nd4
  apply Loops.StmtRun.sequence
    (Loops.SeqRun.next (Loops.StmtRun.evaluate firstRun)
      (Loops.SeqRun.next guardRun
        (Loops.SeqRun.next (Loops.StmtRun.evaluate storeRun)
          (Loops.SeqRun.next (Loops.StmtRun.evaluate increment)
            (Loops.SeqRun.next (Loops.StmtRun.evaluate quotient) (Loops.SeqRun.nil _))))))
  have baseShape := final_shape l c n
  apply (pop_same ?_ ?_).symm
  · simp [frame,buffer,parameter,allocate,baseShape.1]
  · simp [frame,buffer,parameter,allocate,baseShape.1]

end ScopedIO.PrintSIteration
