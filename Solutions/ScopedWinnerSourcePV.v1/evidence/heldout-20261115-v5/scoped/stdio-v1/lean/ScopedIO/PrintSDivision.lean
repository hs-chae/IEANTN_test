/- Original printS quotient update, after its digit store and count increment.
Both allocating source callees and the typed local N store are retained. -/
import ScopedIO.PrintSCondition

namespace ScopedIO.PrintSDivision
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def q1 (l : PoolLayout) (c : Cursor) : Cursor := next l c 10
def q2 (l : PoolLayout) (c : Cursor) (n : Nat) : Cursor := next l (q1 l c) (n/10)

theorem source_calls (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (ndInstalled : Generated.f_nd ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {c : Cursor} {slot n : Nat}
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+1 < capacity) (a : Value) (ds : List Nat) (count first : Nat) :
    SourceCall Header.layout code 3 "nu" [DecimalDigits.integer 10]
      (frame c.state a ds slot count first) (.natObject c.state.nats.values.length)
      (frame (q1 l c).state a ds slot count first) ∧
    SourceCall Header.layout code 3 "nd" [.natObject slot,.natObject c.state.nats.values.length]
      (frame (q1 l c).state a ds slot count first)
      (.natObject (q1 l c).state.nats.values.length)
      (frame (q2 l c n).state a ds slot count first) := by
  have cq : Valid l (q1 l c) := next_valid 10 ctx (by omega)
  have nuRun := nu_call (n:=10) (input:=DecimalDigits.integer 10) code nuInstalled
    keepInstalled (PrintSPoolFrames.frame_context ctx a ds slot count first)
    (by omega) (by norm_num) rfl
  have ten : NatArena.Borrow (q1 l c).state.nats c.state.nats.values.length 10 :=
    next_borrow l c 10
  have old : NatArena.Borrow (q1 l c).state.nats slot n := preserves live
  have ndRun := nd_call code ndInstalled keepInstalled
    (PrintSPoolFrames.frame_context cq a ds slot count first)
    (by change c.top+1 < capacity; omega) old ten (by decide)
  constructor
  · apply raise_once
    simpa only [PrintSDigitCalls.frame_nats,PrintSPoolFrames.frame_binary ctx,q1,next] using nuRun
  · apply raise_once
    simpa only [PrintSDigitCalls.frame_nats,PrintSPoolFrames.frame_binary cq,q2,next] using ndRun

theorem changed_x (s : State) (a : Value) (ds : List Nat)
    (slot count first fresh : Nat) :
    LocalAssignment.changed (frame s a ds slot count first) (s.heap.length+3)
      "N" (.natObject fresh) = frame s a ds fresh count first := by
  simp [LocalAssignment.changed,storeObject,frame,buffer,parameter,allocate,
    List.set_append,Nat.add_assoc]

theorem actual_assignment (service : Call) (l : PoolLayout) (c : Cursor)
    (a : Value) (ds : List Nat) (slot count first n : Nat)
    (nuAnswer : service "nu" [DecimalDigits.integer 10]
      (frame c.state a ds slot count first) =
      some (.natObject c.state.nats.values.length,frame (q1 l c).state a ds slot count first))
    (ndAnswer : service "nd" [.natObject slot,.natObject c.state.nats.values.length]
      (frame (q1 l c).state a ds slot count first) =
      some (.natObject (q1 l c).state.nats.values.length,
        frame (q2 l c n).state a ds slot count first)) :
    Eval Header.layout service
      (.binary "=" (.var "x") (.call (.var "nd") [.var "x",.call (.var "nu") [.nat 10]]))
      (frame c.state a ds slot count first)
      (frame (q2 l c n).state a ds (q1 l c).state.nats.values.length count first)
      (.natObject (q1 l c).state.nats.values.length) := by
  have xValue := LocalBinding.eval service 1 (PrintSDigitRHS.x_at c.state a ds slot count first)
    (by decide) (by decide) (by decide) (by decide)
  have nuResult := ExpressionTemplates.call_one Header.layout service
    (show evalExpr Header.layout service 1 (frame c.state a ds slot count first) (.nat 10) =
      some (DecimalDigits.integer 10,frame c.state a ds slot count first) from rfl) nuAnswer
  have ndResult := ExpressionTemplates.call_two Header.layout service xValue nuResult ndAnswer
  have fresh : NatArena.Borrow (q2 l c n).state.nats
      (q1 l c).state.nats.values.length (n/10) := next_borrow l (q1 l c) (n/10)
  refine ⟨4,?_⟩
  simpa only [changed_x] using LocalAssignment.evaluate service 2 ndResult
    (PrintSDigitRHS.x_at (q2 l c n).state a ds slot count first)
    (PrimitiveCalls.cast_N fresh)

end ScopedIO.PrintSDivision
