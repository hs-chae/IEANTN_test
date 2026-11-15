/- Exact finite-source-event postcondition for subsequent printS checks.
The forced first iteration is handled separately. Zero still allocates once
inside the actual nz callee before the while loop terminates. -/
import ScopedIO.PrintSGenerationEffects

namespace ScopedIO.PrintSTailPost
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSIteration
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

structure Post (code : List Function) (l : PoolLayout) (start final : Cursor)
    (a : Value) (inputSlot outputSlot n : Nat) (ds : List Nat)
    (events : List (CallEvents.Event Header.layout code 3)) : Prop where
  valid : Valid l final
  live : NatArena.Borrow final.state.nats outputSlot 0
  effects : ∃ values : List Nat, final = CursorFrames.advance l start values ∧
    values.length = 6*(Nat.digits 10 n).length+1
  counts : CallEvents.counts events =
    List.range' start.state.nats.values.length (6*(Nat.digits 10 n).length+1)
  source : ∀ service,Answers service events →
    Loops.WhileRun (Eval Header.layout service) (Declare Header.layout service)
      truth Scope PrintSCondition.expression body
      (frame start.state a ds inputSlot ds.length 0)
      (.continuing (frame final.state a (ds++Nat.digits 10 n) outputSlot
        (ds.length+(Nat.digits 10 n).length) 0))

theorem top {code : List Function} {l : PoolLayout} {start final : Cursor}
    {a : Value} {inputSlot outputSlot n : Nat} {ds : List Nat}
    {events : List (CallEvents.Event Header.layout code 3)}
    (post : Post code l start final a inputSlot outputSlot n ds events) :
    final.top = start.top+6*(Nat.digits 10 n).length+1 := by
  obtain ⟨values,equal,length⟩ := post.effects
  rw [equal,CursorFrames.top_advance,length]
  omega

theorem size {code : List Function} {l : PoolLayout} {start final : Cursor}
    {a : Value} {inputSlot outputSlot n : Nat} {ds : List Nat}
    {events : List (CallEvents.Event Header.layout code 3)}
    (post : Post code l start final a inputSlot outputSlot n ds events) :
    final.state.nats.values.length = start.state.nats.values.length+
      6*(Nat.digits 10 n).length+1 := by
  obtain ⟨values,equal,length⟩ := post.effects
  rw [equal,CursorEffects.size,length]
  omega

theorem preserves {code : List Function} {l : PoolLayout} {start final : Cursor}
    {a : Value} {inputSlot outputSlot n slot value : Nat} {ds : List Nat}
    {events : List (CallEvents.Event Header.layout code 3)}
    (post : Post code l start final a inputSlot outputSlot n ds events)
    (live : NatArena.Borrow start.state.nats slot value) :
    NatArena.Borrow final.state.nats slot value := by
  obtain ⟨values,equal,length⟩ := post.effects
  rw [equal]
  exact CursorBorrow.preserves values live

theorem shape {code : List Function} {l : PoolLayout} {start final : Cursor}
    {a : Value} {inputSlot outputSlot n : Nat} {ds : List Nat}
    {events : List (CallEvents.Event Header.layout code 3)}
    (post : Post code l start final a inputSlot outputSlot n ds events) :
    final.state.heap.length = start.state.heap.length ∧ final.state.env = start.state.env := by
  obtain ⟨values,equal,length⟩ := post.effects
  rw [equal]
  exact CursorEffects.shape _ _ _

theorem zero_case (code : List Function) (nzInstalled : Generated.f_nz ∈ code)
    (nuInstalled : Generated.f_nu ∈ code) (neInstalled : Generated.f_ne ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {c : Cursor} {slot : Nat}
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot 0)
    (room : c.top < capacity) (a : Value) (ds : List Nat) :
    ∃ final outputSlot es,Post code l c final a slot outputSlot 0 ds es := by
  have nzRun := PrintSCondition.actual_nz code nzInstalled nuInstalled neInstalled keepInstalled
    ctx live room a ds ds.length
  let ev : CallEvents.Event Header.layout code 3 :=
    ⟨"nz",[.natObject slot],frame c.state a ds slot ds.length 0,PrimitiveCalls.u32 true,
      frame (next l c 0).state a ds slot ds.length 0,nzRun⟩
  refine ⟨next l c 0,slot,[ev],next_valid 0 ctx room,PoolCursor.preserves live,?_,?_,?_⟩
  · exact ⟨[0],rfl,by simp⟩
  · simp [CallEvents.counts,ev,PrintSDigitCalls.frame_nats,List.range']
  · intro service answers
    have answer := answers ev (by simp)
    have check := PrintSCondition.subsequent service l c a ds slot ds.length 0 answer
    have run := Loops.WhileRun.done (Declare:=Declare Header.layout service)
      (Scope:=Scope) (truth:=truth) (body:=body) check rfl
    simpa using run

end ScopedIO.PrintSTailPost
