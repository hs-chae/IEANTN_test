/- Physical resource facts for iterating the original printS body. -/
import ScopedIO.PrintSStepEvents
import ScopedC.CursorBorrow

namespace ScopedIO.PrintSGenerationEffects
open ScopedC ScopedC.Machine ScopedC.PoolCalls ScopedC.PoolCursor
open ScopedIO.PrintSIteration
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem top (l : PoolLayout) (c : Cursor) (n : Nat) :
    (finalCursor l c n).top = c.top+5 := by
  rw [final_trace,CursorFrames.top_advance]
  rfl

theorem size (l : PoolLayout) (c : Cursor) (n : Nat) :
    (finalCursor l c n).state.nats.values.length = c.state.nats.values.length+5 := by
  rw [final_trace,CursorEffects.size]
  rfl

theorem valid {l : PoolLayout} {c : Cursor} (ctx : Valid l c) (n : Nat)
    (room : c.top+5 ≤ capacity) : Valid l (finalCursor l c n) := by
  rw [final_trace]
  exact CursorFrames.advance_valid ctx _ room

theorem quotient (l : PoolLayout) (c : Cursor) (n : Nat) :
    NatArena.Borrow (finalCursor l c n).state.nats (finalSlot l c n) (n/10) :=
  next_borrow l (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)) (n/10)

theorem preserves {l : PoolLayout} {c : Cursor} {slot value : Nat}
    (live : NatArena.Borrow c.state.nats slot value) (n : Nat) :
    NatArena.Borrow (finalCursor l c n).state.nats slot value := by
  rw [final_trace]
  exact CursorBorrow.preserves _ live

end ScopedIO.PrintSGenerationEffects
