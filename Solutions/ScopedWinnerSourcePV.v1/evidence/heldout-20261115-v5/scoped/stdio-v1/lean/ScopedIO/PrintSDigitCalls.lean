/- The original printS digit expression's actual nu, nr and small calls,
including small's own UINT_MAX allocation and all physical caller locals. -/
import ScopedIO.PrintSPoolFrames

namespace ScopedIO.PrintSDigitCalls
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

def c1 (l : PoolLayout) (c : Cursor) : Cursor := next l c 10
def c2 (l : PoolLayout) (c : Cursor) (n : Nat) : Cursor := next l (c1 l c) (n%10)
def c3 (l : PoolLayout) (c : Cursor) (n : Nat) : Cursor := next l (c2 l c n) 4294967295

theorem frame_nats (s : State) (a : Value) (ds : List Nat) (slot count first : Nat) :
    (frame s a ds slot count first).nats = s.nats := rfl

theorem contexts {l : PoolLayout} {c : Cursor} (ctx : Valid l c)
    (n : Nat) (room : c.top+2 < capacity) :
    Valid l (c1 l c) ∧ Valid l (c2 l c n) ∧ Valid l (c3 l c n) := by
  have h1 : Valid l (c1 l c) := next_valid 10 ctx (by omega)
  have h2 : Valid l (c2 l c n) := next_valid (n%10) h1 (by change c.top+1 < capacity; omega)
  exact ⟨h1,h2,next_valid 4294967295 h2 (by change c.top+1+1 < capacity; omega)⟩

theorem source_calls (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (nrInstalled : Generated.f_nr ∈ code)
    (smallInstalled : Generated.f_small ∈ code) (nleInstalled : Generated.f_nle ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {c : Cursor} {slot n : Nat}
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+2 < capacity) (a : Value) (ds : List Nat) (count first : Nat) :
    SourceCall Header.layout code 3 "nu" [DecimalDigits.integer 10]
      (frame c.state a ds slot count first) (.natObject c.state.nats.values.length)
      (frame (c1 l c).state a ds slot count first) ∧
    SourceCall Header.layout code 3 "nr"
      [.natObject slot,.natObject c.state.nats.values.length]
      (frame (c1 l c).state a ds slot count first)
      (.natObject (c1 l c).state.nats.values.length)
      (frame (c2 l c n).state a ds slot count first) ∧
    SourceCall Header.layout code 3 "small" [.natObject (c1 l c).state.nats.values.length]
      (frame (c2 l c n).state a ds slot count first) (unsigned32 (n%10))
      (frame (c3 l c n).state a ds slot count first) := by
  have cs := contexts ctx n room
  have nuRun := nu_call (n:=10) (input:=DecimalDigits.integer 10) code nuInstalled
    keepInstalled (PrintSPoolFrames.frame_context ctx a ds slot count first)
    (by omega) (by norm_num) rfl
  have ten : NatArena.Borrow (c1 l c).state.nats c.state.nats.values.length 10 :=
    next_borrow l c 10
  have old : NatArena.Borrow (c1 l c).state.nats slot n := preserves live
  have second := nr_call code nrInstalled keepInstalled
    (PrintSPoolFrames.frame_context cs.1 a ds slot count first)
    (by change c.top+1 < capacity; omega) old ten (by decide)
  have rem : NatArena.Borrow (c2 l c n).state.nats
      (c1 l c).state.nats.values.length (n%10) := next_borrow l (c1 l c) (n%10)
  have third := small_call code smallInstalled nuInstalled nleInstalled keepInstalled
    (PrintSPoolFrames.frame_context cs.2.1 a ds slot count first)
    (by change c.top+1+1 < capacity; omega) rem
    (show n%10 < 2^32 by omega)
  refine ⟨?_,?_,?_⟩
  · apply raise_once
    simpa only [frame_nats,PrintSPoolFrames.frame_binary ctx,c1,next] using nuRun
  · apply raise_once
    simpa only [frame_nats,PrintSPoolFrames.frame_binary cs.1,c2,next] using second
  · simpa only [frame_nats,PrintSPoolFrames.frame_binary cs.2.1,c3,next] using third

end ScopedIO.PrintSDigitCalls
