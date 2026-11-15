/- Proof-backed actual source events for the complete original digit body.
The chronological allocation counts make the eventual finite service unique. -/
import ScopedIO.PrintSIteration

namespace ScopedIO.PrintSStepEvents
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSIteration
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem events (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (nrInstalled : Generated.f_nr ∈ code)
    (smallInstalled : Generated.f_small ∈ code) (nleInstalled : Generated.f_nle ∈ code)
    (ndInstalled : Generated.f_nd ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {c : Cursor} {slot n : Nat}
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+4 < capacity) (a : Value) (ds : List Nat) (first : Nat)
    (prefixBound : ds.length < 1024) :
    ∃ es : List (CallEvents.Event Header.layout code 3),
      CallEvents.counts es = List.range' c.state.nats.values.length 5 ∧
      ∀ service,Answers service es →
        Run Header.layout service body (frame c.state a ds slot ds.length first)
          (.continuing (frame (finalCursor l c n).state a
            (ds++[n%10]) (finalSlot l c n) (ds.length+1) 0)) := by
  have digit := PrintSDigitCalls.source_calls code nuInstalled nrInstalled smallInstalled
    nleInstalled keepInstalled ctx live (show c.top+2 < capacity by omega) a ds ds.length 0
  have middleCtx := (PrintSDigitCalls.contexts ctx n (show c.top+2 < capacity by omega)).2.2
  have live1 : NatArena.Borrow (PrintSDigitCalls.c1 l c).state.nats slot n := preserves live
  have live2 : NatArena.Borrow (PrintSDigitCalls.c2 l c n).state.nats slot n := preserves live1
  have live3 : NatArena.Borrow (PrintSDigitCalls.c3 l c n).state.nats slot n := preserves live2
  have division := PrintSDivision.source_calls code nuInstalled ndInstalled keepInstalled
    middleCtx live3 (by change c.top+1+1+1+1 < capacity; omega)
    a (ds++[n%10]) (ds.length+1) 0
  let e0 : CallEvents.Event Header.layout code 3 :=
    ⟨"nu",[DecimalDigits.integer 10],frame c.state a ds slot ds.length 0,
      .natObject c.state.nats.values.length,
      frame (PrintSDigitCalls.c1 l c).state a ds slot ds.length 0,digit.1⟩
  let e1 : CallEvents.Event Header.layout code 3 :=
    ⟨"nr",[.natObject slot,.natObject c.state.nats.values.length],
      frame (PrintSDigitCalls.c1 l c).state a ds slot ds.length 0,
      .natObject (PrintSDigitCalls.c1 l c).state.nats.values.length,
      frame (PrintSDigitCalls.c2 l c n).state a ds slot ds.length 0,digit.2.1⟩
  let e2 : CallEvents.Event Header.layout code 3 :=
    ⟨"small",[.natObject (PrintSDigitCalls.c1 l c).state.nats.values.length],
      frame (PrintSDigitCalls.c2 l c n).state a ds slot ds.length 0,unsigned32 (n%10),
      frame (PrintSDigitCalls.c3 l c n).state a ds slot ds.length 0,digit.2.2⟩
  let e3 : CallEvents.Event Header.layout code 3 :=
    ⟨"nu",[DecimalDigits.integer 10],
      frame (PrintSDigitCalls.c3 l c n).state a (ds++[n%10]) slot (ds.length+1) 0,
      .natObject (PrintSDigitCalls.c3 l c n).state.nats.values.length,
      frame (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state a
        (ds++[n%10]) slot (ds.length+1) 0,division.1⟩
  let e4 : CallEvents.Event Header.layout code 3 :=
    ⟨"nd",[.natObject slot,.natObject (PrintSDigitCalls.c3 l c n).state.nats.values.length],
      frame (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state a
        (ds++[n%10]) slot (ds.length+1) 0,.natObject (finalSlot l c n),
      frame (finalCursor l c n).state a (ds++[n%10]) slot (ds.length+1) 0,division.2⟩
  refine ⟨[e0,e1,e2,e3,e4],?_,?_⟩
  · have s1 := size l c 10
    have s2 := size l (PrintSDigitCalls.c1 l c) (n%10)
    have s3 := size l (PrintSDigitCalls.c2 l c n) 4294967295
    have s4 := size l (PrintSDigitCalls.c3 l c n) 10
    change [c.state.nats.values.length,(PrintSDigitCalls.c1 l c).state.nats.values.length,
      (PrintSDigitCalls.c2 l c n).state.nats.values.length,
      (PrintSDigitCalls.c3 l c n).state.nats.values.length,
      (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state.nats.values.length] = _
    change (PrintSDigitCalls.c1 l c).state.nats.values.length = c.state.nats.values.length+1 at s1
    change (PrintSDigitCalls.c2 l c n).state.nats.values.length =
      (PrintSDigitCalls.c1 l c).state.nats.values.length+1 at s2
    change (PrintSDigitCalls.c3 l c n).state.nats.values.length =
      (PrintSDigitCalls.c2 l c n).state.nats.values.length+1 at s3
    change (PrintSDivision.q1 l (PrintSDigitCalls.c3 l c n)).state.nats.values.length =
      (PrintSDigitCalls.c3 l c n).state.nats.values.length+1 at s4
    rw [s4,s3,s2,s1]
    simp [List.range',Nat.add_assoc]
  · intro service answers
    exact body_run service l c a ds slot first n prefixBound
      (answers e0 (by simp)) (answers e1 (by simp)) (answers e2 (by simp))
      (answers e3 (by simp)) (answers e4 (by simp))

end ScopedIO.PrintSStepEvents
