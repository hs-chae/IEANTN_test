/- Structural induction step for the actual subsequent printS while loop.
The smaller-case premise is discharged by strong induction, not exposed as
an application or mathematical premise in the eventual complete theorem. -/
import ScopedIO.PrintSTailPost

namespace ScopedIO.PrintSTailStep
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSIteration ScopedIO.PrintSTailPost
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

theorem extend (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (nrInstalled : Generated.f_nr ∈ code)
    (smallInstalled : Generated.f_small ∈ code) (nleInstalled : Generated.f_nle ∈ code)
    (ndInstalled : Generated.f_nd ∈ code) (nzInstalled : Generated.f_nz ∈ code)
    (neInstalled : Generated.f_ne ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    (l : PoolLayout) (a : Value) (n : Nat) (nonzero : n ≠ 0)
    (smaller : ∀ (c : Cursor) (slot : Nat) (ds : List Nat),
      Valid l c → NatArena.Borrow c.state.nats slot (n/10) →
      c.top+6*(Nat.digits 10 (n/10)).length+1 ≤ capacity →
      ds.length+(Nat.digits 10 (n/10)).length ≤ 1024 →
      ∃ final outputSlot es,Post code l c final a slot outputSlot (n/10) ds es)
    (c : Cursor) (slot : Nat) (ds : List Nat)
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+6*(Nat.digits 10 n).length+1 ≤ capacity)
    (prefixBound : ds.length+(Nat.digits 10 n).length ≤ 1024) :
    ∃ final outputSlot es,Post code l c final a slot outputSlot n ds es := by
  have digitsEq := Nat.digits_eq_cons_digits_div (show 1 < 10 by decide) nonzero
  have digitsLength : (Nat.digits 10 n).length = (Nat.digits 10 (n/10)).length+1 := by
    rw [digitsEq]
    rfl
  have roomZero : c.top < capacity := by omega
  let guardCursor := next l c 0
  let middle := finalCursor l guardCursor n
  let middleSlot := finalSlot l guardCursor n
  have guardCtx : Valid l guardCursor := next_valid 0 ctx roomZero
  have guardLive : NatArena.Borrow guardCursor.state.nats slot n := PoolCursor.preserves live
  have guardTop : guardCursor.top = c.top+1 := rfl
  have guardSize : guardCursor.state.nats.values.length = c.state.nats.values.length+1 :=
    PoolCursor.size l c 0
  have bodyRoom : guardCursor.top+4 < capacity := by omega
  have shortPrefix : ds.length < 1024 := by omega
  obtain ⟨headEvents,headCounts,headRun⟩ := PrintSStepEvents.events code nuInstalled nrInstalled
    smallInstalled nleInstalled ndInstalled keepInstalled guardCtx guardLive bodyRoom a ds 0 shortPrefix
  have middleCtx : Valid l middle := PrintSGenerationEffects.valid guardCtx n (by omega)
  have middleLive : NatArena.Borrow middle.state.nats middleSlot (n/10) :=
    PrintSGenerationEffects.quotient l guardCursor n
  have middleTop : middle.top = guardCursor.top+5 := PrintSGenerationEffects.top l guardCursor n
  have middleSize : middle.state.nats.values.length = guardCursor.state.nats.values.length+5 :=
    PrintSGenerationEffects.size l guardCursor n
  have tailRoom : middle.top+6*(Nat.digits 10 (n/10)).length+1 ≤ capacity := by omega
  have tailPrefix : (ds++[n%10]).length+(Nat.digits 10 (n/10)).length ≤ 1024 := by
    simp only [List.length_append,List.length_singleton]
    omega
  obtain ⟨final,outputSlot,tailEvents,post⟩ := smaller middle middleSlot (ds++[n%10])
    middleCtx middleLive tailRoom tailPrefix
  have nzRun := PrintSCondition.actual_nz code nzInstalled nuInstalled neInstalled keepInstalled
    ctx live roomZero a ds ds.length
  let ev : CallEvents.Event Header.layout code 3 :=
    ⟨"nz",[.natObject slot],frame c.state a ds slot ds.length 0,PrimitiveCalls.u32 (n==0),
      frame guardCursor.state a ds slot ds.length 0,nzRun⟩
  refine ⟨final,outputSlot,[ev]++headEvents++tailEvents,post.valid,post.live,?_,?_,?_⟩
  · obtain ⟨values,equal,length⟩ := post.effects
    refine ⟨0::([10,n%10,4294967295,10,n/10]++values),?_,?_⟩
    · rw [equal,CursorFrames.advance,CursorSingleFrames.advance_append]
      rfl
    · simp only [List.length_cons,List.length_append,List.length_singleton,List.length_nil]
      omega
  · have zeroCounts : CallEvents.counts [ev] = List.range' c.state.nats.values.length 1 := by
      simp [CallEvents.counts,ev,PrintSDigitCalls.frame_nats,List.range']
    have joined : CallEvents.counts ([ev]++headEvents++tailEvents) =
        List.range' c.state.nats.values.length (1+5+(6*(Nat.digits 10 (n/10)).length+1)) := by
      calc
        _ = CallEvents.counts [ev]++CallEvents.counts headEvents++CallEvents.counts tailEvents := by
          simp only [CallEvents.counts,List.map_append]
        _ = List.range' c.state.nats.values.length 1 ++
            List.range' (c.state.nats.values.length+1) 5 ++
            List.range' ((c.state.nats.values.length+1)+5)
              (6*(Nat.digits 10 (n/10)).length+1) := by
          rw [zeroCounts,headCounts,post.counts,middleSize,guardSize]
        _ = _ := by rw [List.range'_append_1,List.range'_append_1]
    have totalEq : 1+5+(6*(Nat.digits 10 (n/10)).length+1) =
        6*(Nat.digits 10 n).length+1 := by omega
    rw [totalEq] at joined
    exact joined
  · intro service answers
    have answer := answers ev (by simp)
    have headAnswers : Answers service headEvents := by
      intro e member
      exact answers e (List.mem_append_left _ (List.mem_append_right _ member))
    have tailAnswers : Answers service tailEvents := by
      intro e member
      exact answers e (List.mem_append_right _ member)
    have check := PrintSCondition.subsequent service l c a ds slot ds.length n answer
    have nzTrue : decide (n ≠ 0) = true := by simp [nonzero]
    rw [nzTrue] at check
    have tailRun := post.source service tailAnswers
    simp only [List.length_append,List.length_singleton] at tailRun
    have run := Loops.WhileRun.next (truth:=truth) check rfl
      (headRun service headAnswers) tailRun
    have countEq : ds.length+1+(Nat.digits 10 (n/10)).length =
        ds.length+(Nat.digits 10 n).length := by omega
    have appendEq : (ds++[n%10])++Nat.digits 10 (n/10) = ds++Nat.digits 10 n := by
      rw [digitsEq,List.append_assoc]
      rfl
    rw [appendEq,countEq] at run
    exact run

end ScopedIO.PrintSTailStep
