/- Complete original printS generation while, including its forced first
iteration for zero. The buffer, quotient and allocation trace are produced
by actual source calls; no precomputed digit buffer is assumed. -/
import ScopedIO.PrintSTailLoop

namespace ScopedIO.PrintSGeneration
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
open ScopedC.NatWrapperCalls ScopedC.PoolCursor ScopedIO.PrintSFrames
open ScopedIO.PrintSIteration
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

structure Post (code : List Function) (l : PoolLayout) (start final : Cursor)
    (a : Value) (inputSlot outputSlot n : Nat) (ds : List Nat)
    (events : List (CallEvents.Event Header.layout code 3)) : Prop where
  valid : Valid l final
  live : NatArena.Borrow final.state.nats outputSlot 0
  effects : ∃ values : List Nat, final = CursorFrames.advance l start values ∧
    values.length = 6*(PrintSDecimalModel.digits n).length
  counts : CallEvents.counts events =
    List.range' start.state.nats.values.length (6*(PrintSDecimalModel.digits n).length)
  source : ∀ service,Answers service events →
    Loops.WhileRun (Eval Header.layout service) (Declare Header.layout service)
      truth Scope PrintSCondition.expression body
      (frame start.state a ds inputSlot ds.length 1)
      (.continuing (frame final.state a (ds++PrintSDecimalModel.digits n) outputSlot
        (ds.length+(PrintSDecimalModel.digits n).length) 0))

theorem loop_exists (code : List Function)
    (nuInstalled : Generated.f_nu ∈ code) (nrInstalled : Generated.f_nr ∈ code)
    (smallInstalled : Generated.f_small ∈ code) (nleInstalled : Generated.f_nle ∈ code)
    (ndInstalled : Generated.f_nd ∈ code) (nzInstalled : Generated.f_nz ∈ code)
    (neInstalled : Generated.f_ne ∈ code) (keepInstalled : Generated.f_keep ∈ code)
    (l : PoolLayout) (a : Value) (n : Nat) (c : Cursor) (slot : Nat) (ds : List Nat)
    (ctx : Valid l c) (live : NatArena.Borrow c.state.nats slot n)
    (room : c.top+6*(PrintSDecimalModel.digits n).length ≤ capacity)
    (prefixBound : ds.length+(PrintSDecimalModel.digits n).length ≤ 1024) :
    ∃ final outputSlot es,Post code l c final a slot outputSlot n ds es := by
  have digitsEq := PrintSDecimalModel.digits_step n
  have digitsLength : (PrintSDecimalModel.digits n).length =
      (Nat.digits 10 (n/10)).length+1 := by rw [digitsEq]; rfl
  have shortPrefix : ds.length < 1024 := by omega
  have bodyRoom : c.top+4 < capacity := by omega
  obtain ⟨headEvents,headCounts,headRun⟩ := PrintSStepEvents.events code nuInstalled nrInstalled
    smallInstalled nleInstalled ndInstalled keepInstalled ctx live bodyRoom a ds 1 shortPrefix
  let middle := finalCursor l c n
  let middleSlot := finalSlot l c n
  have middleCtx : Valid l middle := PrintSGenerationEffects.valid ctx n (by omega)
  have middleLive : NatArena.Borrow middle.state.nats middleSlot (n/10) :=
    PrintSGenerationEffects.quotient l c n
  have middleTop : middle.top = c.top+5 := PrintSGenerationEffects.top l c n
  have middleSize : middle.state.nats.values.length = c.state.nats.values.length+5 :=
    PrintSGenerationEffects.size l c n
  have tailRoom : middle.top+6*(Nat.digits 10 (n/10)).length+1 ≤ capacity := by omega
  have tailPrefix : (ds++[n%10]).length+(Nat.digits 10 (n/10)).length ≤ 1024 := by
    simp only [List.length_append,List.length_singleton]
    omega
  obtain ⟨final,outputSlot,tailEvents,post⟩ := PrintSTailLoop.loop_exists code nuInstalled nrInstalled
    smallInstalled nleInstalled ndInstalled nzInstalled neInstalled keepInstalled l a (n/10)
    middle middleSlot (ds++[n%10]) middleCtx middleLive tailRoom tailPrefix
  refine ⟨final,outputSlot,headEvents++tailEvents,post.valid,post.live,?_,?_,?_⟩
  · obtain ⟨values,equal,length⟩ := post.effects
    refine ⟨[10,n%10,4294967295,10,n/10]++values,?_,?_⟩
    · rw [equal,CursorSingleFrames.advance_append]
      rfl
    · simp only [List.length_append,List.length_cons,List.length_nil]
      omega
  · have joined : CallEvents.counts (headEvents++tailEvents) =
        List.range' c.state.nats.values.length (5+(6*(Nat.digits 10 (n/10)).length+1)) := by
      calc
        _ = CallEvents.counts headEvents++CallEvents.counts tailEvents := by
          simp only [CallEvents.counts,List.map_append]
        _ = List.range' c.state.nats.values.length 5 ++
            List.range' (c.state.nats.values.length+5) (6*(Nat.digits 10 (n/10)).length+1) := by
          rw [headCounts,post.counts,middleSize]
        _ = _ := List.range'_append_1
    have totalEq : 5+(6*(Nat.digits 10 (n/10)).length+1) =
        6*(PrintSDecimalModel.digits n).length := by omega
    rw [totalEq] at joined
    exact joined
  · intro service answers
    have headAnswers : Answers service headEvents := fun e member =>
      answers e (List.mem_append_left _ member)
    have tailAnswers : Answers service tailEvents := fun e member =>
      answers e (List.mem_append_right _ member)
    have tailRun := post.source service tailAnswers
    simp only [List.length_append,List.length_singleton] at tailRun
    have run := Loops.WhileRun.next (truth:=truth)
      (PrintSCondition.forced service c.state a ds slot ds.length) rfl
      (headRun service headAnswers) tailRun
    have appendEq : (ds++[n%10])++Nat.digits 10 (n/10) = ds++PrintSDecimalModel.digits n := by
      rw [digitsEq,List.append_assoc]
      rfl
    have countEq : ds.length+1+(Nat.digits 10 (n/10)).length =
        ds.length+(PrintSDecimalModel.digits n).length := by omega
    rw [appendEq,countEq] at run
    exact run

end ScopedIO.PrintSGeneration
