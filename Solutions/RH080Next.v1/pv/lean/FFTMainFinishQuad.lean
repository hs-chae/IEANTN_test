/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainFinishBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainFinish
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource
open MainRootBirth

def workUpdate (data : MainAllocation.Role → Nat → Nat) (workData : Nat → Nat) : MainAllocation.Role → Nat → Nat
  | .work=>workData | .data=>data .data | .twiddle=>data .twiddle | .output=>data .output

theorem magnitudeAt_congr (a b : Nat → Nat) (start : Nat)
    (same : ∀k,k<6 → a (start+k)=b (start+k)) : magnitudeAt a start=magnitudeAt b start := by
  unfold magnitudeAt FFT.Limbs.magnitude
  apply Finset.sum_congr rfl
  intro k member
  exact congrArg (fun v=>v*1000000000^k) (same k (Finset.mem_range.mp member))

/-- The actual source's three upward chord divisions from the real end-of-quad
state, retaining every main slot and all four live application arrays. -/
theorem normalized_quad {F : Type} (context : Context F) (fap : Bool)
    (programPinned : context.program=NormalizeSource.profileProgram fap)
    {before : State F} {n nId owner base status : Nat}
    {objects ids : MainAllocation.Role → Nat} {data : MainAllocation.Role → Nat → Nat}
    (locals : FullMainLocals before n nId owner objects ids base status)
    (well : WellScoped before) (scope : before.scope=owner)
    (different : Function.Injective objects)
    (arrays : ∀r,WordArrayRep before (objects r) (MainAllocation.length n r) (data r))
    (positive : 0<n) (small : n<1000000000)
    (totalDigits : ∀k,k<6 → data .work (192+k)<1000000000)
    (quadDigits : ∀k,k<6 → data .work (208+k)<1000000000) :
    ∃after workData,NormalSegment context before NormalizeSource.quadStatements after ∧
      FullMainLocals after n nId owner objects ids base status ∧
      after.scope=owner ∧
      (∀r,WordArrayRep after (objects r) (MainAllocation.length n r) (workUpdate data workData r)) ∧
      Frame before.nextObject before after [objects .work] ∧
      magnitudeAt workData 192=magnitudeAt (data .work) 192 ∧
      magnitudeAt workData 208=NormalizeSource.quadValue (magnitudeAt (data .work) 208) n ∧
      (∀k,k<6 → workData (192+k)<1000000000) ∧
      (∀k,k<6 → workData (208+k)<1000000000) := by
  have params:=normalize_locals locals
  have work : WordArrayRep before (objects .work) 512 (data .work):=arrays .work
  have separate : ∀v,objects .work≠normalizeIds nId ids base status v :=
    fun v=>MultiplyParameters.array_slot_different work (params.slots v)
  obtain ⟨_,_,_,after,workData,run,rep,postParams,frame,value,normalized,outside,every⟩:=
    NormalizeSource.source_quad_execution context fap programPinned params work separate well positive small quadDigits
  have postLocals : FullMainLocals after n nId owner objects ids base status := by
    apply MainTransport.locals_of_frame well locals frame.frame
    · intro v;rw [frame.environment]
    · intro v
      have ne:=MultiplyParameters.array_slot_different work (locals.slots v)
      simpa only [List.mem_singleton] using ne.symm
  have postArrays : ∀r,WordArrayRep after (objects r) (MainAllocation.length n r) (workUpdate data workData r) := by
    intro r
    cases r with
    | work=>exact rep
    | data | twiddle | output=>
      apply MainTransport.array_of_frame well (arrays _) frame.frame
      simp only [List.mem_singleton]
      intro eq
      have impossible:=different eq
      cases impossible
  refine ⟨after,workData,⟨run,every⟩,postLocals,frame.scope.trans scope,postArrays,frame.frame,?_,value,?_,normalized⟩
  · apply magnitudeAt_congr
    intro k hk
    exact outside _ (Or.inl (by omega))
  · intro k hk
    rw [outside _ (Or.inl (by omega))]
    exact totalDigits k hk

#print axioms magnitudeAt_congr
#print axioms normalized_quad
end RH080Next.FFTPV.MainFinish
