/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ConvertBoundSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals

theorem upper_zero_iff (data : Nat→Nat) (start : Nat) :
    allZero data start 4 2=true ↔ data (start+2)=0 ∧ data (start+3)=0 ∧ data (start+4)=0 ∧ data (start+5)=0 := by
  simp [allZero]

theorem converted_magnitude (data : Nat→Nat) (start : Nat)
    (digits : ∀k,k<6 → data (start+k)<base) :
    result data start=if FFT.Limbs.magnitude base 6 (fun k=>data (start+k))<base^2
      then FFT.Limbs.magnitude base 6 (fun k=>data (start+k)) else sentinel := by
  have lo := lower_lt digits
  have form : FFT.Limbs.magnitude base 6 (fun k=>data (start+k))=
      lower data start+base^2*data (start+2)+base^3*data (start+3)+base^4*data (start+4)+base^5*data (start+5) := by
    simp [FFT.Limbs.magnitude,Finset.sum_range_succ,lower]
    ring
  by_cases hz : allZero data start 4 2=true
  · obtain ⟨h2,h3,h4,h5⟩ := (upper_zero_iff data start).mp hz
    simp only [result,if_pos hz,form,h2,h3,h4,h5,Nat.mul_zero,Nat.add_zero,if_pos lo]
  · have notzero := (upper_zero_iff data start).not.mp hz
    have large : base^2≤FFT.Limbs.magnitude base 6 (fun k=>data (start+k)) := by
      rw [form]
      dsimp [base] at *
      omega
    simp only [result,if_neg hz,if_neg (Nat.not_lt.mpr large)]

def Correct {F : Type} (context : Context F) (before : State F)
    (object size start : Nat) (data : Nat→Nat) : Prop :=
  ∃after,Call context "convert_bound" [.pointer (wordPointer object start),.integer (integer64 6)] before
    (.value (.integer (integer64 (result data start)))) after ∧
    WordArrayRep after object size data ∧ MultiplyCall.CallerFrame before after [] ∧
    ∀anyResult anyAfter,Call context "convert_bound" [.pointer (wordPointer object start),.integer (integer64 6)] before anyResult anyAfter →
      anyResult=.value (.integer (integer64 (result data start))) ∧ anyAfter=after

theorem convert_bound_total {F : Type} (context : Context F)
    (selected : findFunction context.program "convert_bound"=some convert_bound_ast)
    (before : State F) (object size start : Nat) (data : Nat→Nat)
    (well : WellScoped before) (array : WordArrayRep before object size data)
    (bound : start+6≤size) (digits : ∀k,k<6 → data (start+k)<base) :
    Correct context before object size start data := by
  obtain ⟨after,called,rep,frame⟩ := convert_bound_call context selected before object size start data well array bound digits
  exact ⟨after,called,rep,frame,fun _ _ run=>returned_call_unique selected called run⟩

/-- Exact independent source-character syntax, every actual source Call,
unsigned range guards, untouched input/caller storage, and conversion of the
actual represented magnitude are all consumed. Final FFT/ANT linkage is a
separate application proof. -/
theorem source_convert_bound_total {F : Type} (context : Context F)
    (programPinned : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program)
    (before : State F) (object size start : Nat) (data : Nat→Nat)
    (well : WellScoped before) (array : WordArrayRep before object size data)
    (bound : start+6≤size) (digits : ∀k,k<6 → data (start+k)<base) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      Correct context before object size start data ∧
      result data start=if FFT.Limbs.magnitude base 6 (fun k=>data (start+k))<base^2
        then FFT.Limbs.magnitude base 6 (fun k=>data (start+k)) else sentinel := by
  have selected : findFunction context.program "convert_bound"=some convert_bound_ast := by
    rcases programPinned with h|h
    · rw [h];rfl
    · rw [h];rfl
  exact ⟨FFTRecursivePV.actual_source_syntax,FapFFTRecursivePV.actual_source_syntax,
    convert_bound_total context selected before object size start data well array bound digits,converted_magnitude data start digits⟩

#print axioms converted_magnitude
#print axioms convert_bound_total
#print axioms source_convert_bound_total
end RH080Next.FFTPV.ConvertBoundSource
