/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTIncrementCall
import ExplicitFFTCompareSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.IncrementSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

def IncrementContract {F : Type} (context : Context F) (before : State F)
    (object length start n : Nat) (old : Nat → Nat) : Prop :=
  ∃after,Call context "increment_words" [.pointer (wordPointer object start),.integer (integer64 n)] before
      (.value (.integer (integer64 (incrementDigits base (fun k=>old (start+k)) n).2))) after ∧
    WordArrayRep after object length (currentData old start n) ∧ CallerFrame before after object ∧
    ∀after' result,Call context "increment_words" [.pointer (wordPointer object start),.integer (integer64 n)] before
      result after' → result=.value (.integer (integer64 (incrementDigits base (fun k=>old (start+k)) n).2)) ∧ after'=after

theorem increment_words_total {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (object length start n : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) :
    IncrementContract context before object length start n old := by
  obtain ⟨after,run,post,frame⟩:=increment_words_call context selected before object length start n old well rep bound small digits
  exact ⟨after,run,post,frame,fun after' result second=>returned_call_unique selected run second⟩

theorem currentData_slice (old : Nat → Nat) (start n i : Nat) (hi : i < n) :
    currentData old start n (start+i)=(incrementDigits base (fun k=>old (start+k)) n).1 i := by
  simp [currentData,show start ≤ start+i ∧ start+i < start+n by omega]

theorem currentData_value (old : Nat → Nat) (start n : Nat) :
    magnitude base n (fun i=>currentData old start n (start+i))+
      (incrementDigits base (fun k=>old (start+k)) n).2*base^n=
        magnitude base n (fun i=>old (start+i))+1 := by
  have eq : magnitude base n (fun i=>currentData old start n (start+i))=
      magnitude base n (incrementDigits base (fun k=>old (start+k)) n).1 := by
    apply Finset.sum_congr rfl
    intro i hi
    change currentData old start n (start+i)*base^i=_
    rw [currentData_slice old start n i (Finset.mem_range.mp hi)]
  rw [eq]
  exact incrementDigits_value base n (fun k=>old (start+k))

def IncrementCorrect {F : Type} (context : Context F) (before : State F)
    (object length start n : Nat) (old : Nat → Nat) : Prop :=
    IncrementContract context before object length start n old ∧
      magnitude base n (fun i=>currentData old start n (start+i))+
        (incrementDigits base (fun k=>old (start+k)) n).2*base^n=
          magnitude base n (fun i=>old (start+i))+1 ∧
      (incrementDigits base (fun k=>old (start+k)) n).2 ≤ 1 ∧
      ∀i < n,currentData old start n (start+i) < base

/-- This proves positional-integer correctness, rather than just matching a
source-shaped recurrence; normalized words and the overflow carry are exact. -/
theorem increment_words_value_total {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (object length start n : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) :
    IncrementCorrect context before object length start n old := by
  have bounds:=incrementDigits_bounds base n (by norm_num [base]) (fun k=>old (start+k)) digits
  exact ⟨increment_words_total context selected before object length start n old well rep bound small digits,
    currentData_value old start n,bounds.1,fun i hi=>by rw [currentData_slice old start n i hi]; exact bounds.2 i hi⟩

/-- Actual original w4 source syntax and universal application-source helper
correctness, with caller-supplied typed data and no claimed whole-FFT output. -/
theorem source_increment_words_total (before : State Unit) (object length start n : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧
      IncrementCorrect CompareSource.sourceContext before object length start n old :=
  ⟨RH080Next.FFTPV.actual_source_syntax,
    increment_words_value_total CompareSource.sourceContext (by rfl) before object length start n old well rep bound small digits⟩

theorem fap_source_increment_words_total (before : State Unit) (object length start n : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧
      IncrementCorrect CompareSource.fapSourceContext before object length start n old :=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,
    increment_words_value_total CompareSource.fapSourceContext (by rfl) before object length start n old well rep bound small digits⟩

#print axioms increment_words_total
#print axioms increment_words_value_total
#print axioms source_increment_words_total
#print axioms fap_source_increment_words_total
end RH080Next.FFTPV.IncrementSource
