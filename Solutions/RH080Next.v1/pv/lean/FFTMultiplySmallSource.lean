/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMultiplySmallCall
import FFTRecursiveSource
import FapFFTRecursiveSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySmallSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs

def MultiplyContract {F : Type} (context : Context F) (before : State F)
    (object length start n factor : Nat) (old : Nat→Nat) : Prop:=
  ∃after,Call context "multiply_small" [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)] before
      (.value (.integer (integer64 (scaledRow old start factor n).2))) after ∧
    WordArrayRep after object length (currentData old start factor n) ∧ CallerFrame before after object ∧
    ∀after' result,Call context "multiply_small" [.pointer (wordPointer object start),.integer (integer64 n),.integer (integer64 factor)] before
      result after' → result=.value (.integer (integer64 (scaledRow old start factor n).2)) ∧ after'=after

theorem multiply_small_total {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some multiply_small_ast)
    (before : State F) (object length start n factor : Nat) (old : Nat→Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n≤length) (small : n≤6) (digits : ∀i,i<n → old (start+i)<base)
    (factorSmall : factor<base) :
    MultiplyContract context before object length start n factor old:=by
  obtain ⟨after,run,post,frame⟩:=multiply_small_call context selected before object length start n factor old
    well rep bound small digits factorSmall
  exact ⟨after,run,post,frame,fun after' result second=>returned_call_unique selected run second⟩

theorem processed_digit_bound (old : Nat→Nat) (start factor n i : Nat) (hi : i<n) :
    (scaledRow old start factor n).1 i<base:=by
  induction n with
  | zero=>omega
  | succ n ih=>
    rw [row_step]
    by_cases same : i=n
    · subst i;simpa using Nat.mod_lt (old (start+n)*factor+(scaledRow old start factor n).2) (by norm_num [base])
    · simpa only [Function.update_of_ne same] using ih (by omega)

theorem currentData_slice (old : Nat→Nat) (start factor n i : Nat) (hi : i<n) :
    currentData old start factor n (start+i)=(scaledRow old start factor n).1 i:=by
  simp [currentData,show start≤start+i ∧ start+i<start+n by omega]

theorem currentData_value (old : Nat→Nat) (start factor n : Nat) :
    magnitude base n (fun i=>currentData old start factor n (start+i))+
      (scaledRow old start factor n).2*base^n=factor*magnitude base n (fun i=>old (start+i)):=by
  have h:=final_value old start factor n
  simpa only [value_eq_magnitude,←Nat.cast_mul,←Nat.cast_add,←Nat.cast_pow,Int.natCast_inj] using h

def MultiplyCorrect {F : Type} (context : Context F) (before : State F)
    (object length start n factor : Nat) (old : Nat→Nat) : Prop:=
  MultiplyContract context before object length start n factor old ∧
    magnitude base n (fun i=>currentData old start factor n (start+i))+
      (scaledRow old start factor n).2*base^n=factor*magnitude base n (fun i=>old (start+i)) ∧
    (scaledRow old start factor n).2≤factor ∧
    ∀i,i<n → currentData old start factor n (start+i)<base

/-- Full mathematical integer multiplication and normalized source output,
with returned carry, source call termination and correctness of EVERY Call. -/
theorem multiply_small_value_total {F : Type} (context : Context F)
    (selected : findFunction context.program "multiply_small"=some multiply_small_ast)
    (before : State F) (object length start n factor : Nat) (old : Nat→Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n≤length) (small : n≤6) (digits : ∀i,i<n → old (start+i)<base)
    (factorSmall : factor<base) :
    MultiplyCorrect context before object length start n factor old:=by
  refine ⟨multiply_small_total context selected before object length start n factor old
    well rep bound small digits factorSmall,currentData_value old start factor n,
    row_carry_le old start factor n digits,?_⟩
  intro i hi
  rw [currentData_slice old start factor n i hi]
  exact processed_digit_bound old start factor n i hi

def sourceContext : Context Unit:=
  {program:=FFTRecursivePV.program,foreign:=fun _ _ _ _ _=>False,headerConstant:=fun _=>none,builtin:=fun _ _=>none}
def fapSourceContext : Context Unit:=
  {program:=FapFFTRecursivePV.program,foreign:=fun _ _ _ _ _=>False,headerConstant:=fun _=>none,builtin:=fun _ _=>none}

/-- Both actual original C sources are linked to the full generic helper
proof. This is a source-verified helper, not the whole FFT numerical theorem. -/
theorem source_multiply_small_total (before : State Unit) (object length start n factor : Nat) (old : Nat→Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n≤length) (small : n≤6) (digits : ∀i,i<n → old (start+i)<base)
    (factorSmall : factor<base) :
    Correspondence.SourceSyntaxCorresponds FFTRecursivePV.source FFTRecursivePV.program ∧
      MultiplyCorrect sourceContext before object length start n factor old:=
  ⟨FFTRecursivePV.actual_source_syntax,multiply_small_value_total sourceContext (by rfl)
    before object length start n factor old well rep bound small digits factorSmall⟩

theorem fap_source_multiply_small_total (before : State Unit) (object length start n factor : Nat) (old : Nat→Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n≤length) (small : n≤6) (digits : ∀i,i<n → old (start+i)<base)
    (factorSmall : factor<base) :
    Correspondence.SourceSyntaxCorresponds FapFFTRecursivePV.source FapFFTRecursivePV.program ∧
      MultiplyCorrect fapSourceContext before object length start n factor old:=
  ⟨FapFFTRecursivePV.actual_source_syntax,multiply_small_value_total fapSourceContext (by rfl)
    before object length start n factor old well rep bound small digits factorSmall⟩

#print axioms multiply_small_total
#print axioms multiply_small_value_total
#print axioms source_multiply_small_total
#print axioms fap_source_multiply_small_total
end RH080Next.FFTPV.MultiplySmallSource
