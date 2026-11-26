/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem quotient_value (old : Nat → Nat) (start n d : Nat) (hd : 0 < d) :
    magnitude base n (fun i=>currentData old start n d 0 (start+i))=
      magnitude base n (fun i=>old (start+i))/d ∧
    (division old start n d 0).2=magnitude base n (fun i=>old (start+i))%d := by
  have eq : magnitude base n (fun i=>currentData old start n d 0 (start+i))=
      magnitude base n (divideDigits base d (fun i=>old (start+i)) n).1 := by
    apply Finset.sum_congr rfl
    intro i hi
    change currentData old start n d 0 (start+i)*base^i=_
    rw [currentData_slice old start n d i (Finset.mem_range.mp hi)]
  rw [eq]
  exact divideDigits_quotient_remainder base d n hd _

/-- Exact encoded floor or ceiling quotient, including n=0 and zero data. -/
theorem roundedData_value (old : Nat → Nat) (start n d ceiling : Nat) (hd : 0 < d)
    (digits : ∀i < n,old (start+i) < base) :
    magnitude base n (fun i=>roundedData old start n d ceiling (start+i))=
      if 0 < ceiling then ceilQuotient (magnitude base n (fun i=>old (start+i))) d
      else magnitude base n (fun i=>old (start+i))/d := by
  obtain ⟨qv,rv⟩:=quotient_value old start n d hd
  by_cases hc : 0 < ceiling
  · by_cases hr : 0 < (division old start n d 0).2
    · have original_lt:=magnitude_lt base n (by norm_num [base]) (fun i=>old (start+i)) digits
      have exactValue:=currentData_value old start n d
      have small : magnitude base n (fun i=>currentData old start n d 0 (start+i))+1 < base^n := by
        have hm:=Nat.mul_le_mul_right (magnitude base n (fun i=>currentData old start n d 0 (start+i)))
          (show 1 ≤ d by omega)
        nlinarith
      have carryZero:=(incrementDigits_no_overflow base n (by norm_num [base]) _ small).1
      have inc:=IncrementSource.currentData_value (currentData old start n d 0) start n
      rw [carryZero,zero_mul,add_zero,qv] at inc
      have remNe : magnitude base n (fun i=>old (start+i))%d≠0:=by rw [←rv]; omega
      simpa [roundedData,hc,hr,ceilQuotient,remNe] using inc
    · have remZero : magnitude base n (fun i=>old (start+i))%d=0:=by rw [←rv]; omega
      simpa [roundedData,hc,hr,ceilQuotient,remZero] using qv
  · simpa [roundedData,hc] using qv

theorem roundedData_digits (old : Nat → Nat) (start n d ceiling : Nat) (hd : 0 < d)
    (digits : ∀i < n,old (start+i) < base) :
    ∀i < n,roundedData old start n d ceiling (start+i) < base := by
  have quotient : ∀i < n,currentData old start n d 0 (start+i) < base := by
    intro i hi
    rw [currentData_slice old start n d i hi]
    exact divideDigits_bounds base d n (by norm_num [base]) hd _ digits i hi
  intro i hi
  by_cases positive : 0 < ceiling ∧ 0 < (division old start n d 0).2
  · rw [roundedData,if_pos positive,IncrementSource.currentData_slice _ start n i hi]
    exact (incrementDigits_bounds base n (by norm_num [base]) _ quotient).2 i hi
  · simpa only [roundedData,if_neg positive] using quotient i hi

theorem roundedData_outside (old : Nat → Nat) (start n d ceiling i : Nat)
    (outside : ¬(start ≤ i ∧ i < start+n)) : roundedData old start n d ceiling i=old i := by
  by_cases positive : 0 < ceiling ∧ 0 < (division old start n d 0).2
  · simp [roundedData,positive,IncrementSource.currentData,currentData,outside]
  · simp [roundedData,positive,currentData,outside]

def DivideContract {F : Type} (context : Context F) (before : State F)
    (object length start n d ceiling : Nat) (old : Nat → Nat) : Prop :=
  ∃after,Call context "divide_small" [.pointer (wordPointer object start),.integer (integer64 n),
      .integer (integer64 d),.integer (integer64 ceiling)] before (.value (.integer (integer64 0))) after ∧
    WordArrayRep after object length (roundedData old start n d ceiling) ∧
    IncrementSource.FullCallerFrame before after object ∧
    ∀after' result,Call context "divide_small" [.pointer (wordPointer object start),.integer (integer64 n),
      .integer (integer64 d),.integer (integer64 ceiling)] before result after' →
        result=.value (.integer (integer64 0)) ∧ after'=after

def DivideCorrect {F : Type} (context : Context F) (before : State F)
    (object length start n d ceiling : Nat) (old : Nat → Nat) : Prop :=
  DivideContract context before object length start n d ceiling old ∧
    magnitude base n (fun i=>roundedData old start n d ceiling (start+i))=
      (if 0 < ceiling then ceilQuotient (magnitude base n (fun i=>old (start+i))) d
       else magnitude base n (fun i=>old (start+i))/d) ∧
    (∀i < n,roundedData old start n d ceiling (start+i) < base) ∧
    ∀i,¬(start ≤ i ∧ i < start+n) → roundedData old start n d ceiling i=old i

theorem divide_small_total {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (before : State F) (object length start n d ceiling : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base)
    (hd : 0 < d) (hdb : d < base) (hceil : ceiling ≤ 1) :
    DivideCorrect context before object length start n d ceiling old := by
  obtain ⟨after,run,post,frame⟩:=divide_small_call context selected incrementSelected before object length start n d ceiling old
    well rep bound small digits hd hdb hceil
  exact ⟨⟨after,run,post,frame,fun after' result second=>returned_call_unique selected incrementSelected run second⟩,
    roundedData_value old start n d ceiling hd digits,roundedData_digits old start n d ceiling hd digits,
    roundedData_outside old start n d ceiling⟩

/-- Both preserved actual C files consume their independently checked syntax,
their complete universal call contract and exact integer division semantics. -/
theorem source_divide_small_total (before : State Unit) (object length start n d ceiling : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base)
    (hd : 0 < d) (hdb : d < base) (hceil : ceiling ≤ 1) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FFTPV.source RH080Next.FFTPV.program ∧
      DivideCorrect CompareSource.sourceContext before object length start n d ceiling old :=
  ⟨RH080Next.FFTPV.actual_source_syntax,divide_small_total CompareSource.sourceContext (by rfl) (by rfl)
    before object length start n d ceiling old well rep bound small digits hd hdb hceil⟩

theorem fap_source_divide_small_total (before : State Unit) (object length start n d ceiling : Nat) (old : Nat → Nat)
    (well : WellScoped before) (rep : WordArrayRep before object length old)
    (bound : start+n ≤ length) (small : n ≤ 6) (digits : ∀i < n,old (start+i) < base)
    (hd : 0 < d) (hdb : d < base) (hceil : ceiling ≤ 1) :
    Correspondence.SourceSyntaxCorresponds RH080Next.FapFFTPV.source RH080Next.FapFFTPV.program ∧
      DivideCorrect CompareSource.fapSourceContext before object length start n d ceiling old :=
  ⟨RH080Next.FapFFTPV.actual_source_syntax,divide_small_total CompareSource.fapSourceContext (by rfl) (by rfl)
    before object length start n d ceiling old well rep bound small digits hd hdb hceil⟩

#print axioms roundedData_value
#print axioms divide_small_total
#print axioms source_divide_small_total
#print axioms fap_source_divide_small_total
end RH080Next.FFTPV.DivideSource
