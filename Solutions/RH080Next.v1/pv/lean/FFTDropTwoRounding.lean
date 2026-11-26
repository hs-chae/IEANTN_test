/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTDropTwoClear
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DropTwoSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

def roundData (old : Nat→Nat) (start : Nat) : Nat→Nat:=
  if lost old start=0 then dropped old start else IncrementSource.currentData (dropped old start) start 6

theorem increment_status_zero {old : Nat→Nat} {start : Nat} (digits : ∀k,k<6 → old (start+k)<base) :
    (FFT.Limbs.incrementDigits base (fun k=>dropped old start (start+k)) 6).2=0:=
  (FFT.Limbs.incrementDigits_no_overflow base 6 (by norm_num [base]) _ (dropped_capacity digits)).1

private theorem increment_value_zero (data : Nat→Nat) (start n : Nat)
    (zero : (FFT.Limbs.incrementDigits IncrementSource.base (fun k=>data (start+k)) n).2=0) :
    FFT.Limbs.magnitude IncrementSource.base n (fun k=>IncrementSource.currentData data start n (start+k))=
      FFT.Limbs.magnitude IncrementSource.base n (fun k=>data (start+k))+1 := by
  have value:=IncrementSource.currentData_value data start n
  rw [zero,Nat.zero_mul,Nat.add_zero] at value
  exact value

private theorem generic_round_value (data : Nat→Nat) (start n : Nat) (test : Prop) [Decidable test]
    (zero : (FFT.Limbs.incrementDigits IncrementSource.base (fun k=>data (start+k)) n).2=0) :
    FFT.Limbs.magnitude IncrementSource.base n
      (fun k=>(if test then data else IncrementSource.currentData data start n) (start+k))=
      FFT.Limbs.magnitude IncrementSource.base n (fun k=>data (start+k))+(if test then 0 else 1) := by
  by_cases h : test
  · simp only [if_pos h,Nat.add_zero]
  · simpa only [if_neg h] using increment_value_zero data start n zero

theorem roundData_magnitude {old : Nat→Nat} {start : Nat} (digits : ∀k,k<6 → old (start+k)<base) :
    FFT.Limbs.magnitude base 6 (fun k=>roundData old start (start+k))=
      FFT.Limbs.ceilQuotient (FFT.Limbs.magnitude base 6 (fun k=>old (start+k))) (base^2) := by
  have value:=generic_round_value (dropped old start) start 6 (lost old start=0) (increment_status_zero digits)
  have indicator : (if lost old start=0 then 0 else 1)=
      (if FFT.Limbs.magnitude base 6 (fun k=>old (start+k))%base^2=0 then 0 else 1) := by
    by_cases hz : lost old start=0
    · simp only [if_pos hz,if_pos ((lost_zero_iff_remainder digits).mp hz)]
    · simp only [if_neg hz,if_neg (fun rem=>hz ((lost_zero_iff_remainder digits).mpr rem))]
  exact value.trans (congrArg₂ (·+·) (dropped_magnitude digits) indicator)

def roundingTest : Expr:=.binary .gt (.variable "lost") (.literal (.integer 0 "ULL"))
def arguments : List Expr:=[.variable "total",.literal (.integer 6 "ULL")]
def incrementStmt : Stmt:=StatusCall.statement "increment_words" arguments
def roundingBranch : Stmt:=.ite roundingTest (.block [incrementStmt]) none

theorem actual_rounding : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[31]?=some roundingBranch:=by rfl

private theorem generic_round_normalized (data : Nat→Nat) (start n : Nat) (test : Prop) [Decidable test]
    (digits : ∀k,k<n → data (start+k)<IncrementSource.base) :
    ∀k,k<n → (if test then data else IncrementSource.currentData data start n) (start+k)<IncrementSource.base := by
  intro k hk
  by_cases h : test
  · simpa only [if_pos h] using digits k hk
  · simp only [if_neg h]
    rw [IncrementSource.currentData_slice data start n k hk]
    exact (FFT.Limbs.incrementDigits_bounds IncrementSource.base n (by norm_num [IncrementSource.base]) _ digits).2 k hk

theorem roundData_normalized {old : Nat→Nat} {start : Nat} (digits : ∀k,k<6 → old (start+k)<base) :
    ∀k,k<6 → roundData old start (start+k)<base :=
  generic_round_normalized (dropped old start) start 6 (lost old start=0) (dropped_normalized digits)

#print axioms roundData_magnitude
#print axioms increment_status_zero
#print axioms roundData_normalized
end RH080Next.FFTPV.DropTwoSource
