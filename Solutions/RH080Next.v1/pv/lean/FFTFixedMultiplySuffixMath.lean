/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixExecution
import FFTLimbSuffix
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open FFT.Limbs

theorem retainedData_magnitude (old data : Nat → Nat) (outStart workStart sign : Nat) :
    magnitude 1000000000 5 (fun j => retainedData old data outStart workStart sign (outStart+j)) =
      magnitude 1000000000 5 (fun j => data (workStart+(j+4))) := by
  apply Finset.sum_congr rfl
  intro j hj
  change retainedData old data outStart workStart sign (outStart+j)*1000000000^j = _
  rw [retainedData_digit old data outStart workStart sign j (Finset.mem_range.mp hj)]

theorem retainedData_sign (old data : Nat → Nat) (outStart workStart sign : Nat) :
    retainedData old data outStart workStart sign (outStart+5)=sign := by
  simp [retainedData]

theorem roundedData_sign (old : Nat → Nat) (start sign lost : Nat) :
    roundedData old start sign lost (start+5)=old (start+5) := by
  unfold roundedData
  split
  · simp [IncrementSource.currentData]
  · rfl

/-- Positional output/carry equation follows from the executed source recurrence
and the verified increment helper. It retains all rounding and overflow terms. -/
theorem suffix_output_equation (old data : Nat → Nat) (outStart workStart sign : Nat) :
    let raw:=retainedData old data outStart workStart sign
    let lost:=CanonicalSource.digitSum data workStart 4
    magnitude 1000000000 5 (fun j => roundedData raw outStart sign lost (outStart+j))+
      roundingCarry raw outStart sign lost*1000000000^5 =
      magnitude 1000000000 5 (fun j => data (workStart+(j+4)))+
        (if decide (sign≠0) && decide ((∑j ∈ Finset.range 4,data (workStart+j))≠0) then 1 else 0) := by
  dsimp only
  let raw:=retainedData old data outStart workStart sign
  let lost:=CanonicalSource.digitSum data workStart 4
  change magnitude 1000000000 5 (fun j => roundedData raw outStart sign lost (outStart+j))+
      roundingCarry raw outStart sign lost*1000000000^5 =
      magnitude 1000000000 5 (fun j => data (workStart+(j+4)))+
        (if decide (sign≠0) && decide (lost≠0) then 1 else 0)
  have hm : magnitude 1000000000 5 (fun j => raw (outStart+j)) =
      magnitude 1000000000 5 (fun j => data (workStart+(j+4))) :=
    retainedData_magnitude old data outStart workStart sign
  by_cases hs : 0<sign
  · by_cases hl : 0<lost
    · have hh:=IncrementSource.currentData_value raw outStart 5
      dsimp only [IncrementSource.base] at hh
      rw [hm] at hh
      have hc : (decide (sign≠0) && decide (lost≠0))=true := by simp [show sign≠0 by omega,show lost≠0 by omega]
      simpa [roundedData,roundingCarry,hs,hl,show sign≠0 by omega,show lost≠0 by omega] using hh
    · have hz : lost=0:=by omega
      simpa [roundedData,roundingCarry,hs,hl,hz] using hm
  · have hz : sign=0:=by omega
    simpa [roundedData,roundingCarry,hs,hz] using hm

/-- A zero returned status implies the actual canonicalized output is the true
signed Euclidean quotient. No hardcoded output or desired quotient is assumed. -/
theorem finalData_successful (old data : Nat → Nat) (outStart workStart sign : Nat)
    (digits : ∀j,j<10 → data (workStart+j)<1000000000)
    (status : finalStatus old data outStart workStart sign=0) :
    CanonicalSource.represented (finalData old data outStart workStart sign) outStart =
      (if decide (sign≠0) then -(magnitude 1000000000 10 (fun j => data (workStart+j)):Int)
        else (magnitude 1000000000 10 (fun j => data (workStart+j)):Int))/(1000000000^4:Nat) := by
  rw [finalData,CanonicalSource.canonicalData_preserves]
  have signEq : decide (roundedData (retainedData old data outStart workStart sign) outStart sign
      (CanonicalSource.digitSum data workStart 4) (outStart+5)≠0)=decide (sign≠0) := by
    rw [roundedData_sign,retainedData_sign]
  unfold CanonicalSource.represented
  rw [signEq]
  apply successful_product_suffix 1000000000 (by norm_num) (fun j => data (workStart+j)) digits
    (decide (sign≠0)) _ _ (suffix_output_equation old data outStart workStart sign)
  exact status

/-- Normalized bounded input magnitudes force the real suffix status to zero;
the optional negative rounding cannot overflow the retained five words. -/
theorem finalStatus_eq_zero (old data : Nat → Nat) (outStart workStart sign : Nat)
    (top : data (workStart+9)=0)
    (safe : magnitude 1000000000 5 (fun j => data (workStart+(j+4)))+1<1000000000^5) :
    finalStatus old data outStart workStart sign=0 := by
  unfold finalStatus roundingCarry
  rw [top]
  split
  · have hm:=retainedData_magnitude old data outStart workStart sign
    have hc:=incrementDigits_no_overflow 1000000000 5 (by norm_num)
      (fun j => retainedData old data outStart workStart sign (outStart+j)) (by rwa [hm])
    simp [hc.1]
  · rfl

#print axioms suffix_output_equation
#print axioms finalData_successful
#print axioms finalStatus_eq_zero
end RH080Next.FFTPV.MultiplySuffix
