/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddCanonical
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect WordArrays FFT.Limbs
open IncrementSource (base)

def mathResult (input : Input) : SignedResult:=fixedAddMath base 5 input.a input.b
  (decide (input.asign≠0)) (decide (input.bsign≠0))

theorem rawData_math_digit (input : Input) (i : Nat) (hi : i < 5) :
    rawData input (input.layout.start .out+i)=(mathResult input).digits i := by
  have ha : input.asign=0 ∨ input.asign=1:=by have h:=input.signA; change input.asign ≤ 1 at h; omega
  have hb : input.bsign=0 ∨ input.bsign=1:=by have h:=input.bsign_bound; omega
  have interval : input.layout.start .out ≤ input.layout.start .out+i ∧
      input.layout.start .out+i < input.layout.start .out+5:=by omega
  rcases ha with ha|ha <;> rcases hb with hb|hb
  all_goals
    by_cases hc : input.cmp=0
    all_goals
      simp [rawData,signedData,Function.update_of_ne (show input.layout.start .out+i≠input.layout.start .out+5 by omega),
        currentData,interval,mathResult,fixedAddMath,Input.left,Input.right,Input.subtractionSign,scan,ha,hb,hc,Input.cmp] at *
  all_goals simp_all

theorem rawData_math_sign (input : Input) :
    decide (rawData input (input.layout.start .out+5)≠0)=(mathResult input).negative := by
  have ha : input.asign=0 ∨ input.asign=1:=by have h:=input.signA; change input.asign ≤ 1 at h; omega
  have hb : input.bsign=0 ∨ input.bsign=1:=by have h:=input.bsign_bound; omega
  rcases ha with ha|ha <;> rcases hb with hb|hb
  all_goals
    by_cases hc : input.cmp=0
    all_goals simp [rawData,signedData,mathResult,fixedAddMath,Input.subtractionSign,ha,hb,hc,Input.cmp] at *
  all_goals simp_all

theorem rawStatus_math (input : Input) : rawStatus input=(mathResult input).status := by
  have ha : input.asign=0 ∨ input.asign=1:=by have h:=input.signA; change input.asign ≤ 1 at h; omega
  have hb : input.bsign=0 ∨ input.bsign=1:=by have h:=input.bsign_bound; omega
  rcases ha with ha|ha <;> rcases hb with hb|hb
  all_goals
    by_cases hc : input.cmp=0
    all_goals simp [rawStatus,mathResult,fixedAddMath,Input.left,Input.right,scan,ha,hb,hc,Input.cmp] at *
  all_goals simp_all

theorem raw_magnitude_math (input : Input) :
    magnitude base 5 (fun i=>rawData input (input.layout.start .out+i))=
      magnitude base 5 (mathResult input).digits := by
  apply Finset.sum_congr rfl
  intro i hi
  change rawData input (input.layout.start .out+i)*base^i=_
  rw [rawData_math_digit input i (Finset.mem_range.mp hi)]

theorem effective_sign_correct (input : Input) (m : Nat) :
    signed (decide (input.bsign≠0)) m=
      if 0 < input.subtract then -signed (decide (input.old (input.layout.object .b) (input.layout.start .b+5)≠0)) m
      else signed (decide (input.old (input.layout.object .b) (input.layout.start .b+5)≠0)) m := by
  have hs : input.old (input.layout.object .b) (input.layout.start .b+5)=0 ∨
      input.old (input.layout.object .b) (input.layout.start .b+5)=1:=by have h:=input.signB; omega
  rcases hs with hs|hs <;> by_cases hflag : 0 < input.subtract <;> simp [Input.bsign,hs,hflag,signed]

theorem finalData_digits (input : Input) : ∀i < 5,finalData input (input.layout.start .out+i) < base := by
  intro i hi
  rw [finalData,CanonicalSource.canonicalData_digit _ _ i hi]
  exact rawData_digits input i hi

theorem rawData_sign_bound (input : Input) : rawData input (input.layout.start .out+5) ≤ 1 := by
  unfold rawData
  split_ifs
  · simpa only [signedData,Function.update_self,Input.asign] using input.signA
  · simp only [signedData,Function.update_self,Input.subtractionSign]
    split_ifs
    · exact input.bsign_bound
    · exact input.signA

theorem finalData_sign_bound (input : Input) : finalData input (input.layout.start .out+5) ≤ 1 := by
  rw [finalData,CanonicalSource.canonicalData_sign]
  split_ifs
  · norm_num
  · exact rawData_sign_bound input

theorem rawStatus_zero_of_sum_lt (input : Input)
    (small : magnitude base 5 input.a+magnitude base 5 input.b < base^5) : rawStatus input=0 := by
  unfold rawStatus
  split_ifs
  · exact (addDigits_no_overflow base 5 (by norm_num [base]) input.a input.b small).1
  · rfl

/-- The actual source digit/sign branches refine mathematical signed integer
addition or subtraction, provided the actual returned overflow status is zero. -/
theorem finalData_integer_correct (input : Input) (status : rawStatus input=0) :
    CanonicalSource.represented (finalData input) (input.layout.start .out)=
      if 0 < input.subtract then
        CanonicalSource.represented (input.old (input.layout.object .a)) (input.layout.start .a)-
          CanonicalSource.represented (input.old (input.layout.object .b)) (input.layout.start .b)
      else CanonicalSource.represented (input.old (input.layout.object .a)) (input.layout.start .a)+
          CanonicalSource.represented (input.old (input.layout.object .b)) (input.layout.start .b) := by
  have hstatus : (mathResult input).status=0:=by rw [←rawStatus_math]; exact status
  have math:=fixedAddMath_correct base 5 (by norm_num [base]) input.a input.b input.digitsA input.digitsB
    (decide (input.asign≠0)) (decide (input.bsign≠0)) hstatus
  change signed (mathResult input).negative (magnitude base 5 (mathResult input).digits)=_ at math
  rw [show finalData input=CanonicalSource.canonicalData (rawData input) (input.layout.start .out) from rfl,
    CanonicalSource.canonicalData_preserves]
  unfold CanonicalSource.represented
  have mag:=raw_magnitude_math input
  dsimp only [base] at mag math
  rw [rawData_math_sign,mag,math,effective_sign_correct]
  unfold Input.asign Input.a Input.b
  split_ifs <;> ring

#print axioms rawData_math_digit
#print axioms rawStatus_math
#print axioms finalData_integer_correct
end RH080Next.FFTPV.AddSource
