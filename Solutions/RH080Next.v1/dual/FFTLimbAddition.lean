/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTLimbMultiplication

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.FFT.Limbs

/-- The source compares from the highest digit, returning 0,1,2. -/
def compareDigits (a b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n+1 => if b n < a n then 2 else if a n < b n then 0 else compareDigits a b n

theorem compareDigits_correct (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) (hb : ∀ j < n, b j < B) :
    compareDigits a b n=
      if magnitude B n b < magnitude B n a then 2
      else if magnitude B n a < magnitude B n b then 0 else 1 := by
  induction n with
  | zero => simp [compareDigits,magnitude]
  | succ n ih =>
    have ha' := magnitude_lt B n hB a (fun j hj => ha j (by omega))
    have hb' := magnitude_lt B n hB b (fun j hj => hb j (by omega))
    by_cases hba : b n < a n
    · have hm := Nat.mul_le_mul_right (B^n) (show b n+1 ≤ a n by omega)
      have hbig : magnitude B (n+1) b < magnitude B (n+1) a := by
        rw [magnitude_succ,magnitude_succ]
        nlinarith
      simp [compareDigits,hba,hbig]
    · by_cases hab : a n < b n
      · have hm := Nat.mul_le_mul_right (B^n) (show a n+1 ≤ b n by omega)
        have hbig : magnitude B (n+1) a < magnitude B (n+1) b := by
          rw [magnitude_succ,magnitude_succ]
          nlinarith
        simp [compareDigits,hba,hab,hbig,not_lt.mpr hbig.le]
      · have he : a n=b n := by omega
        rw [compareDigits,if_neg hba,if_neg hab,ih (fun j hj => ha j (by omega))
          (fun j hj => hb j (by omega))]
        simp [magnitude_succ,he]

theorem magnitude_prefix_update (B n v : ℕ) (d : ℕ → ℕ) :
    magnitude B (n+1) (Function.update d n v)=magnitude B n d+v*B^n := by
  rw [magnitude_succ]
  simp only [Function.update_self]
  congr 1
  unfold magnitude
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (show j≠n by have := Finset.mem_range.mp hj; omega)]

theorem value_prefix_update (B n v : ℕ) (d : ℕ → ℕ) :
    value B (n+1) (Function.update d n v)=value B n d+(v:ℤ)*(B:ℤ)^n := by
  have h := congrArg (fun t : ℕ => (t:ℤ)) (magnitude_prefix_update B n v d)
  push_cast at h
  simpa only [value_eq_magnitude] using h

def addDigits (B : ℕ) (a b : ℕ → ℕ) : ℕ → ((ℕ → ℕ) × ℕ)
  | 0 => (fun _ => 0,0)
  | n+1 =>
    let r := addDigits B a b n
    let t := a n+b n+r.2
    (Function.update r.1 n (t%B),t/B)

theorem addDigits_value (B n : ℕ) (a b : ℕ → ℕ) :
    magnitude B n (addDigits B a b n).1+(addDigits B a b n).2*B^n=
      magnitude B n a+magnitude B n b := by
  induction n with
  | zero => simp [addDigits,magnitude]
  | succ n ih =>
    let r := addDigits B a b n
    let t := a n+b n+r.2
    have hd : t%B+B*(t/B)=a n+b n+r.2 := Nat.mod_add_div t B
    change magnitude B (n+1) (Function.update r.1 n (t%B))+(t/B)*B^(n+1)=_
    rw [magnitude_prefix_update,magnitude_succ,magnitude_succ,pow_succ]
    change magnitude B n r.1+r.2*B^n=_ at ih
    have hh := congrArg (fun z : ℕ => z*B^n) hd
    nlinarith only [ih,hh]

theorem addDigits_no_overflow (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (hsmall : magnitude B n a+magnitude B n b < B^n) :
    (addDigits B a b n).2=0 ∧
      magnitude B n (addDigits B a b n).1=magnitude B n a+magnitude B n b := by
  have h := addDigits_value B n a b
  have hc : (addDigits B a b n).2=0 := by
    by_contra hh
    have hm := Nat.mul_le_mul_right (B^n) (Nat.one_le_iff_ne_zero.mpr hh)
    nlinarith
  exact ⟨hc,by simpa [hc] using h⟩

def subDigits (B : ℕ) (a b : ℕ → ℕ) : ℕ → ((ℕ → ℕ) × ℕ)
  | 0 => (fun _ => 0,0)
  | n+1 =>
    let r := subDigits B a b n
    let t := B+a n-b n-r.2
    (Function.update r.1 n (t%B),1-t/B)

theorem sub_digit_quotient_le_one (B a b c : ℕ) (hB : 0 < B)
    (ha : a < B) (hb : b < B) (hc : c ≤ 1) :
    (B+a-b-c)/B ≤ 1 := by
  have ht : B+a-b-c < 2*B := by omega
  have h := (Nat.div_lt_iff_lt_mul hB).mpr ht
  omega

theorem sub_digit_identity (B a b c : ℕ) (hB : 0 < B)
    (ha : a < B) (hb : b < B) (hc : c ≤ 1) :
    (((B+a-b-c)%B:ℕ):ℤ)-(B:ℤ)*((1-(B+a-b-c)/B:ℕ):ℤ)=
      (a:ℤ)-(b:ℤ)-(c:ℤ) := by
  let t := B+a-b-c
  have ht : t+b+c=B+a := by dsimp [t]; omega
  have hq : t/B ≤ 1 := sub_digit_quotient_le_one B a b c hB ha hb hc
  have hr : (1-t/B)+t/B=1 := by omega
  have hti : (t:ℤ)+(b:ℤ)+(c:ℤ)=(B:ℤ)+(a:ℤ) := by exact_mod_cast ht
  have hri : ((1-t/B:ℕ):ℤ)+((t/B:ℕ):ℤ)=1 := by exact_mod_cast hr
  have hdi : ((t%B:ℕ):ℤ)+(B:ℤ)*((t/B:ℕ):ℤ)=(t:ℤ) := by exact_mod_cast Nat.mod_add_div t B
  change ((t%B:ℕ):ℤ)-(B:ℤ)*((1-t/B:ℕ):ℤ)=_
  linear_combination hdi+hti-(B:ℤ)*hri

theorem subDigits_bounds (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) (hb : ∀ j < n, b j < B) :
    (subDigits B a b n).2 ≤ 1 ∧ ∀ j < n, (subDigits B a b n).1 j < B := by
  induction n with
  | zero => simp [subDigits]
  | succ n ih =>
    have hi := ih (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    constructor
    · exact Nat.sub_le _ _
    · intro j hj
      by_cases he : j=n
      · subst j
        simp only [subDigits,Function.update_self]
        exact Nat.mod_lt _ hB
      · simp only [subDigits,Function.update_of_ne he]
        exact hi.2 j (by omega)

/-- Exact subtract-with-borrow invariant of all source digits. -/
theorem subDigits_value (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) (hb : ∀ j < n, b j < B) :
    value B n (subDigits B a b n).1-((subDigits B a b n).2:ℤ)*(B:ℤ)^n=
      value B n a-value B n b := by
  induction n with
  | zero => simp [subDigits,value]
  | succ n ih =>
    have ha' : ∀ j < n, a j < B := fun j hj => ha j (by omega)
    have hb' : ∀ j < n, b j < B := fun j hj => hb j (by omega)
    have ih' := ih ha' hb'
    let r := subDigits B a b n
    let t := B+a n-b n-r.2
    have hc : r.2 ≤ 1 := (subDigits_bounds B n hB a b ha' hb').1
    have hd := sub_digit_identity B (a n) (b n) r.2 hB (ha n (by omega)) (hb n (by omega)) hc
    change ((t%B:ℕ):ℤ)-(B:ℤ)*((1-t/B:ℕ):ℤ)=(a n:ℤ)-(b n:ℤ)-(r.2:ℤ) at hd
    change value B (n+1) (Function.update r.1 n (t%B))-((1-t/B:ℕ):ℤ)*(B:ℤ)^(n+1)=_
    rw [value_prefix_update,value_succ,value_succ,pow_succ]
    change value B n r.1-(r.2:ℤ)*(B:ℤ)^n=_ at ih'
    linear_combination ih'+(B:ℤ)^n*hd

theorem subDigits_no_borrow (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) (hb : ∀ j < n, b j < B)
    (hab : magnitude B n b ≤ magnitude B n a) :
    (subDigits B a b n).2=0 ∧
      magnitude B n (subDigits B a b n).1=magnitude B n a-magnitude B n b := by
  have h := subDigits_value B n hB a b ha hb
  have hbounds := subDigits_bounds B n hB a b ha hb
  have hmag := magnitude_lt B n hB _ hbounds.2
  simp only [value_eq_magnitude] at h
  have habInt : (magnitude B n b:ℤ) ≤ (magnitude B n a:ℤ) := by exact_mod_cast hab
  have hpos : (0:ℤ) ≤ (magnitude B n a:ℤ)-(magnitude B n b:ℤ) := sub_nonneg.mpr habInt
  have hc : (subDigits B a b n).2=0 := by
    by_contra hh
    have he : (subDigits B a b n).2=1 := by omega
    have hm : (magnitude B n (subDigits B a b n).1:ℤ) < (B:ℤ)^n := by exact_mod_cast hmag
    rw [he] at h
    norm_num at h
    linarith
  refine ⟨hc,?_⟩
  rw [hc] at h
  norm_num at h
  have he : (magnitude B n a:ℤ)-(magnitude B n b:ℤ)=((magnitude B n a-magnitude B n b:ℕ):ℤ) :=
    (Nat.cast_sub hab).symm
  rw [he] at h
  exact_mod_cast h

def signed (negative : Bool) (m : ℕ) : ℤ := if negative then -(m:ℤ) else (m:ℤ)

def signedAddResult (sa sb : Bool) (a b : ℕ) : ℤ :=
  if sa=sb then signed sa (a+b)
  else if a < b then signed sb (b-a) else signed sa (a-b)

theorem signedAddResult_correct (sa sb : Bool) (a b : ℕ) :
    signedAddResult sa sb a b=signed sa a+signed sb b := by
  cases sa <;> cases sb <;> simp only [signedAddResult,signed]
  all_goals split_ifs <;> norm_num <;> omega

structure SignedResult where
  digits : ℕ → ℕ
  negative : Bool
  status : ℕ

/-- Exactly the mathematical digit/sign/status branches of fixed_add,
after its optional subtraction flag has selected the second input sign,
and before the final canonical_sign operation. Canonicalization preserves
the represented integer, as proved below. -/
def fixedAddMath (B n : ℕ) (a b : ℕ → ℕ) (sa sb : Bool) : SignedResult :=
  if sa=sb then
    let r := addDigits B a b n
    ⟨r.1,sa,r.2⟩
  else if compareDigits a b n=0 then
    ⟨(subDigits B b a n).1,sb,0⟩
  else ⟨(subDigits B a b n).1,sa,0⟩

/-- Full signed result of the source-matching mathematical algorithm,
including the checked overflow status. There is no assumed output sum. -/
theorem fixedAddMath_correct (B n : ℕ) (hB : 0 < B) (a b : ℕ → ℕ)
    (ha : ∀ j < n, a j < B) (hb : ∀ j < n, b j < B)
    (sa sb : Bool) (hstatus : (fixedAddMath B n a b sa sb).status=0) :
    signed (fixedAddMath B n a b sa sb).negative
      (magnitude B n (fixedAddMath B n a b sa sb).digits)=
        signed sa (magnitude B n a)+signed sb (magnitude B n b) := by
  rw [←signedAddResult_correct]
  by_cases hs : sa=sb
  · have hc : (addDigits B a b n).2=0 := by simpa [fixedAddMath,hs] using hstatus
    have hv := addDigits_value B n a b
    rw [hc,zero_mul,add_zero] at hv
    simpa [fixedAddMath,hs,signedAddResult,hv]
  · have hcmp := compareDigits_correct B n hB a b ha hb
    by_cases hz : compareDigits a b n=0
    · have hab : magnitude B n a < magnitude B n b := by
        rw [hz] at hcmp
        split_ifs at hcmp <;> omega
      have hv := (subDigits_no_borrow B n hB b a hb ha hab.le).2
      simp [fixedAddMath,hs,hz,signedAddResult,hab,hv]
    · have hab : magnitude B n b ≤ magnitude B n a := by
        by_contra hh
        have hh' : magnitude B n a < magnitude B n b := lt_of_not_ge hh
        have hba : ¬magnitude B n b < magnitude B n a := not_lt.mpr hh'.le
        simp only [hba,hh',↓reduceIte] at hcmp
        exact hz hcmp
      have hv := (subDigits_no_borrow B n hB a b ha hb hab).2
      simp [fixedAddMath,hs,hz,signedAddResult,not_lt.mpr hab,hv]

theorem signed_toggle (s subtract : Bool) (m : ℕ) :
    signed (Bool.xor s subtract) m=(if subtract then -signed s m else signed s m) := by
  cases s <;> cases subtract <;> simp [signed]

/-- The actual canonical_sign tests the unweighted sum of five digits.
Its zero test is equivalent to zero magnitude, so even a negative-zero
intermediate is normalized without changing the represented integer. -/
theorem canonical_sign_preserves (B n : ℕ) (hB : 0 < B) (d : ℕ → ℕ) (s : Bool) :
    signed (if (∑ j ∈ Finset.range n, d j)=0 then false else s) (magnitude B n d)=
      signed s (magnitude B n d) := by
  by_cases hz : (∑ j ∈ Finset.range n, d j)=0
  · have hm := (lost_sum_zero_iff B n hB d).mp hz
    simp [hz,hm,signed]
  · simp [hz]


#print axioms subDigits_value
#print axioms subDigits_no_borrow
#print axioms signedAddResult_correct
#print axioms fixedAddMath_correct

#print axioms compareDigits_correct
#print axioms addDigits_value
#print axioms addDigits_no_overflow
end RH080Next.FFT.Limbs
