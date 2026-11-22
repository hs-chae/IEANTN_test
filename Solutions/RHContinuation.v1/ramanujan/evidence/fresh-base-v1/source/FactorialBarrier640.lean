import AnalyticBarrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 10000

lemma const_div_pow_hasDerivAt (c : ℝ) (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ => c/x^(n+1))
      (-((n+1:ℕ):ℝ)*c/t^(n+2)) t := by
  have hd := (hasDerivAt_const t c).div ((hasDerivAt_id t).pow (n+1))
    (pow_ne_zero _ ht)
  convert! hd using 1
  simp only [Pi.pow_apply, id_eq, Nat.add_sub_cancel, mul_one, zero_mul, zero_sub]
  field_simp
  simp only [pow_succ]
  ring

noncomputable def pDiv (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (N+1), (Nat.factorial k : ℝ)/t^(k+1)

lemma pDiv_succ (N : ℕ) (t : ℝ) :
    pDiv (N+1) t = pDiv N t + (Nat.factorial (N+1):ℝ)/t^(N+2) := by
  simp [pDiv, Finset.sum_range_succ, Nat.add_assoc]

/-- The exact telescoping factorial identity, before any barrier is applied. -/
theorem pDiv_hasDerivAt (N : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (pDiv N)
      (1/t - (Nat.factorial (N+1):ℝ)/t^(N+2) - pDiv N t) t := by
  induction N with
  | zero =>
    have h := const_div_pow_hasDerivAt 1 0 ht
    convert! h using 1
    · funext x
      simp [pDiv]
    · simp [pDiv]
      ring
  | succ N ih =>
    have h := ih.add (const_div_pow_hasDerivAt (Nat.factorial (N+1):ℝ) (N+1) ht)
    convert! h using 1
    · funext x
      exact pDiv_succ N x
    · rw [pDiv_succ, Nat.factorial_succ]
      push_cast
      simp only [Nat.add_assoc]
      field_simp
      ring

/-- Positivity of the source residual from its true initial anchor. -/
theorem residual_lower {r : ℝ → ℝ} {N : ℕ} {a x : ℝ}
    (ha : 0 < a) (hax : a ≤ x)
    (hd : ∀ t ∈ Ici a, HasDerivAt r
      ((Nat.factorial (N+1):ℝ)/t^(N+2)-r t) t)
    (hanchor : 0 ≤ r a) : 0 ≤ r x := by
  apply ode_nonneg hax hd _ hanchor
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hp : 0 ≤ (Nat.factorial (N+1):ℝ)/t^(N+2) := by positivity
  linarith

/-- Exact inverse-power upper barrier. Its hypotheses are a true ODE,
one initial value, and a scalar supersolution inequality. -/
theorem residual_upper {r : ℝ → ℝ} {N : ℕ} {a x C : ℝ}
    (ha : 0 < a) (hax : a ≤ x) (hC : 0 ≤ C)
    (hd : ∀ t ∈ Ici a, HasDerivAt r
      ((Nat.factorial (N+1):ℝ)/t^(N+2)-r t) t)
    (hanchor : r a ≤ C*(Nat.factorial (N+1):ℝ)/a^(N+2))
    (hsuper : 1 ≤ C*(1-((N+2:ℕ):ℝ)/a)) :
    r x ≤ C*(Nat.factorial (N+1):ℝ)/x^(N+2) := by
  apply ode_compare hax hd
    (fun t ht => const_div_pow_hasDerivAt (C*(Nat.factorial (N+1):ℝ)) (N+1)
      (ne_of_gt (lt_of_lt_of_le ha ht))) _ hanchor
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hquot : ((N+2:ℕ):ℝ)/t ≤ ((N+2:ℕ):ℝ)/a :=
    div_le_div_of_nonneg_left (by positivity) ha ht
  have hsup : 1 ≤ C*(1-((N+2:ℕ):ℝ)/t) := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hquot)]
  have hfactor : 0 ≤ (Nat.factorial (N+1):ℝ)/t^(N+2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsup hfactor
  have heq : (Nat.factorial (N+1):ℝ)/t^(N+2)*
      (C*(1-((N+2:ℕ):ℝ)/t)) =
      -((N+1+1:ℕ):ℝ)*(C*(Nat.factorial (N+1):ℝ))/t^(N+1+2)+
        C*(Nat.factorial (N+1):ℝ)/t^(N+2) := by
    norm_num only [Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat]
    field_simp
    simp only [pow_succ]
    ring
  rw [heq] at hmul
  linarith

lemma source_scalar_supersolutions :
    1 ≤ (3:ℝ)*(1-(3+2)/13) ∧
    1 ≤ (7:ℝ)*(1-(20+2)/26) := by norm_num

#print axioms const_div_pow_hasDerivAt
#print axioms pDiv_hasDerivAt
#print axioms residual_lower
#print axioms residual_upper
end Ramanujan640.AnalyticBarrier
