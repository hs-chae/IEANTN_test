import ActualCompensatedJ
import PrimePowerTransport
namespace RHContinuation.Ramanujan
open Real Finset ArithmeticFunction IEANTN
set_option maxHeartbeats 0

lemma finite_J_primepowers {x : ℝ} (hx : 0 ≤ x) :
    FiniteMangoldtAbel.J x =
      ∑ k ∈ Icc 1 ⌊Real.log x/Real.log 2⌋₊, primeCounting (x^(1/(k:ℝ)))/(k:ℝ) := by
  have hJ : FiniteMangoldtAbel.J x =
      ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n,
        (ArithmeticFunction.vonMangoldt n:ℝ)/Real.log n := by
    unfold FiniteMangoldtAbel.J
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : (0:ℕ) ≤ ⌊x⌋₊)]
    simp only [ArithmeticFunction.map_zero,zero_div,zero_add]
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    split_ifs with hp
    · rfl
    · rw [vonMangoldt_eq_zero_iff.mpr hp,zero_div]
  rw [hJ,Chebyshev.sum_PrimePow_eq_sum_sum _ hx]
  apply sum_congr rfl
  intro k hk
  have hk0 : k ≠ 0 := by have := (mem_Icc.mp hk).1; omega
  have hc : (k:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hterm (p : ℕ) (hp : p.Prime) :
      (ArithmeticFunction.vonMangoldt (p^k):ℝ)/Real.log (p^k:ℕ) = 1/(k:ℝ) := by
    rw [vonMangoldt_apply_pow hk0,vonMangoldt_apply_prime hp,Nat.cast_pow,Real.log_pow]
    have hp0 : Real.log (p:ℝ) ≠ 0 := (log_pos (by exact_mod_cast hp.one_lt)).ne'
    field_simp [hc,hp0]
  simp_rw [sum_filter]
  have hh : (∑ p ∈ Ioc 0 ⌊x^(1/(k:ℝ))⌋₊,
      if p.Prime then (ArithmeticFunction.vonMangoldt (p^k):ℝ)/Real.log (p^k:ℕ) else 0) =
      ∑ p ∈ (Ioc 0 ⌊x^(1/(k:ℝ))⌋₊).filter Nat.Prime, 1/(k:ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    split_ifs with h
    · exact hterm p h
    · rfl
  rw [hh,sum_const]
  have hs : (Ioc 0 ⌊x^(1/(k:ℝ))⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊x^(1/(k:ℝ))⌋₊ := by
    rw [Nat.primesLE_eq_filter_Icc_zero]
    ext p
    simp only [mem_filter,mem_Ioc,mem_Icc,Nat.zero_le,true_and]
    have hp := Nat.Prime.pos (p:=p)
    aesop
  rw [hs,Nat.primesLE_card_eq_primeCounting]
  simp [primeCounting,nsmul_eq_mul,div_eq_mul_inv]

lemma prime_root_zero_past_log {x : ℝ} (hx : 0 < x) {k : ℕ}
    (hk : ⌊Real.log x/Real.log 2⌋₊ ≤ k) : primeCounting (x^(1/(k+1:ℝ)))=0 := by
  have h2 : 0 < Real.log (2:ℝ) := log_pos (by norm_num)
  have hk1 : 0 < (k:ℝ)+1 := by positivity
  have hf := Nat.lt_floor_add_one (Real.log x/Real.log 2)
  have hkcast : (⌊Real.log x/Real.log 2⌋₊:ℝ) ≤ k := by exact_mod_cast hk
  have hh : Real.log x/Real.log 2 < (k:ℝ)+1 := by linarith
  have hm : Real.log x < ((k:ℝ)+1)*Real.log 2 := (div_lt_iff₀ h2).mp hh
  have hroot : x^(1/(k+1:ℝ)) < 2 := by
    rw [Real.rpow_def_of_pos hx]
    calc exp (Real.log x*(1/(k+1:ℝ))) < exp (Real.log 2) := by
          apply exp_lt_exp.mpr
          simpa [div_eq_mul_inv] using (div_lt_iff₀ hk1).mpr (by simpa [mul_comm] using hm)
      _ = 2 := exp_log (by norm_num)
  exact Ramanujan640.primeCounting_zero_of_lt_two (Real.rpow_nonneg hx.le _) hroot

/-- Actual finite Mangoldt/Real.log sum equals the actual vocabulary Riemann count,
for every positive real x, including all prime-power endpoints. -/
theorem actual_J_eq_riemann {x : ℝ} (hx : 0 < x) :
    FiniteMangoldtAbel.J x = IEANTN.riemannPrimeCounting x := by
  rw [finite_J_primepowers hx.le]
  unfold riemannPrimeCounting
  rw [tsum_eq_sum (s:=range ⌊Real.log x/Real.log 2⌋₊) (fun k hk => by
    have h : ⌊Real.log x/Real.log 2⌋₊ ≤ k := by simpa only [mem_range,not_lt] using hk
    rw [prime_root_zero_past_log hx h,zero_div])]
  apply (sum_bij (fun k hk => k+1) ?_ ?_ ?_ ?_).symm
  · intro k hk
    simp only [mem_range] at hk
    simp only [mem_Icc]
    omega
  · intro a ha b hb he
    omega
  · intro k hk
    have h := mem_Icc.mp hk
    refine ⟨k-1,mem_range.mpr (by omega),?_⟩
    omega
  · intro k hk
    simp [Nat.cast_add,Nat.cast_one]

lemma actual_riemann_series_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun k : ℕ => primeCounting (x^(1/(k+1:ℝ)))/(k+1:ℝ)) := by
  apply summable_of_ne_finset_zero (s:=Finset.range ⌊Real.log x/Real.log 2⌋₊)
  intro k hk
  have h : ⌊Real.log x/Real.log 2⌋₊ ≤ k := by simpa only [mem_range,not_lt] using hk
  rw [prime_root_zero_past_log hx h,zero_div]

/-- The independent lower-height prime-power expression, with summability proved. -/
theorem actual_prime_power_series {x : ℝ} (hx : 0 < x) :
    riemannPrimeCounting x-primeCounting x =
      ∑' k : ℕ, primeCounting (x^(1/(k+2:ℝ)))/(k+2:ℝ) := by
  have hs := actual_riemann_series_summable hx
  unfold riemannPrimeCounting
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero,zero_add,div_one,Real.rpow_one]
  simp only [add_sub_cancel_left]
  apply tsum_congr
  intro k
  norm_num [Nat.cast_add,Nat.cast_one,add_assoc]

lemma actual_prime_power_nonnegative {x : ℝ} (hx : 0 < x) :
    0 ≤ riemannPrimeCounting x-primeCounting x := by
  rw [actual_prime_power_series hx]
  apply tsum_nonneg
  intro k
  unfold primeCounting
  positivity

#print axioms actual_prime_power_series
#print axioms actual_prime_power_nonnegative
theorem actual_riemann_abel {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    riemannPrimeCounting b-riemannPrimeCounting a =
      Chebyshev.psi b/Real.log b-Chebyshev.psi a/Real.log a+
        ∫ t in Set.Ioc a b, Chebyshev.psi t/(t*(Real.log t)^2) := by
  rw [← actual_J_eq_riemann (by linarith : 0 < b),
    ← actual_J_eq_riemann (by linarith : 0 < a)]
  exact FiniteMangoldtAbel.abel ha hab

theorem actual_riemann_compensation {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (riemannPrimeCounting b-IEANTN.li b-(Chebyshev.psi b-b)/Real.log b)-
      (riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/Real.log a) =
        ∫ t in Set.Ioc a b, (Chebyshev.psi t-t)/(t*(Real.log t)^2) := by
  rw [← actual_J_eq_riemann (by linarith : 0 < b),
    ← actual_J_eq_riemann (by linarith : 0 < a)]
  exact actual_finite_J_compensation ha hab

#print axioms actual_riemann_abel
#print axioms actual_riemann_compensation
#print axioms actual_J_eq_riemann
end RHContinuation.Ramanujan
