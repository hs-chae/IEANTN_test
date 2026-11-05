/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Global

/-!
# A Mills constant for every real exponent `k ≥ 8`, under QRH

Mills (1947): if every interval `(q^k, (q+1)^k − 1)` with `q ≥ q₀` contains a prime, then there is
`A` with `⌊A^{k^n}⌋` prime for every `n`. Choose primes `p₀ ≥ q₀`, `p_{n+1} ∈ (p_n^k, (p_n+1)^k − 1)`;
then `p_n^{k^{-n}}` increases, `(p_n + 1)^{k^{-n}}` decreases, and their common limit `A`
satisfies `p_n ≤ A^{k^n} < p_n + 1` (`mills_of_step`, a generic construction).

Under QRH, `global_interval` gives a prime in `(q^k, q^k + q^{7k/8}]`, and `q^{7k/8} ≤ q^{k−1}`
once `k ≥ 8`, which is well inside `(q^k, (q+1)^k − 1)` for every `q ≥ 1` (`step_of_qrh`). So for
every real `k ≥ 8` and every prime `p₀` there is a Mills constant `A ∈ [p₀, p₀ + 1)` with
`⌊A^{k^n}⌋` prime for all `n ≥ 0` (`mills_qrh`).

**What is and is not new.** Mills' theorem itself is unconditional for `k = 3` (Ingham's prime
intervals, with `p₀` large and not explicit). What QRH adds here is that every exponent `k ≥ 8`
works from every starting prime, `p₀ = 2` included, so `A` is pinned in an explicit interval
`[p₀, p₀ + 1)`; under RH the analogue holds for `k = 3` only from a large `p₀` (classical results)
unless one also verifies the small cubes.
-/

namespace QRHGlobal

open Real IEANTN

section Construction

variable {k : ℝ} {p₀ : ℕ}

/-- The Mills sequence: `p₀`, then a chosen prime in `(q^k, (q+1)^k − 1)` above each term. -/
noncomputable def millsSeq (k : ℝ) (p₀ : ℕ)
    (step : ∀ q : ℕ, p₀ ≤ q →
      ∃ p : ℕ, p.Prime ∧ (q : ℝ) ^ k < p ∧ (p : ℝ) + 1 < ((q : ℝ) + 1) ^ k) : ℕ → ℕ
  | 0 => p₀
  | n + 1 =>
      if h : p₀ ≤ millsSeq k p₀ step n then Classical.choose (step _ h) else p₀

theorem millsSeq_spec (hk : 1 ≤ k) (hp₀ : p₀.Prime)
    (step : ∀ q : ℕ, p₀ ≤ q →
      ∃ p : ℕ, p.Prime ∧ (q : ℝ) ^ k < p ∧ (p : ℝ) + 1 < ((q : ℝ) + 1) ^ k) :
    ∀ n, (millsSeq k p₀ step n).Prime ∧ p₀ ≤ millsSeq k p₀ step n ∧
      ((millsSeq k p₀ step n : ℝ) ^ k < millsSeq k p₀ step (n + 1) ∧
        (millsSeq k p₀ step (n + 1) : ℝ) + 1 < ((millsSeq k p₀ step n : ℝ) + 1) ^ k) := by
  intro n
  induction n with
  | zero =>
      have h0 : p₀ ≤ millsSeq k p₀ step 0 := le_refl p₀
      have hs : millsSeq k p₀ step 1 = Classical.choose (step _ h0) := by
        simp [millsSeq]
      have hc := Classical.choose_spec (step _ h0)
      refine ⟨hp₀, le_refl _, ?_, ?_⟩
      · rw [hs]; exact hc.2.1
      · rw [hs]; exact hc.2.2
  | succ n ih =>
      obtain ⟨hpr, hge, hlt, hlt'⟩ := ih
      have hs1 : millsSeq k p₀ step (n + 1) = Classical.choose (step _ hge) := by
        simp [millsSeq, hge]
      have hc := Classical.choose_spec (step _ hge)
      have hpr' : (millsSeq k p₀ step (n + 1)).Prime := by rw [hs1]; exact hc.1
      -- the new term is at least the old one: q ≤ q^k < p
      have hq1 : (1 : ℝ) ≤ millsSeq k p₀ step n := by exact_mod_cast hpr.one_lt.le
      have hqk : (millsSeq k p₀ step n : ℝ) ≤ (millsSeq k p₀ step n : ℝ) ^ k := by
        calc (millsSeq k p₀ step n : ℝ) = (millsSeq k p₀ step n : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
          _ ≤ _ := rpow_le_rpow_of_exponent_le hq1 hk
      have hge' : p₀ ≤ millsSeq k p₀ step (n + 1) := by
        have : (millsSeq k p₀ step n : ℝ) < millsSeq k p₀ step (n + 1) := by linarith
        have : millsSeq k p₀ step n < millsSeq k p₀ step (n + 1) := by exact_mod_cast this
        omega
      have hs2 : millsSeq k p₀ step (n + 1 + 1) = Classical.choose (step _ hge') := by
        rw [millsSeq]
        split_ifs
        rfl
      have hc2 := Classical.choose_spec (step _ hge')
      refine ⟨hpr', hge', ?_, ?_⟩
      · rw [hs2]; exact hc2.2.1
      · rw [hs2]; exact hc2.2.2

/-- **Mills' construction.** From prime steps `q^k < p`, `p + 1 < (q + 1)^k` for all `q ≥ p₀`, with
`p₀` prime and `k > 1`, there is `A ∈ [p₀, p₀ + 1)` with `⌊A^{k^n}⌋` prime for every `n`. -/
theorem mills_of_step (hk : 1 < k) (hp₀ : p₀.Prime)
    (step : ∀ q : ℕ, p₀ ≤ q →
      ∃ p : ℕ, p.Prime ∧ (q : ℝ) ^ k < p ∧ (p : ℝ) + 1 < ((q : ℝ) + 1) ^ k) :
    ∃ A : ℝ, (p₀ : ℝ) ≤ A ∧ A < p₀ + 1 ∧ ∀ n : ℕ, (⌊A ^ (k ^ n)⌋₊).Prime := by
  set s := millsSeq k p₀ step with hsdef
  have spec := millsSeq_spec hk.le hp₀ step
  have hk0 : 0 < k := by linarith
  have hs0 : ∀ n, (0 : ℝ) < s n := fun n => by exact_mod_cast (spec n).1.pos
  -- exponents e n = (k^n)⁻¹
  have hkn : ∀ n : ℕ, 0 < k ^ n := fun n => pow_pos hk0 n
  set u : ℕ → ℝ := fun n => (s n : ℝ) ^ ((k ^ n)⁻¹) with hu
  set v : ℕ → ℝ := fun n => ((s n : ℝ) + 1) ^ ((k ^ n)⁻¹) with hv
  have hexp : ∀ n : ℕ, k * (k ^ (n + 1))⁻¹ = (k ^ n)⁻¹ := by
    intro n
    rw [pow_succ]
    field_simp [(hkn n).ne', hk0.ne']
  have hu_succ : ∀ n, u n ≤ u (n + 1) := by
    intro n
    have h1 : ((s n : ℝ) ^ k) ^ ((k ^ (n + 1))⁻¹) ≤ (s (n + 1) : ℝ) ^ ((k ^ (n + 1))⁻¹) :=
      rpow_le_rpow (rpow_nonneg (hs0 n).le _) (spec n).2.2.1.le (inv_nonneg.mpr (hkn _).le)
    rw [← rpow_mul (hs0 n).le, hexp] at h1
    exact h1
  have hv_succ : ∀ n, v (n + 1) ≤ v n := by
    intro n
    have h1 : ((s (n + 1) : ℝ) + 1) ^ ((k ^ (n + 1))⁻¹) ≤
        (((s n : ℝ) + 1) ^ k) ^ ((k ^ (n + 1))⁻¹) :=
      rpow_le_rpow (by linarith [hs0 (n + 1)]) (spec n).2.2.2.le (inv_nonneg.mpr (hkn _).le)
    rw [← rpow_mul (by linarith [hs0 n]), hexp] at h1
    exact h1
  have hv_lt : ∀ n, v (n + 1) < v n := by
    intro n
    have h1 : ((s (n + 1) : ℝ) + 1) ^ ((k ^ (n + 1))⁻¹) <
        (((s n : ℝ) + 1) ^ k) ^ ((k ^ (n + 1))⁻¹) :=
      rpow_lt_rpow (by linarith [hs0 (n + 1)]) (spec n).2.2.2 (inv_pos.mpr (hkn _))
    rw [← rpow_mul (by linarith [hs0 n]), hexp] at h1
    exact h1
  have huv : ∀ n, u n < v n := fun n =>
    rpow_lt_rpow (hs0 n).le (by linarith) (inv_pos.mpr (hkn n))
  have hu_mono : Monotone u := monotone_nat_of_le_succ hu_succ
  have hv_anti : Antitone v := antitone_nat_of_succ_le hv_succ
  have hle : ∀ n m, u n ≤ v m := by
    intro n m
    rcases le_total n m with h | h
    · exact (hu_mono h).trans (huv m).le
    · exact (huv n).le.trans (hv_anti h)
  have hbdd : BddAbove (Set.range u) := ⟨v 0, by rintro _ ⟨n, rfl⟩; exact hle n 0⟩
  set A := ⨆ n, u n with hA
  have hAu : ∀ n, u n ≤ A := fun n => le_ciSup hbdd n
  have hAv : ∀ m, A ≤ v m := fun m => ciSup_le (fun n => hle n m)
  have hAlt : ∀ n, A < v n := fun n => (hAv (n + 1)).trans_lt (hv_lt n)
  have hpow_u : ∀ n, u n ^ (k ^ n) = s n := fun n => by
    simp only [hu]
    exact rpow_inv_rpow (hs0 n).le (hkn n).ne'
  have hpow_v : ∀ n, v n ^ (k ^ n) = (s n : ℝ) + 1 := fun n => by
    simp only [hv]
    exact rpow_inv_rpow (by linarith [hs0 n]) (hkn n).ne'
  have hu0 : ∀ n, 0 ≤ u n := fun n => rpow_nonneg (hs0 n).le _
  refine ⟨A, ?_, ?_, ?_⟩
  · have := hAu 0
    simp only [hu, pow_zero, inv_one, rpow_one] at this
    simpa [hsdef, millsSeq] using this
  · have := hAlt 0
    simp only [hv, pow_zero, inv_one, rpow_one] at this
    simpa [hsdef, millsSeq] using this
  · intro n
    have hA0 : 0 ≤ A := (hu0 n).trans (hAu n)
    have hlo : (s n : ℝ) ≤ A ^ (k ^ n) := by
      rw [← hpow_u n]; exact rpow_le_rpow (hu0 n) (hAu n) (hkn n).le
    have hhi : A ^ (k ^ n) < (s n : ℝ) + 1 := by
      rw [← hpow_v n]; exact rpow_lt_rpow hA0 (hAlt n) (hkn n)
    have hfloor : ⌊A ^ (k ^ n)⌋₊ = s n := by
      rw [Nat.floor_eq_iff (rpow_nonneg hA0 _)]
      exact ⟨hlo, hhi⟩
    rw [hfloor]
    exact (spec n).1

end Construction

/-- Under QRH, the step of Mills' construction holds for every real `k ≥ 8` and every `q ≥ 1`:
a prime `p` with `q^k < p ≤ q^k + q^{k−1}`, and `q^k + q^{k−1} + 1 < q^k + k·q^{k−1} ≤ (q + 1)^k`. -/
theorem step_of_qrh (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {k : ℝ} (hk : 8 ≤ k) (q : ℕ) (hq : 1 ≤ q) :
    ∃ p : ℕ, p.Prime ∧ (q : ℝ) ^ k < p ∧ (p : ℝ) + 1 < ((q : ℝ) + 1) ^ k := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hx : (1 : ℝ) ≤ (q : ℝ) ^ k := one_le_rpow hq1 (by linarith)
  obtain ⟨p, hp, hlt, hle⟩ := global_interval hθ hD hcrit _ hx
  refine ⟨p, hp, hlt, ?_⟩
  -- (q^k)^{7/8} = q^{7k/8} ≤ q^{k−1}
  have hpow : ((q : ℝ) ^ k) ^ ((7 : ℝ) / 8) ≤ (q : ℝ) ^ (k - 1) := by
    rw [← rpow_mul hq0.le]
    exact rpow_le_rpow_of_exponent_le hq1 (by linarith)
  -- Bernoulli: (1 + 1/q)^k ≥ 1 + k/q
  have hs' : (-1 : ℝ) ≤ 1 / (q : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
    linarith
  have hbern : 1 + k * (1 / (q : ℝ)) ≤ (1 + 1 / (q : ℝ)) ^ k :=
    one_add_mul_self_le_rpow_one_add hs' (by linarith)
  have hsplit : ((q : ℝ) + 1) ^ k = (q : ℝ) ^ k * (1 + 1 / (q : ℝ)) ^ k := by
    rw [← mul_rpow hq0.le (by positivity)]
    congr 1
    field_simp
  have hqk1 : (q : ℝ) ^ k * (1 / (q : ℝ)) = (q : ℝ) ^ (k - 1) := by
    rw [rpow_sub hq0, rpow_one]; field_simp
  have hge1 : (1 : ℝ) ≤ (q : ℝ) ^ (k - 1) := one_le_rpow hq1 (by linarith)
  have hlow : (q : ℝ) ^ k + k * (q : ℝ) ^ (k - 1) ≤ ((q : ℝ) + 1) ^ k := by
    rw [hsplit, ← hqk1]
    have hqk0 : 0 ≤ (q : ℝ) ^ k := rpow_nonneg hq0.le _
    nlinarith [mul_le_mul_of_nonneg_left hbern hqk0]
  have h8 : 8 * (q : ℝ) ^ (k - 1) ≤ k * (q : ℝ) ^ (k - 1) :=
    mul_le_mul_of_nonneg_right hk (by linarith)
  have : (p : ℝ) ≤ (q : ℝ) ^ k + (q : ℝ) ^ (k - 1) := by linarith
  linarith

/-- **Mills under QRH.** For every real `k ≥ 8` and every prime `p₀` there is `A ∈ [p₀, p₀ + 1)`
such that `⌊A^{k^n}⌋` is prime for every `n ≥ 0`. -/
theorem mills_qrh (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {k : ℝ} (hk : 8 ≤ k) {p₀ : ℕ} (hp₀ : p₀.Prime) :
    ∃ A : ℝ, (p₀ : ℝ) ≤ A ∧ A < p₀ + 1 ∧ ∀ n : ℕ, (⌊A ^ (k ^ n)⌋₊).Prime :=
  mills_of_step (by linarith) hp₀
    (fun q hq => step_of_qrh hθ hD hcrit hk q (hp₀.one_lt.le.trans hq))

/-- The exponent `8`, with natural powers: there is `A ∈ [2, 3)` with `⌊A^{8^n}⌋` prime for all `n`
(`2, 257, 19031147999601100901, …` for the least choices). -/
theorem mills_eight (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∃ A : ℝ, 2 ≤ A ∧ A < 3 ∧ ∀ n : ℕ, (⌊A ^ (8 ^ n : ℕ)⌋₊).Prime := by
  obtain ⟨A, h1, h2, h3⟩ := mills_qrh hθ hD hcrit (k := 8) le_rfl Nat.prime_two
  refine ⟨A, by exact_mod_cast h1, by norm_num at h2; linarith, fun n => ?_⟩
  have := h3 n
  have hA0 : 0 ≤ A := by norm_num at h1; linarith
  rwa [show ((8 : ℝ) ^ n) = (((8 ^ n : ℕ)) : ℝ) by push_cast; rfl, rpow_natCast] at this

end QRHGlobal
