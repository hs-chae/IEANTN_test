/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticOptimizedCertified
import PrimeQuantiles

/-! Exact count/width tradeoff and genuinely open prime-index consumers.
These are consequences of the frozen octic theorem, not a new Fourier kernel.
The published comparison concerns displayed asymptotic upper-bound curves only.
-/
noncomputable section
namespace RHOnePrime.Frontier
open Real Set Finset
set_option maxHeartbeats 0

def widthFor (α : ℝ) : ℝ := 163827 / 160000 + 9 / 8 * α
def chirreWidth (α : ℝ) : ℝ := 4179 / 5000 * (1 + 2 * α)
def allowance (C x : ℝ) : ℝ :=
  (8 / 9 * C - 18203 / 20000 + (21 / 5) / log x) * sqrt x

theorem exact_frontier_coefficient (α : ℝ) :
    (8 / 9 : ℝ) * widthFor α - 18203 / 20000 = α := by
  unfold widthFor
  ring

/-- Exact crossing of the two displayed width curves; not a claim that either
published infimum upper bound is an optimal attainable constant. -/
theorem displayed_curve_comparison (α : ℝ) :
    widthFor α < chirreWidth α ↔ 10033 / 29152 < α := by
  unfold widthFor chirreWidth
  constructor <;> intro h <;> linarith

theorem displayed_curve_equality :
    widthFor (10033 / 29152) = chirreWidth (10033 / 29152) := by
  norm_num [widthFor, chirreWidth]

/-- An explicit positive limiting margin requires ε>0. At ε=0 the finite
strict count is still proved, but it does not imply liminf>α. -/
theorem count_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {α ε : ℝ}
    (hC : widthFor (α + ε) ∈ Icc (103 / 100 : ℝ) 16)
    {x : ℝ} (hx : exp 24 ≤ x) :
    (α + ε + (21 / 5) / log x) * sqrt x <
      ((QuarticWindow.primesBetween x
        (x + widthFor (α + ε) * sqrt x * log x)).card : ℝ) := by
  have h := RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh
    (widthFor (α + ε)) hC x hx
  rw [exact_frontier_coefficient] at h
  exact h

/-- The strict-open finite count actually locates the index strictly below
the upper endpoint. This strengthens the old closed-upper quantile adapter. -/
theorem quantile_open_of_card {x y : ℝ} (hx : 0 ≤ x) {m : ℕ}
    (hc : (m : ℝ) < ((QuarticWindow.primesBetween x y).card : ℝ)) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) < y := by
  classical
  let s := QuarticWindow.primesBetween x y
  have hcard : 0 < s.card := by
    have hm : (0 : ℝ) ≤ m := by positivity
    have hc' : (0 : ℝ) < (s.card : ℝ) := by dsimp [s]; linarith
    exact_mod_cast hc'
  have hs : s.Nonempty := Finset.card_pos.mp hcard
  let p := s.max' hs
  have hp : p ∈ s := Finset.max'_mem s hs
  have hxp : x < (p : ℝ) := (Finset.mem_filter.mp hp).2.1
  have hpy : (p : ℝ) < y := (Finset.mem_filter.mp hp).2.2
  let z : ℝ := ((p : ℝ) + y) / 2
  have hpz : (p : ℝ) < z := by dsimp [z]; linarith
  have hzy : z < y := by dsimp [z]; linarith
  have hxz : x ≤ z := (hxp.trans hpz).le
  have hsub : s ⊆ QuarticWindow.primesBetween x z := by
    intro q hq
    have hqp : q ≤ p := Finset.le_max' s q hq
    have hqz : (q : ℝ) < z :=
      (by exact_mod_cast hqp : (q : ℝ) ≤ (p : ℝ)).trans_lt hpz
    have hprime : q.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hq).1).2
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr
      ⟨Nat.le_floor hqz.le, hprime⟩, (Finset.mem_filter.mp hq).2.1, hqz⟩
  have hcount : (m : ℝ) < QuarticWindow.primeCounting z -
      QuarticWindow.primeCounting x := by
    have hle : (s.card : ℝ) ≤
        ((QuarticWindow.primesBetween x z).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    exact (hc.trans_le hle).trans_le
      (QuarticWindow.count_le_primeCounting_difference hx hxz)
  obtain ⟨hl, hu⟩ := RHContinuation.PrimeQuantiles.quantile_from_count hx hxz hcount
  exact ⟨hl, hu.trans_lt hzy⟩

theorem prime_block_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {C x : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hx : exp 24 ≤ x)
    {m : ℕ} (hm : (m : ℝ) ≤ allowance C x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + C * sqrt x * log x := by
  apply quantile_open_of_card ((exp_pos 24).le.trans hx)
  exact hm.trans_lt (RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh C hC x hx)

/-- Pointwise shortest width licensed by the frozen affine count estimate,
subject to its original [1.03,16] domain. No out-of-domain substitution. -/
def indexWidth (m : ℕ) (x : ℝ) : ℝ :=
  widthFor ((m : ℝ) / sqrt x - (21 / 5) / log x)

theorem exact_index_allowance {x : ℝ} (hx : 0 < x) (m : ℕ) :
    allowance (indexWidth m x) x = m := by
  have hs : sqrt x ≠ 0 := (sqrt_pos.mpr hx).ne'
  unfold allowance indexWidth
  rw [exact_frontier_coefficient]
  field_simp
  <;> ring

theorem pointwise_index_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x) (m : ℕ)
    (hC : indexWidth m x ∈ Icc (103 / 100 : ℝ) 16) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + indexWidth m x * sqrt x * log x := by
  apply prime_block_frontier hG hN hB rh hC hx
  rw [exact_index_allowance ((exp_pos 24).trans_le hx)]

/-- Clamp to the genuinely proved kernel domain. For small index targets the
raw affine inversion lies below1.03, where substitution is not licensed. -/
def clampedIndexWidth (m : ℕ) (x : ℝ) : ℝ := max (103 / 100) (indexWidth m x)

theorem clamped_index_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x) (m : ℕ)
    (hC : clampedIndexWidth m x ≤ 16) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + clampedIndexWidth m x * sqrt x * log x := by
  have hlow : (103 / 100 : ℝ) ≤ clampedIndexWidth m x := le_max_left _ _
  apply prime_block_frontier hG hN hB rh ⟨hlow, hC⟩ hx
  have hwidth : indexWidth m x ≤ clampedIndexWidth m x := le_max_right _ _
  have hmono : allowance (indexWidth m x) x ≤ allowance (clampedIndexWidth m x) x := by
    unfold allowance
    apply mul_le_mul_of_nonneg_right _ (sqrt_nonneg x)
    linarith
  rw [exact_index_allowance ((exp_pos 24).trans_le hx)] at hmono
  exact hmono

theorem allowance_nonneg {C x : ℝ} (hC : (103 / 100 : ℝ) ≤ C)
    (hx : exp 24 ≤ x) : 0 ≤ allowance C x := by
  have hx1 : 1 ≤ x := (one_le_exp (by norm_num : (0 : ℝ) ≤ 24)).trans hx
  have hl : 0 ≤ log x := log_nonneg hx1
  have hlead : 0 ≤ 8 / 9 * C - 18203 / 20000 := by linarith
  unfold allowance
  positivity

/-- The maximal integer target licensed by the entire count margin is used,
including the logarithmic contribution, with both prime endpoints strict. -/
theorem maximal_certified_block
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {C x : ℝ}
    (hC : C ∈ Icc (103 / 100 : ℝ) 16) (hx : exp 24 ≤ x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + ⌊allowance C x⌋₊) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + ⌊allowance C x⌋₊) : ℝ) <
        x + C * sqrt x * log x :=
  prime_block_frontier hG hN hB rh hC hx (Nat.floor_le (allowance_nonneg hC.1 hx))

/-- The specialized2.15 proof has a stronger logarithmic count contribution
than the generic family at the same width, and must be retained separately. -/
def specialAllowance (x : ℝ) : ℝ :=
  (180173 / 180000 + (29 / 5) / log x) * sqrt x

theorem special_prime_block_open
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x) {m : ℕ}
    (hm : (m : ℝ) ≤ specialAllowance x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + (43 / 20) * sqrt x * log x := by
  apply quantile_open_of_card ((exp_pos 24).le.trans hx)
  exact hm.trans_lt (RHOcticPush.OptimizedFinal.strict_count_215 hG hN hB rh x hx)

def effectiveIndexWidth (m : ℕ) (x : ℝ) : ℝ :=
  if (m : ℝ) ≤ specialAllowance x then min (clampedIndexWidth m x) (43 / 20)
  else clampedIndexWidth m x

/-- The effective index frontier uses the shorter applicable width. In the
entire old specialized block it never enlarges the certified interval. -/
theorem effective_index_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x) (m : ℕ)
    (hC : clampedIndexWidth m x ≤ 16) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + effectiveIndexWidth m x * sqrt x * log x := by
  obtain ⟨hl, hnew⟩ := clamped_index_frontier hG hN hB rh hx m hC
  refine ⟨hl, ?_⟩
  unfold effectiveIndexWidth
  split_ifs with hm
  · have hold := (special_prime_block_open hG hN hB rh hx hm).2
    by_cases hshort : clampedIndexWidth m x ≤ 43 / 20
    · simpa only [min_eq_left hshort] using hnew
    · simpa only [min_eq_right (le_of_not_ge hshort)] using hold
  · exact hnew

theorem retains_special_width {m : ℕ} {x : ℝ}
    (hm : (m : ℝ) ≤ specialAllowance x) : effectiveIndexWidth m x ≤ 43 / 20 := by
  simp only [effectiveIndexWidth, if_pos hm]
  exact min_le_right _ _

/-- Recover the positive logarithmic count term as an additive shortening of
the actual forward window, instead of discarding it in a fixed-width corollary. -/
def populationWidth (α x : ℝ) : ℝ := widthFor (α - (21 / 5) / log x)

theorem shifted_population_frontier
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {α x : ℝ} (hx : exp 24 ≤ x)
    (hC : populationWidth α x ∈ Icc (103 / 100 : ℝ) 16) :
    α * sqrt x < ((QuarticWindow.primesBetween x
      (x + populationWidth α x * sqrt x * log x)).card : ℝ) := by
  have h := RHOcticPush.OptimizedFinal.strict_count_family hG hN hB rh
    (populationWidth α x) hC x hx
  have hc : 8 / 9 * populationWidth α x - 18203 / 20000 +
      (21 / 5) / log x = α := by
    unfold populationWidth widthFor
    ring
  rwa [hc] at h

lemma population_one_width_domain {x : ℝ} (hx : exp 24 ≤ x) :
    populationWidth 1 x ∈ Icc (103 / 100 : ℝ) 16 := by
  have hl : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
  have hlpos : 0 < log x := by linarith
  have hq : 0 ≤ (21 / 5 : ℝ) / log x := by positivity
  have hqu : (21 / 5 : ℝ) / log x ≤ 7 / 40 :=
    (div_le_iff₀ hlpos).mpr (by nlinarith)
  unfold populationWidth widthFor
  constructor <;> linarith

lemma population_one_window_identity {x : ℝ} (hx : exp 24 ≤ x) :
    x + populationWidth 1 x * sqrt x * log x =
      x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x := by
  have hl : 0 < log x := by
    have h : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
    linarith
  unfold populationWidth widthFor
  field_simp
  <;> ring

theorem rich_shifted_window
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x) :
    sqrt x < ((QuarticWindow.primesBetween x
      (x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x)).card : ℝ) := by
  have h := shifted_population_frontier hG hN hB rh hx (population_one_width_domain hx)
  rw [population_one_window_identity hx] at h
  simpa using h

theorem shifted_window_strictly_shorter {x : ℝ} (hx : exp 24 ≤ x) :
    x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x <
      x + (343827 / 160000) * sqrt x * log x := by
  have hs : 0 < sqrt x := sqrt_pos.mpr ((exp_pos 24).trans_le hx)
  nlinarith

theorem shifted_sqrt_block
    (hG : RHOcticPush.GreenSource.SourceGreenSmooth)
    (hN : NicolasContinuation.SourceNicolas119)
    (hB : RHOcticPush.BPTSourceEndpoint.SourceBPTOffOrdinate)
    (rh : RiemannHypothesis) {x : ℝ} (hx : exp 24 ≤ x)
    {m : ℕ} (hm : (m : ℝ) ≤ sqrt x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) <
        x + (343827 / 160000) * sqrt x * log x - (189 / 40) * sqrt x := by
  apply quantile_open_of_card ((exp_pos 24).le.trans hx)
  exact hm.trans_lt (rich_shifted_window hG hN hB rh hx)

#print axioms count_frontier
#print axioms quantile_open_of_card
#print axioms prime_block_frontier
#print axioms pointwise_index_frontier
#print axioms clamped_index_frontier
#print axioms maximal_certified_block
#print axioms special_prime_block_open
#print axioms effective_index_frontier
#print axioms rich_shifted_window
#print axioms shifted_sqrt_block
end RHOnePrime.Frontier
