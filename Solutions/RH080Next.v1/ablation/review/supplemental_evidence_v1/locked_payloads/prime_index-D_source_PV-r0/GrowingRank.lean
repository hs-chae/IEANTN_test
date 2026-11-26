import RH080EstimatePack
import PopulationActualConsumers
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Filter Real IEANTN.CMSFunctional

namespace GrowingRank

def P (n : ℕ) : ℝ := primeAt n
def scale (n : ℕ) : ℝ := sqrt (P n) * log (P n)
def gap (n j : ℕ) : ℝ := P (n+j) - P n
def cap (n : ℕ) (β : ℝ) : ℕ := ⌊β*sqrt (P n)⌋₊ + 1

theorem two_le_P (n : ℕ) : 2 ≤ P n := by
  have hh := Nat.add_two_le_nth_prime n
  have h : 2 ≤ Nat.nth Nat.Prime n := by omega
  unfold P primeAt
  exact_mod_cast h

theorem sqrt_P_pos (n : ℕ) : 0 < sqrt (P n) :=
  Real.sqrt_pos.2 (lt_of_lt_of_le (by norm_num) (two_le_P n))

theorem scale_pos (n : ℕ) : 0 < scale n :=
  mul_pos (sqrt_P_pos n) (Real.log_pos (lt_of_lt_of_le (by norm_num) (two_le_P n)))

theorem primeAt_strictMono : StrictMono primeAt :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem P_strictMono : StrictMono P := by
  intro a b hab
  unfold P
  exact_mod_cast primeAt_strictMono hab

theorem P_atTop : Tendsto P atTop atTop := by
  refine tendsto_atTop.2 fun b => eventually_atTop.2 ⟨⌈b⌉₊, ?_⟩
  intro n hn
  have h : n ≤ Nat.nth Nat.Prime n := (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)
  have hc : (n : ℝ) ≤ P n := by unfold P primeAt; exact_mod_cast h
  exact (Nat.le_ceil b).trans ((Nat.cast_le.mpr hn).trans hc)

theorem piReal_P (n : ℕ) : piReal (P n) = n+1 := by
  unfold piReal P primeAt
  rw [Nat.floor_natCast]
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

theorem le_iff_index_lt_count {m : ℕ} {y : ℝ} (hy : 0 ≤ y) :
    P m ≤ y ↔ m < piReal y := by
  unfold P primeAt piReal Nat.primeCounting Nat.primeCounting'
  rw [← Nat.le_floor_iff hy, ← Nat.lt_succ_iff]
  exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).symm

def piStrict (y : ℝ) : ℕ := Nat.primeCounting' ⌈y⌉₊

theorem lt_iff_index_lt_count {m : ℕ} {y : ℝ} :
    P m < y ↔ m < piStrict y := by
  unfold P primeAt piStrict Nat.primeCounting'
  rw [← Nat.lt_ceil]
  exact (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).symm

theorem halfOpen_bridge {n j : ℕ} {y : ℝ} (hy : P n ≤ y) :
    P (n+j) ≤ y ↔ j ≤ piReal y - (n+1) := by
  have hy0 : 0 ≤ y := (by linarith [two_le_P n] : (0 : ℝ) ≤ P n).trans hy
  have hn := (le_iff_index_lt_count hy0).1 hy
  rw [le_iff_index_lt_count hy0]
  omega

theorem strictOpen_bridge {n j : ℕ} {y : ℝ} (hj : 1 ≤ j) :
    P n < P (n+j) ∧ P (n+j) < y ↔ j ≤ piStrict y - (n+1) := by
  have h : P n < P (n+j) := P_strictMono (by omega)
  rw [and_iff_right h, lt_iff_index_lt_count]
  omega

theorem strict_of_spare {n j : ℕ} {y : ℝ} (hy : P n ≤ y)
    (h : j < piReal y - (n+1)) : P (n+j) < y :=
  (P_strictMono (show n+j < n+(j+1) by omega)).trans_le
    ((halfOpen_bridge hy).2 (by omega))

/-- Quantitative bonus: the count margin gives also a positive additive saving
of order sqrt(p_n), uniformly on the fixed cap, without an effective constant. -/
theorem good_transport {β c : ℝ} (hβ : 0 ≤ β) (h : GoodCoefficient β c) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap n β →
      0 < gap n j ∧ gap n j < c * scale n - κ * sqrt (P n) := by
  obtain ⟨hc, δ, hδ, hcount⟩ := h
  have hs := Real.tendsto_sqrt_atTop.comp P_atTop
  have hm : ∀ᶠ n : ℕ in atTop, 2 < sqrt (P n) * δ :=
    (hs.atTop_mul_const hδ).eventually_gt_atTop 2
  refine ⟨δ/2, by linarith, ?_⟩
  have ht : ∀ᶠ n : ℕ in atTop, β+δ ≤ normalizedPopulation c (P n) :=
    P_atTop.eventually hcount
  filter_upwards [ht, hm] with n hcnt hmargin j hj hjcap
  have hp := sqrt_P_pos n
  let y := P n + c*sqrt (P n)*log (P n)
  have hPy : P n ≤ y := by
    dsimp [y]
    have hh : 0 < c * sqrt (P n) * log (P n) :=
      mul_pos (mul_pos hc hp) (Real.log_pos (by linarith [two_le_P n]))
    linarith
  let k := piReal y - (n+1)
  have hpop : (β+δ)*sqrt (P n) ≤ (k : ℝ) := by
    have hh : β+δ ≤ (halfOpenCount c (P n) : ℝ) / sqrt (P n) := hcnt
    have hk : halfOpenCount c (P n) = k := by
      unfold halfOpenCount k y
      rw [piReal_P]
    rw [hk] at hh
    exact (le_div_iff₀ hp).1 hh
  have hjR : (j : ℝ) ≤ β*sqrt (P n)+1 := by
    have hl : (j : ℝ) ≤ (cap n β : ℝ) := by exact_mod_cast hjcap
    have hf := Nat.floor_le (mul_nonneg hβ hp.le)
    unfold cap at hl
    rw [Nat.cast_add, Nat.cast_one] at hl
    linarith
  have hextra : δ/2 * sqrt (P n) < (k : ℝ) - j := by
    rw [mul_comm] at hmargin
    linarith [hpop, hjR]
  have hjk : j ≤ k := by
    suffices h : (j : ℝ) ≤ (k : ℝ) by exact_mod_cast h
    have hh := mul_nonneg (show 0 ≤ δ/2 by linarith) hp.le
    linarith
  have hp_k : P (n+k) ≤ y := (halfOpen_bridge hPy).2 le_rfl
  have hd : (k : ℝ) - j ≤ P (n+k) - P (n+j) := by
    have hh := primeAt_strictMono.add_le_nat (k-j) (n+j)
    rw [show (k-j)+(n+j) = n+k by omega] at hh
    have hhR : (↑(k-j) : ℝ) + P (n+j) ≤ P (n+k) := by
      unfold P
      exact_mod_cast hh
    rw [Nat.cast_sub hjk] at hhR
    linarith
  constructor
  · exact sub_pos.mpr (P_strictMono (by omega))
  · unfold gap scale
    dsimp [y] at hp_k
    rw [mul_assoc] at hp_k
    linarith

def G (t : ℝ) : ℝ := (20582561296/24680948495 : ℝ)*(1+2*t)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine

def envelope (t : ℝ) : ℝ := min (G t) (min (S t) (F t))
def envelopeSlack (t ε : ℝ) : ℝ := min (G t+ε) (min (S t) (F t))

def Bound (β c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap n β →
    0 < gap n j ∧ gap n j < c * scale n

theorem good_to_bound {β c : ℝ} (hβ : 0 ≤ β) (hc : GoodCoefficient β c) :
    Bound β c := by
  obtain ⟨κ, hκ, h⟩ := good_transport hβ hc
  filter_upwards [h] with n hn j hj hcap
  obtain ⟨h0, hu⟩ := hn j hj hcap
  exact ⟨h0, hu.trans (sub_lt_self _ (mul_pos hκ (sqrt_P_pos n)))⟩

theorem bound_min {β a b : ℝ} (ha : Bound β a) (hb : Bound β b) : Bound β (min a b) := by
  filter_upwards [ha, hb] with n hna hnb j hj hcap
  rcases le_total a b with hab|hba
  · simpa only [min_eq_left hab] using hna j hj hcap
  · simpa only [min_eq_right hba] using hnb j hj hcap

theorem gaussian_bound (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    Bound β (G β+ε) :=
  good_to_bound hβ (RH080Exposure.Estimates.gaussian hCMS hRH β hβ ε hε)

theorem br_bound_kernel (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {β : ℝ} (hβ : 0 ≤ β) : Bound β (min (S β) (F β)) :=
  bound_min (good_to_bound hβ (RH080Exposure.Estimates.sparse hNorm hUniform hRH β hβ))
    (good_to_bound hβ (RH080Exposure.Estimates.flat hNorm hUniform hRH β hβ))

theorem br_bound_source (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {β : ℝ} (hβ : 0 ≤ β) : Bound β (min (S β) (F β)) :=
  bound_min (good_to_bound hβ
    (RH080Next.PopulationCanonical.source_first_sparse_curve hNorm hUniform hRH β hβ))
    (good_to_bound hβ
      (RH080Next.PopulationCanonical.source_first_flat_curve hNorm hUniform hRH β hβ))

theorem fixed_cap_kernel (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) : Bound β (envelopeSlack β ε) :=
  bound_min (gaussian_bound hCMS hRH hβ hε) (br_bound_kernel hNorm hUniform hRH hβ)

theorem fixed_cap_source_BR (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) : Bound β (envelopeSlack β ε) :=
  bound_min (gaussian_bound hCMS hRH hβ hε) (br_bound_source hNorm hUniform hRH hβ)

#print axioms halfOpen_bridge
#print axioms strictOpen_bridge
#print axioms good_transport
#print axioms fixed_cap_kernel
#print axioms fixed_cap_source_BR
end GrowingRank
