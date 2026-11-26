import RH080EstimatePack
import Mathlib.Data.Nat.Prime.Nth

namespace RankTransfer

open Filter IEANTN.CMSFunctional
open scoped Filter
noncomputable section

abbrev p (n : ℕ) : ℕ := Nat.nth Nat.Prime n
abbrev P (n : ℕ) : ℝ := (p n : ℝ)
def scale (x : ℝ) := Real.sqrt x * Real.log x
def gap (n j : ℕ) := P (n+j) - P n

theorem prime_strict : StrictMono p :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem P_two (n : ℕ) : 2 ≤ P n := by
  exact_mod_cast (Nat.prime_nth_prime n).two_le

theorem scale_pos (n : ℕ) : 0 < scale (P n) := by
  have h := P_two n
  exact mul_pos (Real.sqrt_pos.2 (by linarith)) (Real.log_pos (by linarith))

theorem pi_at_prime (n : ℕ) : piReal (P n) = n+1 := by
  unfold piReal Nat.primeCounting Nat.primeCounting'
  simp only [Nat.floor_natCast, Nat.count_succ, Nat.prime_nth_prime, ite_true]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)

theorem le_iff_pi (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    P k ≤ y ↔ k+1 ≤ piReal y := by
  constructor
  · intro hk
    rw [← pi_at_prime k]
    exact Nat.monotone_primeCounting (Nat.floor_natCast (R := ℝ) (p k) ▸ Nat.le_floor hk)
  · intro hk
    have hk' : k < Nat.count Nat.Prime (⌊y⌋₊ + 1) := by
      change k+1 ≤ Nat.count Nat.Prime (⌊y⌋₊ + 1) at hk
      omega
    have hk'' : p k ≤ ⌊y⌋₊ := Nat.lt_succ_iff.mp (Nat.nth_lt_of_lt_count hk')
    exact (Nat.cast_le.mpr hk'').trans (Nat.floor_le hy)

theorem halfOpen_order (n j : ℕ) {y : ℝ} (hy : P n ≤ y) :
    P (n+j) ≤ y ↔ j ≤ piReal y - piReal (P n) := by
  have hy0 : 0 ≤ y := (by linarith [P_two n] : 0 ≤ P n).trans hy
  have hn := (le_iff_pi n hy0).mp hy
  rw [le_iff_pi (n+j) hy0, pi_at_prime]
  omega

/-- Number of positive primes strictly below y (for y ≥ 0). -/
def piStrict (y : ℝ) := Nat.count Nat.Prime ⌈y⌉₊

theorem lt_iff_piStrict (k : ℕ) (y : ℝ) :
    P k < y ↔ k+1 ≤ piStrict y := by
  rw [← not_le, ← Nat.ceil_le, not_le]
  unfold piStrict
  rw [← not_le, ← Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime, not_le]
  change k < Nat.count Nat.Prime ⌈y⌉₊ ↔ _
  omega

theorem strictOpen_order (n j : ℕ) {y : ℝ} (hy : P n < y) :
    P (n+j) < y ↔ j ≤ piStrict y - piReal (P n) := by
  have hn := (lt_iff_piStrict n y).mp hy
  rw [lt_iff_piStrict, pi_at_prime]
  omega

theorem spare_rank_open (n j : ℕ) {y : ℝ} (hy : P n ≤ y)
    (h : j+1 ≤ piReal y - piReal (P n)) : P (n+j) < y := by
  have h' := (halfOpen_order n (j+1) hy).mpr h
  have hs : P (n+j) < P (n+(j+1)) := by
    exact_mod_cast prime_strict (show n+j < n+(j+1) by omega)
  exact hs.trans_le h'

def Bound (β c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β * Real.sqrt (P n)⌋₊ + 1 →
    0 < gap n j ∧ gap n j < c * scale (P n)

/-- A fixed positive population margin absorbs the extra endpoint rank as well
as any fixed number m of further ranks. -/
theorem margin_transport {β c : ℝ} (hβ : 0 ≤ β) (hc : GoodCoefficient β c) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      j ≤ ⌊β * Real.sqrt (P n)⌋₊ + 1 + m →
      0 < gap n j ∧ gap n j < c * scale (P n) := by
  obtain ⟨hc, δ, hδ, hX⟩ := hc
  obtain ⟨X, hX⟩ := eventually_atTop.mp hX
  let a : ℝ := ((m : ℝ) + 2) / δ
  have ha : 0 ≤ a := by dsimp [a]; positivity
  apply eventually_atTop.mpr
  refine ⟨⌈max X (a^2)⌉₊, ?_⟩
  intro n hn j hj hjmax
  have hn' : max X (a^2) ≤ P n :=
    (Nat.ceil_le.mp hn).trans (by exact_mod_cast (prime_strict.id_le n))
  have hX' := hX (P n) ((le_max_left _ _).trans hn')
  have hs : 0 < Real.sqrt (P n) := Real.sqrt_pos.2 (by linarith [P_two n])
  have hds : (m : ℝ) + 2 ≤ δ * Real.sqrt (P n) := by
    have h := (Real.le_sqrt ha (by linarith [P_two n])).2 ((le_max_right _ _).trans hn')
    dsimp [a] at h
    rw [div_le_iff₀ hδ] at h
    simpa [mul_comm] using h
  let y := P n + c * scale (P n)
  have hy : P n ≤ y := by
    dsimp [y]; linarith [mul_pos hc (scale_pos n)]
  unfold normalizedPopulation halfOpenCount at hX'
  rw [mul_assoc] at hX'
  change β + δ ≤ (↑(piReal y - piReal (P n)) : ℝ) / Real.sqrt (P n) at hX'
  have hpop := (le_div_iff₀ hs).mp hX'
  have hf := Nat.floor_le (mul_nonneg hβ hs.le)
  have hjmax' : (j : ℝ) ≤ ↑⌊β * Real.sqrt (P n)⌋₊ + 1 + (m : ℝ) := by
    exact_mod_cast hjmax
  have hspare' : (j : ℝ) + 1 ≤ ↑(piReal y - piReal (P n)) := by
    linarith only [hpop, hds, hf, hjmax', add_mul β δ (Real.sqrt (P n))]
  have hspare : j+1 ≤ piReal y - piReal (P n) := by exact_mod_cast hspare'
  have hl := spare_rank_open n j hy hspare
  have hs' : P n < P (n+j) := by
    exact_mod_cast prime_strict (show n < n+j by omega)
  exact ⟨by unfold gap; linarith, by unfold gap; dsimp [y] at hl; linarith⟩

theorem from_good {β c : ℝ} (hβ : 0 ≤ β) (hc : GoodCoefficient β c) : Bound β c := by
  simpa [Bound] using margin_transport hβ hc 0

abbrev G (t : ℝ) : ℝ := 20582561296 / 24680948495 * (1+2*t)
abbrev B := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine

theorem gaussian (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) : Bound β (G β + ε) :=
  from_good hβ (RH080Exposure.Estimates.gaussian hCMS hRH β hβ ε hε)

theorem sparse (hRH : RiemannHypothesis)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β : ℝ} (hβ : 0 ≤ β) : Bound β (B β) :=
  from_good hβ (RH080Exposure.Estimates.sparse hNorm hUniform hRH β hβ)

theorem flat (hRH : RiemannHypothesis)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β : ℝ} (hβ : 0 ≤ β) : Bound β (F β) :=
  from_good hβ (RH080Exposure.Estimates.flat hNorm hUniform hRH β hβ)

theorem bound_min {β c d : ℝ} (hc : Bound β c) (hd : Bound β d) : Bound β (min c d) := by
  filter_upwards [hc, hd] with n hc hd
  intro j hj hjmax
  rw [min_mul_of_nonneg _ _ (scale_pos n).le, lt_min_iff]
  exact ⟨(hc j hj hjmax).1, (hc j hj hjmax).2, (hd j hj hjmax).2⟩

theorem br (hRH : RiemannHypothesis)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β : ℝ} (hβ : 0 ≤ β) : Bound β (min (B β) (F β)) :=
  bound_min (sparse hRH hNorm hUniform hβ) (flat hRH hNorm hUniform hβ)

theorem envelope (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) : Bound β (min (G β + ε) (min (B β) (F β))) :=
  bound_min (gaussian hRH hCMS hβ hε) (br hRH hNorm hUniform hβ)


/-- Exact correction for the upper endpoint of the strict-open count. -/
theorem pi_endpoint {y : ℝ} (hy : 0 ≤ y) :
    piReal y = piStrict y + if y = (⌊y⌋₊ : ℝ) ∧ Nat.Prime ⌊y⌋₊ then 1 else 0 := by
  by_cases h : y = (⌊y⌋₊ : ℝ)
  · have he : ⌈y⌉₊ = ⌊y⌋₊ := by
      apply le_antisymm (Nat.ceil_le.mpr h.le) (Nat.floor_le_ceil y)
    unfold piReal piStrict Nat.primeCounting Nat.primeCounting'
    rw [he, Nat.count_succ]
    simp only [eq_true h, true_and]
  · have he : ⌈y⌉₊ = ⌊y⌋₊+1 := by
      have ha := Nat.floor_le_ceil y
      have hb := Nat.ceil_le_floor_add_one y
      have hn : ⌈y⌉₊ ≠ ⌊y⌋₊ := by
        intro he
        apply h
        exact le_antisymm (he ▸ Nat.le_ceil y) (Nat.floor_le hy)
      omega
    unfold piReal piStrict
    have hc : (if y = (⌊y⌋₊ : ℝ) ∧ Nat.Prime ⌊y⌋₊ then 1 else 0) = (0 : ℕ) :=
      by simp only [eq_false (show ¬(y = (⌊y⌋₊ : ℝ) ∧ Nat.Prime ⌊y⌋₊) from fun hp => h hp.1), ite_false]
    rw [he, Nat.primeCounting_eq_primeCounting'_succ, hc, Nat.add_zero]
    rfl

/-- Lift fixed-parameter bounds to a uniform bound at the individual rank. -/
def Profile (β : ℝ) (E : ℝ → ℝ) (η : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β * Real.sqrt (P n)⌋₊ + 1 →
    0 < gap n j ∧ gap n j < (E (((j : ℝ)-1) / Real.sqrt (P n)) + η) * scale (P n)

theorem uniformize {E : ℝ → ℝ} {L β η : ℝ} (hL : 0 ≤ L) (hβ : 0 ≤ β) (hη : 0 < η)
    (hlip : ∀ t u : ℝ, t ≤ u → E u ≤ E t + L*(u-t))
    (hb : ∀ u : ℝ, 0 ≤ u → ∀ e : ℝ, 0 < e → Bound u (E u + e)) :
    Profile β E η := by
  let d : ℝ := η / (2*(L+1))
  have hd : 0 < d := div_pos hη (by linarith)
  have hLd : L * d ≤ η / 2 := by
    have he : (L+1)*d = η/2 := by
      dsimp [d]
      field_simp [show L+1 ≠ 0 by linarith]
    linarith only [he, hd, add_mul L 1 d, one_mul d]
  have hh : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (⌈β/d⌉₊+1),
      ∀ j : ℕ, 1 ≤ j → j ≤ ⌊((i : ℕ) : ℝ)*d * Real.sqrt (P n)⌋₊ + 1 →
        0 < gap n j ∧ gap n j < (E (((i : ℕ) : ℝ)*d) + η/2)*scale (P n) :=
    eventually_all.mpr (fun i => hb _ (mul_nonneg (Nat.cast_nonneg _) hd.le) _ (by linarith))
  filter_upwards [hh] with n hh
  intro j hj hjmax
  let s := Real.sqrt (P n)
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith [P_two n])
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  let t := ((j : ℝ)-1)/s
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hj') hs.le
  have htβ : t ≤ β := by
    apply (div_le_iff₀ hs).mpr
    have hf : j-1 ≤ ⌊β*s⌋₊ := by dsimp [s]; omega
    have hf' := (Nat.cast_le.mpr hf : ((j-1 : ℕ) : ℝ) ≤ ↑⌊β*s⌋₊)
    rw [Nat.cast_sub hj, Nat.cast_one] at hf'
    exact hf'.trans (Nat.floor_le (mul_nonneg hβ hs.le))
  let i : Fin (⌈β/d⌉₊+1) := ⟨⌈t/d⌉₊, Nat.lt_succ_of_le
    (Nat.ceil_le.mpr ((div_le_div_of_nonneg_right htβ hd.le).trans (Nat.le_ceil _)))⟩
  let u := ((i : ℕ) : ℝ)*d
  have htu : t ≤ u :=
    (div_le_iff₀ hd).mp (Nat.le_ceil (t/d))
  have hut : u < t+d := by
    have he := (lt_div_iff₀ hd).mp
      (show (⌈t/d⌉₊ : ℝ) < (t+d)/d by
        rw [add_div, div_self hd.ne']
        exact Nat.ceil_lt_add_one (div_nonneg ht hd.le))
    exact he
  have hj'': j ≤ ⌊u*s⌋₊ + 1 := by
    have ht' := (div_le_iff₀ hs).mp htu
    have hh' : ((j-1 : ℕ) : ℝ) ≤ u*s := by simpa [Nat.cast_sub hj] using ht'
    have hfloor := Nat.le_floor hh'
    omega
  obtain ⟨hpos, hg⟩ := hh i j hj hj''
  have hE : E u + η/2 ≤ E t + η := by
    have h := mul_le_mul_of_nonneg_left (show u-t ≤ d by linarith) hL
    linarith only [hlip t u htu, h, hLd]
  exact ⟨hpos, hg.trans_le (mul_le_mul_of_nonneg_right hE (scale_pos n).le)⟩


theorem open_count_endpoint (n : ℕ) {y : ℝ} (hy : P n < y) :
    piReal y - piReal (P n) = (piStrict y - piReal (P n)) +
      if y = (⌊y⌋₊ : ℝ) ∧ Nat.Prime ⌊y⌋₊ then 1 else 0 := by
  have hle : piReal (P n) ≤ piStrict y := by
    rw [pi_at_prime]
    exact (lt_iff_piStrict n y).mp hy
  have hy0 : 0 ≤ y := by linarith [P_two n]
  rw [pi_endpoint hy0]
  omega

def lines (t : ℝ) := min (G t) (min (B t) (F t))
def brLines (t : ℝ) := min (B t) (F t)

theorem bound_mono {β c d : ℝ} (h : c ≤ d) (hb : Bound β c) : Bound β d := by
  filter_upwards [hb] with n hb
  intro j hj hjmax
  exact ⟨(hb j hj hjmax).1,
    (hb j hj hjmax).2.trans_le (mul_le_mul_of_nonneg_right h (scale_pos n).le)⟩

theorem envelope_perturbed (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β e : ℝ} (hβ : 0 ≤ β) (he : 0 < e) : Bound β (lines β+e) := by
  apply bound_mono _ (envelope hRH hCMS hNorm hUniform hβ he)
  unfold lines
  rw [← min_add_add_right]
  exact min_le_min le_rfl (by linarith)

theorem slope_G {t u : ℝ} (h : t ≤ u) : G u ≤ G t + 2*(u-t) := by
  dsimp [G]
  linarith only [mul_nonneg (show (0 : ℝ) ≤ 2-2*(20582561296/24680948495) by norm_num)
    (sub_nonneg.mpr h)]

theorem slope_B {t u : ℝ} (h : t ≤ u) : B u ≤ B t + 2*(u-t) := by
  dsimp [B, RHWeightedPopulation.v1.sparseLine]
  linarith only [mul_nonneg (show (0 : ℝ) ≤ 2-1163388/1000000 by norm_num)
    (sub_nonneg.mpr h)]

theorem slope_F {t u : ℝ} (h : t ≤ u) : F u ≤ F t + 2*(u-t) := by
  dsimp [F, RHWeightedPopulation.v1.flatLine]
  linarith only [mul_nonneg (show (0 : ℝ) ≤ 2-16/15 by norm_num)
    (sub_nonneg.mpr h)]

theorem slope_brLines {t u : ℝ} (h : t ≤ u) :
    brLines u ≤ brLines t + 2*(u-t) := by
  unfold brLines
  rw [← min_add_add_right]
  exact min_le_min (slope_B h) (slope_F h)

theorem slope_lines {t u : ℝ} (h : t ≤ u) : lines u ≤ lines t + 2*(u-t) := by
  unfold lines
  rw [← min_add_add_right]
  exact min_le_min (slope_G h) (slope_brLines h)

theorem gaussian_profile (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) : Profile β G η :=
  uniformize (by norm_num) hβ hη (fun _ _ => slope_G) (fun _ hu _ he => gaussian hRH hCMS hu he)

theorem br_profile (hRH : RiemannHypothesis)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) : Profile β brLines η :=
  uniformize (by norm_num) hβ hη (fun _ _ => slope_brLines)
    (fun _ hu _ he => bound_mono (by unfold brLines; linarith) (br hRH hNorm hUniform hu))

theorem envelope_profile (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) : Profile β lines η :=
  uniformize (by norm_num) hβ hη (fun _ _ => slope_lines)
    (fun _ hu _ he => envelope_perturbed hRH hCMS hNorm hUniform hu he)

end
end RankTransfer
#print axioms RankTransfer.open_count_endpoint
#print axioms RankTransfer.margin_transport
#print axioms RankTransfer.envelope
#print axioms RankTransfer.envelope_profile
