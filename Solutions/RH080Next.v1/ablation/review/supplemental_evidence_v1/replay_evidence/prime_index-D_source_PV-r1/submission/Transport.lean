import RH080EstimatePack
import PopulationActualConsumers

set_option autoImplicit false
noncomputable section
open Real Filter IEANTN.CMSFunctional

namespace RankTransport

def P (n : ℕ) : ℝ := primeAt n
def scale (x : ℝ) : ℝ := sqrt x * log x
def cutoff (β : ℝ) (n : ℕ) : ℕ := ⌊β * sqrt (P n)⌋₊ + 1
def gap (n j : ℕ) : ℝ := P (n+j) - P n

theorem P_strictMono : StrictMono P := by
  intro a b hab
  unfold P primeAt
  exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime hab

theorem P_ge (n : ℕ) : (n : ℝ)+2 ≤ P n := by
  unfold P primeAt
  exact_mod_cast Nat.add_two_le_nth_prime n

theorem P_tendsto : Tendsto P atTop atTop := by
  apply tendsto_atTop.2
  intro a
  filter_upwards [eventually_ge_atTop ⌈a⌉₊] with n hn
  have h : (⌈a⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith [Nat.le_ceil a, P_ge n]

theorem P_one_lt (n : ℕ) : 1 < P n := by
  linarith [P_ge n, Nat.cast_nonneg (α := ℝ) n]

theorem scale_pos (n : ℕ) : 0 < scale (P n) :=
  mul_pos (sqrt_pos.2 ((by norm_num : (0 : ℝ) < 1).trans (P_one_lt n)))
    (log_pos (P_one_lt n))

theorem piReal_P (n : ℕ) : piReal (P n) = n + 1 := by
  rw [piReal, P, Nat.floor_natCast, primeAt, Nat.primeCounting, Nat.primeCounting']
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

def piStrict (y : ℝ) : ℕ := Nat.primeCounting' ⌈y⌉₊

theorem strict_count_le_iff (y : ℝ) (k : ℕ) :
    piStrict y ≤ k ↔ y ≤ P k := by
  unfold piStrict Nat.primeCounting' P primeAt
  rw [Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime, Nat.ceil_le]

theorem piStrict_order (y : ℝ) (k : ℕ) : k < piStrict y ↔ P k < y := by
  simpa only [not_le] using not_congr (strict_count_le_iff y k)

theorem piReal_order {y : ℝ} (hy : 0 ≤ y) (k : ℕ) : k < piReal y ↔ P k ≤ y := by
  unfold piReal Nat.primeCounting Nat.primeCounting'
  rw [← not_le, Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime, not_le, Nat.lt_succ_iff]
  exact Nat.le_floor_iff hy

theorem le_endpoint_iff {n j : ℕ} (hj : 1 ≤ j) {y : ℝ} (hy : 0 ≤ y) :
    j ≤ piReal y - piReal (P n) ↔ P (n+j) ≤ y := by
  rw [← piReal_order hy, piReal_P]
  omega

theorem lt_endpoint_iff {n j : ℕ} (hj : 1 ≤ j) (y : ℝ) :
    j ≤ piStrict y - piReal (P n) ↔ P (n+j) < y := by
  rw [← piStrict_order, piReal_P]
  omega

theorem piReal_le_piStrict_add_one (y : ℝ) : piReal y ≤ piStrict y + 1 := by
  unfold piReal piStrict Nat.primeCounting Nat.primeCounting'
  calc
    Nat.count Nat.Prime (⌊y⌋₊ + 1) ≤ Nat.count Nat.Prime (⌈y⌉₊ + 1) :=
      Nat.count_monotone _ (Nat.add_le_add_right (Nat.floor_le_ceil y) 1)
    _ ≤ _ := by rw [Nat.count_succ]; split <;> omega

theorem endpoint_indicator {y : ℝ} (hy : 0 ≤ y) :
    piReal y = piStrict y +
      (if (⌊y⌋₊ : ℝ) = y ∧ Nat.Prime ⌊y⌋₊ then 1 else 0) := by
  unfold piReal piStrict Nat.primeCounting Nat.primeCounting'
  by_cases h : (⌊y⌋₊ : ℝ) = y
  · have hceil : ⌈y⌉₊ = ⌊y⌋₊ := by
      conv_lhs => rw [← h]
      exact Nat.ceil_natCast _
    rw [hceil, Nat.count_succ]
    simp only [h, true_and]
  · have hlo : ⌊y⌋₊ < ⌈y⌉₊ := Nat.lt_ceil.2 ((Nat.floor_le hy).lt_of_ne h)
    have hhi : ⌈y⌉₊ ≤ ⌊y⌋₊ + 1 := Nat.ceil_le.2 (by
      push_cast
      exact (Nat.lt_floor_add_one y).le)
    have hceil : ⌈y⌉₊ = ⌊y⌋₊ + 1 := by omega
    rw [hceil]
    simp [h]

theorem strict_from_halfOpen {n j : ℕ} (hj : 1 ≤ j) {y : ℝ}
    (h : j+1 ≤ piReal y - piReal (P n)) : P (n+j) < y := by
  apply (lt_endpoint_iff hj y).1
  have := piReal_le_piStrict_add_one y
  omega

/-- Stronger than the cutoff conclusion: a fixed positive square-root
width can be removed, and a positive square-root rank margin retained. -/
theorem transport_with_margin {β c : ℝ} (hβ : 0 ≤ β) (h : GoodCoefficient β c) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ j : ℕ, 1 ≤ j → j ≤ cutoff (β+η) n →
        0 < gap n j ∧ gap n j < c * scale (P n) - η * sqrt (P n) := by
  obtain ⟨hc, δ, hδ, hPop⟩ := h
  let η := δ / 4
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨η, hη, ?_⟩
  have hLarge : ∀ᶠ n : ℕ in atTop, 8 / δ < sqrt (P n) :=
    (Real.tendsto_sqrt_atTop.comp P_tendsto).eventually_gt_atTop _
  filter_upwards [P_tendsto.eventually hPop, hLarge] with n hn hLarge
  intro j hj hjMax
  have hX : 0 < P n := by linarith [P_one_lt n]
  have hS : 0 < sqrt (P n) := Real.sqrt_pos.2 hX
  have hn' : (β+δ)*sqrt (P n) ≤ (halfOpenCount c (P n) : ℝ) :=
    (le_div_iff₀ hS).1 hn
  have hj' : (j : ℝ) ≤ (β+η)*sqrt (P n) + 1 := by
    have hz : 0 ≤ (β+η)*sqrt (P n) := by positivity
    have hh : (j : ℝ) ≤ (⌊(β+η)*sqrt (P n)⌋₊ : ℝ)+1 := by
      exact_mod_cast hjMax
    linarith only [hh, Nat.floor_le hz]
  have hδS : 8 < δ * sqrt (P n) := by
    have hh := (div_lt_iff₀ hδ).mp hLarge
    linarith only [hh]
  have hbudget : (j : ℝ) + η * sqrt (P n) + 2 <
      (halfOpenCount c (P n) : ℝ) := by
    dsimp [η] at hj' ⊢
    rw [add_mul] at hn' hj'
    rw [div_mul_eq_mul_div] at hj' ⊢
    linarith only [hn', hj', hδS]
  let y := P n + c * scale (P n)
  have hy : 0 ≤ y := by
    dsimp [y]
    linarith [mul_pos hc (scale_pos n)]
  have hN : (halfOpenCount c (P n) : ℝ) =
      (piReal y : ℝ) - (piReal (P n) : ℝ) := by
    have heq : halfOpenCount c (P n) = piReal y - piReal (P n) := by
      unfold halfOpenCount y scale
      rw [mul_assoc]
    rw [heq, Nat.cast_sub]
    apply Nat.monotone_primeCounting
    apply (Nat.le_floor_iff hy).2
    apply (Nat.floor_le hX.le).trans
    dsimp [y]
    linarith [mul_pos hc (scale_pos n)]
  have hjN : j ≤ halfOpenCount c (P n) := by
    exact_mod_cast (show (j : ℝ) ≤ (halfOpenCount c (P n) : ℝ) by
      linarith [mul_pos hη hS])
  have hle : P (n+j) ≤ y := by
    apply (le_endpoint_iff hj hy).1
    have heq : halfOpenCount c (P n) = piReal y - piReal (P n) := by
      unfold halfOpenCount y scale
      rw [mul_assoc]
    rwa [← heq]
  have hnth : (piReal (P (n+j)) : ℝ) - (piReal (P n) : ℝ) = (j : ℝ) := by
    rw [piReal_P, piReal_P]
    push_cast
    ring
  have hfloors : piReal y ≤ piReal (P (n+j)) + (⌊y⌋₊ - primeAt (n+j)) := by
    unfold piReal
    rw [P, Nat.floor_natCast]
    unfold Nat.primeCounting Nat.primeCounting'
    have hbase : primeAt (n+j) ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hle
    have hstep : ∀ a b : ℕ, Nat.count Nat.Prime (a+b) ≤ Nat.count Nat.Prime a + b := by
      intro a b
      induction b with
      | zero => simp
      | succ b ih =>
        rw [Nat.add_succ, Nat.count_succ]
        split <;> omega
    have hh := hstep (primeAt (n+j)+1) (⌊y⌋₊ - primeAt (n+j))
    convert hh using 2; omega
  have hbase : primeAt (n+j) ≤ ⌊y⌋₊ := (Nat.le_floor_iff hy).2 hle
  have hcount : (piReal y : ℝ) ≤ (piReal (P (n+j)) : ℝ) + (⌊y⌋₊ : ℝ) - P (n+j) := by
    have hh : (piReal y : ℝ) ≤ (piReal (P (n+j)) : ℝ) +
          ((⌊y⌋₊ - primeAt (n+j) : ℕ) : ℝ) := by exact_mod_cast hfloors
    rw [Nat.cast_sub hbase] at hh
    change (piReal y : ℝ) ≤ (piReal (P (n+j)) : ℝ) + ((⌊y⌋₊ : ℝ) - P (n+j)) at hh
    linarith only [hh]
  constructor
  · exact sub_pos.2 (P_strictMono (by omega))
  · have hy' : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    rw [hN] at hbudget
    unfold gap
    change (⌊y⌋₊ : ℝ) ≤ P n + c * scale (P n) at hy'
    linarith only [hbudget, hnth, hcount, hy']

def Bound (β c : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cutoff β n →
      0 < gap n j ∧ gap n j < c * scale (P n)

theorem transport {β c : ℝ} (hβ : 0 ≤ β) (h : GoodCoefficient β c) :
    Bound β c := by
  obtain ⟨η, hη, hh⟩ := transport_with_margin hβ h
  filter_upwards [hh] with n hn
  intro j hj hjMax
  have hm : cutoff β n ≤ cutoff (β+η) n := by
    unfold cutoff
    gcongr
    linarith
  have hS : 0 ≤ sqrt (P n) := sqrt_nonneg _
  obtain ⟨ha,hb⟩ := hn j hj (hjMax.trans hm)
  exact ⟨ha, hb.trans_le (sub_le_self _ (mul_nonneg hη.le hS))⟩

def gaussianLine (β : ℝ) : ℝ := (20582561296/24680948495 : ℝ)*(1+2*β)

theorem gaussian (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    Bound β (gaussianLine β + ε) :=
  transport hβ (RH080Exposure.Estimates.gaussian hCMS hRH β hβ ε hε)

theorem br (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β : ℝ} (hβ : 0 ≤ β) :
    Bound β (RHWeightedPopulation.v1.frontier β) :=
  transport hβ
    (RHWeightedPopulation.v1.challenge_frontier_curve
      (RH080Exposure.Estimates.sparse hNorm hUniform hRH)
      (RH080Exposure.Estimates.flat hNorm hUniform hRH) β hβ)

theorem br_source (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β : ℝ} (hβ : 0 ≤ β) :
    Bound β (RHWeightedPopulation.v1.frontier β) :=
  transport hβ (RH080Next.PopulationCanonical.source_first_frontier hNorm hUniform hRH β hβ)

theorem Bound.min {β a b : ℝ} (ha : Bound β a) (hb : Bound β b) : Bound β (min a b) := by
  rcases le_total a b with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

theorem combined_source (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    Bound β (min (gaussianLine β + ε) (RHWeightedPopulation.v1.frontier β)) :=
  (gaussian hCMS hRH hβ hε).min (br_source hNorm hUniform hRH hβ)

/-- The leading profile for rank j uses (j-1)/sqrt(p_n), not the outer
rank cutoff. The error term below is uniform over the entire cutoff. -/
def rankParameter (n j : ℕ) : ℝ := ((j : ℝ) - 1) / sqrt (P n)

def Profile (β : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cutoff β n →
    gap n j < f (rankParameter n j) * scale (P n)

theorem rank_valid {β : ℝ} {n j : ℕ} (hβ : 0 ≤ β)
    (hj : 1 ≤ j) (hjMax : j ≤ cutoff β n) :
    0 ≤ rankParameter n j ∧ rankParameter n j ≤ β := by
  have hs : 0 < sqrt (P n) := sqrt_pos.2 (by linarith [P_one_lt n])
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hfloor : (j : ℝ) ≤ (⌊β * sqrt (P n)⌋₊ : ℝ) + 1 := by exact_mod_cast hjMax
  have hz : 0 ≤ β * sqrt (P n) := mul_nonneg hβ hs.le
  unfold rankParameter
  exact ⟨div_nonneg (sub_nonneg.2 hjr) hs.le,
    (div_le_iff₀ hs).2 (by linarith only [hfloor, Nat.floor_le hz])⟩

theorem cutoff_of_rank_le {b : ℝ} {n j : ℕ} (hb : 0 ≤ b)
    (h : rankParameter n j ≤ b) : j ≤ cutoff b n := by
  have hs : 0 < sqrt (P n) := sqrt_pos.2 (by linarith [P_one_lt n])
  have h' := (div_le_iff₀ hs).1 h
  cases j with
  | zero => exact Nat.zero_le _
  | succ k =>
    unfold cutoff
    apply Nat.succ_le_succ
    apply (Nat.le_floor_iff (mul_nonneg hb hs.le)).2
    push_cast at h'
    linarith only [h']

/-- Finite grid; no common threshold over continuum parameters is assumed. -/
theorem affine_profile {β a b e : ℝ} (hβ : 0 ≤ β) (hb : 0 ≤ b) (he : 0 < e)
    (hcurve : ∀ t : ℝ, 0 ≤ t → Bound t (a + b*t + e/2)) :
    Profile β (fun t => a+b*t+e) := by
  let d : ℝ := e / (2*(b+1))
  have hd : 0 < d := by dsimp [d]; positivity
  let m : ℕ := ⌈β/d⌉₊
  have hgs : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (m+1), ∀ j : ℕ, 1 ≤ j →
      j ≤ cutoff ((i : ℕ)*d) n → gap n j < (a+b*((i : ℕ)*d)+e/2)*scale (P n) := by
    rw [eventually_all]
    intro i
    have hi := hcurve ((i : ℕ)*d) (mul_nonneg (Nat.cast_nonneg _) hd.le)
    filter_upwards [hi] with n hn j hj hjmax using (hn j hj hjmax).2
  filter_upwards [hgs] with n hn
  intro j hj hjmax
  let t := rankParameter n j
  have hv : 0 ≤ t ∧ t ≤ β := rank_valid hβ hj hjmax
  let k : ℕ := ⌈t/d⌉₊
  have hkm : k ≤ m := by
    dsimp [k,m]
    gcongr
    exact hv.2
  let i : Fin (m+1) := ⟨k, by omega⟩
  have hlo : t ≤ (k : ℝ)*d := (div_le_iff₀ hd).1 (Nat.le_ceil (t/d))
  have hhi : (k : ℝ)*d ≤ t+d := by
    have hh : (k : ℝ) ≤ t/d+1 := by
      cases hk : k with
      | zero => rw [Nat.cast_zero]; linarith [div_nonneg hv.1 hd.le]
      | succ l =>
        have hl : l < ⌈t/d⌉₊ := by
          change l < k
          omega
        have hll := Nat.lt_ceil.1 hl
        push_cast
        linarith only [hll]
    have hp := (le_div_iff₀ hd).1 (show (k : ℝ) - 1 ≤ t/d by linarith only [hh])
    rw [sub_mul, one_mul] at hp
    linarith only [hp]
  have hbd : b*d ≤ e/2 := by
    have hd' : (2*(b+1))*d = e := by
      dsimp [d]
      have hden : (2*(b+1):ℝ) ≠ 0 := by positivity
      field_simp
    nlinarith only [hd', hd.le]
  have hupper : a+b*((k : ℝ)*d)+e/2 ≤ a+b*t+e := by
    have hh := mul_le_mul_of_nonneg_left hhi hb
    rw [mul_add] at hh
    linarith only [hh, hbd]
  have hc : j ≤ cutoff ((k : ℝ)*d) n :=
    cutoff_of_rank_le (mul_nonneg (Nat.cast_nonneg _) hd.le) hlo
  exact (hn i j hj hc).trans_le
    (mul_le_mul_of_nonneg_right hupper (scale_pos n).le)

theorem Profile.min {β : ℝ} {f g : ℝ → ℝ} (hf : Profile β f) (hg : Profile β g) :
    Profile β (fun t => min (f t) (g t)) := by
  filter_upwards [hf,hg] with n hn hm
  intro j hj hjmax
  rcases le_total (f (rankParameter n j)) (g (rankParameter n j)) with h | h
  · rw [min_eq_left h]
    exact hn j hj hjmax
  · rw [min_eq_right h]
    exact hm j hj hjmax

theorem Bound.toProfile {β c : ℝ} (h : Bound β c) : Profile β (fun _ => c) := by
  filter_upwards [h] with n hn j hj hjmax using (hn j hj hjmax).2

theorem br_profile_source (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β e : ℝ} (hβ : 0 ≤ β) (he : 0 < e) :
    Profile β (fun t => min (RHWeightedPopulation.v1.frontier β)
      (RHWeightedPopulation.v1.frontier t + e)) := by
  open RHWeightedPopulation.v1 in
  have hs : Profile β (fun t => sparseLine t+e) := by
    apply affine_profile hβ (by norm_num : (0:ℝ) ≤ 1163388/1000000) he
    intro t ht
    apply transport ht
    apply RHOnePrime.CMSFunctional.goodCoefficient_mono
      (RH080Next.PopulationCanonical.source_first_sparse_curve hNorm hUniform hRH t ht)
    change sparseLine t ≤ sparseLine t+e/2
    linarith only [he]
  open RHWeightedPopulation.v1 in
  have hf : Profile β (fun t => flatLine t+e) := by
    apply affine_profile hβ (by norm_num : (0:ℝ) ≤ 16/15) he
    intro t ht
    apply transport ht
    apply RHOnePrime.CMSFunctional.goodCoefficient_mono
      (RH080Next.PopulationCanonical.source_first_flat_curve hNorm hUniform hRH t ht)
    change flatLine t ≤ flatLine t+e/2
    linarith only [he]
  simpa only [RHWeightedPopulation.v1.frontier, min_add_add_right] using
    (br_source hNorm hUniform hRH hβ).toProfile.min (hs.min hf)

theorem gaussian_profile (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) {β e : ℝ} (hβ : 0 ≤ β) (he : 0 < e) :
    Profile β (fun t => gaussianLine t+e) := by
  have hh := affine_profile (a := 20582561296/24680948495)
    hβ (by norm_num : (0:ℝ) ≤ 2*(20582561296/24680948495)) he
  have heq (t : ℝ) :
      gaussianLine t = 20582561296/24680948495 + 2*(20582561296/24680948495)*t := by
    unfold gaussianLine
    ring
  simp_rw [← heq] at hh
  exact hh (fun _ ht => gaussian hCMS hRH ht (by linarith only [he]))

theorem combined_profile_source (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β e : ℝ} (hβ : 0 ≤ β) (he : 0 < e) :
    Profile β (fun t => min (min (gaussianLine t) (RHWeightedPopulation.v1.frontier t)+e)
      (RHWeightedPopulation.v1.frontier β)) := by
  have hh := (gaussian_profile hCMS hRH hβ he).min (br_profile_source hNorm hUniform hRH hβ he)
  have eq : (fun t => min (min (gaussianLine t) (RHWeightedPopulation.v1.frontier t)+e)
      (RHWeightedPopulation.v1.frontier β)) =
    (fun t => min (gaussianLine t+e)
      (min (RHWeightedPopulation.v1.frontier β) (RHWeightedPopulation.v1.frontier t+e))) := by
    funext t
    rw [← min_add_add_right]
    ac_rfl
  rwa [eq]

/- Separate witness-level refinement; not inferred from the rounded curves. -/
section WitnessRefinement
open RHWeightedPopulation.v1 RH080Next.Explicit AffineFourierPrograms.v1

def sparseRaw (α : ℝ) : ℝ :=
  ((887721072633027910/1000000000000000000 : ℝ) + 2*(546871713113309800/1000000000000000000 : ℝ)*α) /
    (1-4*(119725872611533800/(8*1000000000000000000) : ℝ))

def flatRaw (α : ℝ) : ℝ :=
  ((1120475208606944546/1000000000000000000 : ℝ) + 2*(533333333333333333/1000000000000000000 : ℝ)*α) /
    ((15*533333333333333333)/(8*1000000000000000000) : ℝ)

theorem sparse_raw_good (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) (hProvider : sparse_witness)
    {α c : ℝ} (hc : 0 < c) (hw : sparseRaw α < c) : GoodCoefficient α c := by
  rcases hProvider with ⟨hEligible,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 =
      1-4*(119725872611533800/(8*1000000000000000000) : ℝ) := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
  have hN' : brAmplitudeMass sparseNodes 8 ≤
      (887721072633027910/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hUniform sparseNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,sparseNodes,sparseNumerators])
    (546871713113309800/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) c α hc _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 2*(546871713113309800/1000000000000000000))).2
  unfold sparseRaw at hw
  have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 1-4*(119725872611533800/(8*1000000000000000000) : ℝ))).1 hw
  linarith only [hh,hN']

theorem flat_raw_good (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) (hProvider : flat_witness)
    {α c : ℝ} (hc : 0 < c) (hw : flatRaw α < c) : GoodCoefficient α c := by
  rcases hProvider with ⟨hEligible,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 =
      ((15*533333333333333333)/(8*1000000000000000000) : ℝ) := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]; ring
  have hN' : brAmplitudeMass flatNodes 8 ≤
      (1120475208606944546/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hUniform flatNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,flatNodes,flatNumerators])
    (533333333333333333/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) c α hc _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ) < 2*(533333333333333333/1000000000000000000))).2
  unfold flatRaw at hw
  have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < ((15*533333333333333333)/(8*1000000000000000000) : ℝ))).1 hw
  linarith only [hh,hN']

theorem br_refined_source (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {β c : ℝ} (hβ : 0 ≤ β)
    (hw : min (sparseRaw β) (flatRaw β) < c) : Bound β c := by
  rcases min_lt_iff.1 hw with h | h
  · have hz : 0 < sparseRaw β := by
      unfold sparseRaw
      positivity
    exact transport hβ (sparse_raw_good hUniform hRH (challenge_sparse_witness hNorm)
      (hz.trans h) h)
  · have hz : 0 < flatRaw β := by
      unfold flatRaw
      positivity
    exact transport hβ (flat_raw_good hUniform hRH (challenge_flat_witness hNorm)
      (hz.trans h) h)

theorem sparseRaw_lt_line {β : ℝ} (hβ : 0 ≤ β) : sparseRaw β < sparseLine β := by
  unfold sparseRaw sparseLine
  apply (div_lt_iff₀ (by norm_num)).2
  linarith only [hβ]

theorem flatRaw_lt_line (β : ℝ) : flatRaw β < flatLine β := by
  unfold flatRaw flatLine
  apply (div_lt_iff₀ (by norm_num)).2
  ring_nf
  norm_num

end WitnessRefinement

#print axioms br_refined_source

#print axioms endpoint_indicator
#print axioms affine_profile
#print axioms combined_profile_source

#print axioms le_endpoint_iff
#print axioms lt_endpoint_iff
#print axioms transport_with_margin
#print axioms gaussian
#print axioms br
#print axioms br_source
#print axioms combined_source

end RankTransport
