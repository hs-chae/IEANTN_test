import RH080EstimatePack

noncomputable section
open Filter Real IEANTN.CMSFunctional
set_option autoImplicit false

namespace GrowingRank

abbrev P (n : ℕ) : ℝ := (primeAt n : ℝ)
def H (x : ℝ) : ℝ := sqrt x * log x
def W (n j : ℕ) : ℝ := (P (n+j)-P n) / H (P n)
def cap (β : ℝ) (n : ℕ) : ℕ := ⌊β * sqrt (P n)⌋₊ + 1

theorem p_large (n : ℕ) : (n : ℝ) + 2 ≤ P n := by
  exact_mod_cast Nat.add_two_le_nth_prime n

theorem p_ge_two (n : ℕ) : 2 ≤ P n := by
  linarith [p_large n, Nat.cast_nonneg (α := ℝ) n]

theorem p_strict : StrictMono P := by
  intro n m h
  exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime h

theorem p_tendsto : Tendsto P atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ)) _ tendsto_natCast_atTop_atTop
  intro n
  linarith [p_large n]

theorem H_prime_pos (n : ℕ) : 0 < H (P n) := by
  apply mul_pos (Real.sqrt_pos.2 _) (Real.log_pos _)
  all_goals linarith [p_ge_two n]

theorem pc_at_prime (k : ℕ) : Nat.primeCounting (primeAt k) = k+1 := by
  unfold Nat.primeCounting
  change Nat.count Nat.Prime (primeAt k + 1) = k+1
  unfold primeAt
  rw [Nat.count_succ]
  simp only [Nat.prime_nth_prime, ite_true]
  rw [← Nat.primeCounting', Nat.primeCounting'_nth_eq]

theorem pc'_rank (k m : ℕ) :
    k+1 ≤ Nat.primeCounting' m ↔ primeAt k < m := by
  constructor
  · intro h
    by_contra! hm
    have h' := Nat.monotone_primeCounting' hm
    change Nat.primeCounting' m ≤ Nat.primeCounting' (Nat.nth Nat.Prime k) at h'
    rw [Nat.primeCounting'_nth_eq] at h'
    omega
  · intro h
    have h' := Nat.monotone_primeCounting' (Nat.succ_le_of_lt h)
    change Nat.primeCounting (primeAt k) ≤ Nat.primeCounting' m at h'
    rwa [pc_at_prime] at h'

theorem pi_rank (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    k+1 ≤ piReal y ↔ P k ≤ y := by
  change k+1 ≤ Nat.primeCounting' (⌊y⌋₊ + 1) ↔ _
  rw [pc'_rank, Nat.lt_succ_iff]
  exact ⟨fun h => (Nat.cast_le.mpr h).trans (Nat.floor_le hy), Nat.le_floor⟩

theorem pi_at_prime (n : ℕ) : piReal (P n) = n+1 := by
  rw [piReal, Nat.floor_natCast, pc_at_prime]

/-- For positive ranks no extra monotonicity assumption on y is needed
after requiring y nonnegative. -/
theorem count_bridge (n j : ℕ) (hj : 1 ≤ j) {y : ℝ} (hy : 0 ≤ y) :
    j ≤ piReal y - piReal (P n) ↔ P (n+j) ≤ y := by
  rw [← pi_rank (n+j) hy, pi_at_prime]
  omega

/-- Number of primes strictly below y; for y≤0 this definition is also zero. -/
def strictPi (y : ℝ) : ℕ := Nat.primeCounting' ⌈y⌉₊

theorem strict_count_bridge (n j : ℕ) (hj : 1 ≤ j) (y : ℝ) :
    j ≤ strictPi y - piReal (P n) ↔ P (n+j) < y := by
  have h : n+j+1 ≤ strictPi y ↔ P (n+j) < y := by
    unfold strictPi
    rw [pc'_rank, Nat.lt_ceil]
  rw [← h, pi_at_prime]
  omega

/-- An extra half-open prime suffices irrespective of whether y is prime. -/
theorem extra_prime (n j : ℕ) {y : ℝ} (hy : 0 ≤ y)
    (h : j+1 ≤ piReal y - piReal (P n)) : P (n+j) < y := by
  have hnext := (count_bridge n (j+1) (by omega) hy).mp h
  exact (p_strict (show n+j < n+(j+1) by omega)).trans_le hnext

theorem population_transport {β c : ℝ} (hβ : 0 ≤ β) (hc : GoodCoefficient β c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n → W n j < c := by
  rcases hc with ⟨hc, δ, hδ, hpop⟩
  have hthin : ∀ᶠ n : ℕ in atTop, (1/δ : ℝ) < sqrt (P n) :=
    (Real.tendsto_sqrt_atTop.comp p_tendsto).eventually (eventually_gt_atTop _)
  filter_upwards [p_tendsto.eventually hpop, hthin] with n hpop hthin j _ hj
  have hsq : 0 < sqrt (P n) := Real.sqrt_pos.2 (by linarith [p_ge_two n])
  have hm : 1 < δ * sqrt (P n) := by
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hthin
  have hb : (β+δ) * sqrt (P n) ≤ (halfOpenCount c (P n) : ℝ) :=
    (le_div_iff₀ hsq).mp hpop
  have hf : ((⌊β * sqrt (P n)⌋₊ : ℕ) : ℝ) ≤ β * sqrt (P n) :=
    Nat.floor_le (mul_nonneg hβ hsq.le)
  have hfloor : ⌊β * sqrt (P n)⌋₊ + 1 < halfOpenCount c (P n) := by
    exact_mod_cast (show ((⌊β * sqrt (P n)⌋₊ : ℕ) : ℝ) + 1 <
      (halfOpenCount c (P n) : ℝ) by rw [add_mul] at hb; linarith)
  have hcnt : j+1 ≤ halfOpenCount c (P n) := by
    unfold cap at hj
    omega
  have hy : 0 ≤ P n + c * sqrt (P n) * log (P n) := by
    have hy' := mul_pos hc (H_prime_pos n)
    unfold H at hy'
    rw [mul_assoc]
    linarith [p_ge_two n]
  have he := extra_prime n j hy hcnt
  rw [W, div_lt_iff₀ (H_prime_pos n), H]
  rw [mul_assoc] at he
  linarith

def G (t : ℝ) : ℝ := (20582561296/24680948495) * (1+2*t)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine

theorem gaussian_cap (hRH : RiemannHypothesis)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n → W n j < G β + ε :=
  population_transport hβ (RH080Exposure.Estimates.gaussian hCMS hRH β hβ ε hε)

theorem br_cap (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n → W n j < min (S β) (F β) := by
  filter_upwards [population_transport hβ (RH080Exposure.Estimates.sparse hNorm hUniform hRH β hβ),
    population_transport hβ (RH080Exposure.Estimates.flat hNorm hUniform hRH β hβ)] with n hs hf j hj hc
  exact lt_min (hs j hj hc) (hf j hj hc)

theorem combined_cap (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < min (G β + ε) (min (S β) (F β)) := by
  filter_upwards [gaussian_cap hRH hCMS hβ hε, br_cap hRH hNorm hUniform hβ] with n hg hb j hj hc
  exact lt_min (hg j hj hc) (hb j hj hc)

def rankDensity (n j : ℕ) : ℝ := ((j : ℝ)-1) / sqrt (P n)

theorem rank_nonneg {n j : ℕ} (hj : 1 ≤ j) : 0 ≤ rankDensity n j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  exact div_nonneg (sub_nonneg.mpr hj') (sqrt_nonneg _)

theorem cap_iff_rank {n j : ℕ} {t : ℝ} (ht : 0 ≤ t) (hj : 1 ≤ j) :
    j ≤ cap t n ↔ rankDensity n j ≤ t := by
  have hs : 0 < sqrt (P n) := Real.sqrt_pos.2 (by linarith [p_ge_two n])
  have hsub : (((j-1 : ℕ) : ℝ)) = (j : ℝ)-1 := by
    exact_mod_cast Nat.cast_sub hj (R := ℝ)
  rw [rankDensity, div_le_iff₀ hs, ← hsub,
    ← Nat.le_floor_iff (mul_nonneg ht hs.le), cap]
  omega

/-- Uniformization on a bounded rank range via a finite fixed grid.
Only pointwise eventual convergence at each grid point is needed. -/
theorem affine_uniform {a b : ℝ} (hb : 0 ≤ b)
    (hc : ∀ t : ℝ, 0 ≤ t → ∀ η : ℝ, 0 < η →
      ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap t n → W n j < a+b*t+η)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < a+b*rankDensity n j+ε := by
  let d : ℝ := ε / (2 * (b+1))
  have hd : 0 < d := div_pos hε (by positivity)
  have hd' : d * (2 * (b+1)) = ε := by
    dsimp [d]
    exact div_mul_cancel₀ _ (by positivity)
  have hbd : b*d ≤ ε/2 := by nlinarith
  let I := Finset.range (⌊β/d⌋₊+2)
  have hgrid : ∀ᶠ n : ℕ in atTop, ∀ i ∈ I, ∀ j : ℕ, 1 ≤ j →
      j ≤ cap ((i : ℝ)*d) n → W n j < a+b*((i : ℝ)*d)+ε/2 :=
    (eventually_all_finset I).2 (fun i _ =>
      hc ((i : ℝ)*d) (by positivity) (ε/2) (by positivity))
  filter_upwards [hgrid] with n hn j hj hjcap
  let t := rankDensity n j
  have ht : 0 ≤ t := rank_nonneg hj
  have htβ : t ≤ β := (cap_iff_rank hβ hj).mp hjcap
  let i := ⌊t/d⌋₊+1
  have hi : i ∈ I := by
    have hm := Nat.floor_mono ((div_le_div_iff_of_pos_right hd).2 htβ)
    dsimp [i, I]
    rw [Finset.mem_range]
    omega
  have hi_eq : (i : ℝ) = (⌊t/d⌋₊ : ℕ) + 1 := by dsimp [i]; push_cast; rfl
  have hleft : t ≤ (i : ℝ)*d := by
    apply (div_le_iff₀ hd).mp
    rw [hi_eq]
    exact (Nat.lt_floor_add_one _).le
  have hright : (i : ℝ)*d ≤ t+d := by
    have hfloor := (le_div_iff₀ hd).mp (Nat.floor_le (div_nonneg ht hd.le))
    rw [hi_eq, add_mul, one_mul]
    linarith
  have hcap : j ≤ cap ((i : ℝ)*d) n := (cap_iff_rank (by positivity) hj).mpr hleft
  have hw := hn i hi j hj hcap
  have hw' := mul_le_mul_of_nonneg_left hright hb
  rw [mul_add] at hw'
  change W n j < a+b*t+ε
  linarith

def envelope (t : ℝ) : ℝ := min (G t) (min (S t) (F t))

theorem rank_envelope (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < envelope (rankDensity n j) + ε := by
  have g := affine_uniform (a := (20582561296/24680948495 : ℝ))
    (b := 2*(20582561296/24680948495 : ℝ)) (by norm_num) (by
      intro t ht η hη
      rw [show (20582561296/24680948495 : ℝ) + (2*(20582561296/24680948495 : ℝ))*t =
          G t by unfold G; ring]
      exact gaussian_cap hRH hCMS ht hη) hβ hε
  have s := affine_uniform (a := (944247/1000000 : ℝ)) (b := (1163388/1000000 : ℝ))
    (by norm_num) (by
      intro t ht η hη
      filter_upwards [population_transport ht (RH080Exposure.Estimates.sparse hNorm hUniform hRH t ht)]
        with n hn j hj hjcap
      exact (hn j hj hjcap).trans (lt_add_of_pos_right _ hη)) hβ hε
  have f := affine_uniform (a := (9/8 : ℝ)) (b := (16/15 : ℝ))
    (by norm_num) (by
      intro t ht η hη
      filter_upwards [population_transport ht (RH080Exposure.Estimates.flat hNorm hUniform hRH t ht)]
        with n hn j hj hjcap
      exact (hn j hj hjcap).trans (lt_add_of_pos_right _ hη)) hβ hε
  filter_upwards [g, s, f] with n hg hs hf j hj hjcap
  unfold envelope
  rw [min_add, min_add, lt_min_iff, lt_min_iff]
  refine ⟨?_, hs j hj hjcap, hf j hj hjcap⟩
  rw [show G (rankDensity n j) =
      (20582561296/24680948495 : ℝ) + (2*(20582561296/24680948495 : ℝ))*rankDensity n j by
    unfold G
    ring]
  exact hg j hj hjcap

theorem clipped_envelope (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < min (envelope (rankDensity n j) + ε) (min (S β) (F β)) := by
  filter_upwards [rank_envelope hRH hCMS hNorm hUniform hβ hε, br_cap hRH hNorm hUniform hβ]
    with n h₁ h₂ j hj hjcap
  exact lt_min (h₁ j hj hjcap) (h₂ j hj hjcap)

def u : ℝ := 544470055511653/2490320656859788
def v : ℝ := 542259/290164

theorem u_pos : 0 < u := by norm_num [u]
theorem u_lt_v : u < v := by norm_num [u, v]

theorem GS_order (t : ℝ) : G t ≤ S t ↔ t ≤ u := by
  unfold G S RHWeightedPopulation.v1.sparseLine u
  constructor <;> intro h <;> linarith

theorem SF_order (t : ℝ) : S t ≤ F t ↔ t ≤ v := by
  unfold S F RHWeightedPopulation.v1.sparseLine RHWeightedPopulation.v1.flatLine v
  constructor <;> intro h <;> linarith

theorem SG_order (t : ℝ) : S t ≤ G t ↔ u ≤ t := by
  unfold G S RHWeightedPopulation.v1.sparseLine u
  constructor <;> intro h <;> linarith

theorem FS_order (t : ℝ) : F t ≤ S t ↔ v ≤ t := by
  unfold S F RHWeightedPopulation.v1.sparseLine RHWeightedPopulation.v1.flatLine v
  constructor <;> intro h <;> linarith

theorem active_gaussian {t : ℝ} (ht : t ≤ u) : envelope t = G t := by
  have h₁ := (GS_order t).2 ht
  have h₂ := (SF_order t).2 (ht.trans u_lt_v.le)
  simp [envelope, min_eq_left h₂, min_eq_left h₁]

theorem active_sparse {t : ℝ} (h₁ : u ≤ t) (h₂ : t ≤ v) : envelope t = S t := by
  simp [envelope, min_eq_left ((SF_order t).2 h₂), min_eq_right ((SG_order t).2 h₁)]

theorem active_flat {t : ℝ} (ht : v ≤ t) : envelope t = F t := by
  have h₁ := (FS_order t).2 ht
  have h₂ := (SG_order t).2 (u_lt_v.le.trans ht)
  simp [envelope, min_eq_right h₁, min_eq_right (h₁.trans h₂)]

/-- On and above the first switch the true cap theorem needs neither
the CMS premise nor any positive width tolerance. -/
theorem exact_envelope_cap (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {β : ℝ} (hβ : u ≤ β) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n → W n j < envelope β := by
  have h := (SG_order β).mpr hβ
  have h' := (min_le_left (S β) (F β)).trans h
  rw [envelope, min_eq_right h']
  exact br_cap hRH hNorm hUniform (u_pos.le.trans hβ)

theorem odd_spacing {k : ℕ} (hk : 1 ≤ k) (m : ℕ) : P k + 2*(m : ℝ) ≤ P (k+m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.nth_strictMono Nat.infinite_setOfPred_prime (show k+m < k+(m+1) by omega)
    change Nat.nth Nat.Prime (k+m) < Nat.nth Nat.Prime (k+(m+1)) at h
    have he := Nat.add_two_le_nth_prime (k+m)
    have he' := Nat.add_two_le_nth_prime (k+(m+1))
    have ho := (Nat.prime_nth_prime (k+m)).eq_two_or_odd.resolve_left (by omega)
    have ho' := (Nat.prime_nth_prime (k+(m+1))).eq_two_or_odd.resolve_left (by omega)
    have hgap : primeAt (k+m) + 2 ≤ primeAt (k+(m+1)) := by
      unfold primeAt
      omega
    have hgap' : P (k+m) + 2 ≤ P (k+(m+1)) := by exact_mod_cast hgap
    rw [Nat.cast_succ]
    linarith

/-- The same GoodCoefficient slack gives a uniform lower-order saving.
Here δ is the actual, unspecified positive population margin. -/
theorem population_headroom {β c : ℝ} (hβ : 0 ≤ β) (hc : GoodCoefficient β c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      P (n+j)-P n ≤ c*H (P n) - 2*δ*sqrt (P n) + 2 := by
  rcases hc with ⟨hc, δ, hδ, hpop⟩
  refine ⟨δ, hδ, ?_⟩
  have hthin : ∀ᶠ n : ℕ in atTop, (1/δ : ℝ) < sqrt (P n) :=
    (Real.tendsto_sqrt_atTop.comp p_tendsto).eventually (eventually_gt_atTop _)
  filter_upwards [p_tendsto.eventually hpop, hthin] with n hpop hthin j hj hjcap
  have hy' := mul_pos hc (H_prime_pos n)
  have hy : 0 ≤ P n + c * sqrt (P n) * log (P n) := by
    unfold H at hy'
    rw [mul_assoc]
    linarith [p_ge_two n]
  let K := halfOpenCount c (P n)
  have hsq : 0 < sqrt (P n) := Real.sqrt_pos.2 (by linarith [p_ge_two n])
  have hm : 1 < δ * sqrt (P n) := by
    simpa [mul_comm] using (div_lt_iff₀ hδ).mp hthin
  have hb : (β+δ) * sqrt (P n) ≤ (K : ℝ) := (le_div_iff₀ hsq).mp hpop
  have hf : ((⌊β * sqrt (P n)⌋₊ : ℕ) : ℝ) ≤ β * sqrt (P n) :=
    Nat.floor_le (mul_nonneg hβ hsq.le)
  have hj' : (j : ℝ) ≤ (⌊β * sqrt (P n)⌋₊ : ℕ) + 1 := by
    exact_mod_cast hjcap
  have hdiff : δ * sqrt (P n) - 1 ≤ (K : ℝ) - (j : ℝ) := by
    rw [add_mul] at hb
    linarith
  have hjK : j ≤ K := by
    exact_mod_cast (show (j : ℝ) ≤ K by linarith)
  have hK := (count_bridge n K (hj.trans hjK) hy).mp (le_refl K)
  have hs := odd_spacing (k := n+j) (by omega) (K-j)
  rw [Nat.cast_sub hjK, show n+j+(K-j) = n+K by omega] at hs
  rw [mul_assoc] at hK
  change P (n+K) ≤ P n + c*H (P n) at hK
  linarith

section WitnessRefinement

open RH080Next.Explicit AffineFourierPrograms.v1

def Ds : ℝ := 1-4*(119725872611533800/(8*1000000000000000000) : ℝ)
def Df : ℝ := (15*533333333333333333)/(8*1000000000000000000)
def As : ℝ := (887721072633027910/1000000000000000000) / Ds
def Bs : ℝ := (2*(546871713113309800/1000000000000000000)) / Ds
def Af : ℝ := (1120475208606944546/1000000000000000000) / Df
def Bf : ℝ := (2*(533333333333333333/1000000000000000000)) / Df

/-- Optional witness-level refinement: the inequality is strict because
the added tolerance is positive, not because the norm cap is a strict bound. -/
theorem sparse_refined (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (t : ℝ) (ht : 0 ≤ t) (η : ℝ) (hη : 0 < η) :
    GoodCoefficient t (As+Bs*t+η) := by
  rcases RH080Next.PopulationCanonical.kernel_only_sparse_witness hNorm with
    ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 = Ds := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
    rfl
  have hN' : brAmplitudeMass sparseNodes 8 ≤ (887721072633027910/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hUniform sparseNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,sparseNodes,sparseNumerators])
    (546871713113309800/1000000000000000000 : ℝ) (by norm_num)
    hBound hAttain (by rw [hD]; norm_num [Ds]) _ _
    (by have ha : 0 < As := by norm_num [As, Ds]
        have hb : 0 ≤ Bs := by norm_num [Bs, Ds]
        positivity) _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(546871713113309800/1000000000000000000))).2
  have hp : 0 < η*Ds := mul_pos hη (by norm_num [Ds])
  unfold As Bs Ds at *
  linarith

theorem flat_refined (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (t : ℝ) (ht : 0 ≤ t) (η : ℝ) (hη : 0 < η) :
    GoodCoefficient t (Af+Bf*t+η) := by
  rcases RH080Next.PopulationCanonical.kernel_only_flat_witness hNorm with
    ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 = Df := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]
    unfold Df
    ring
  have hN' : brAmplitudeMass flatNodes 8 ≤ (1120475208606944546/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hUniform flatNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,flatNodes,flatNumerators])
    (533333333333333333/1000000000000000000 : ℝ) (by norm_num)
    hBound hAttain (by rw [hD]; norm_num [Df]) _ _
    (by have ha : 0 < Af := by norm_num [Af, Df]
        have hb : 0 ≤ Bf := by norm_num [Bf, Df]
        positivity) _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(533333333333333333/1000000000000000000))).2
  have hp : 0 < η*Df := mul_pos hη (by norm_num [Df])
  unfold Af Bf Df at *
  linarith

theorem br_rank_refined (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < min (As+Bs*rankDensity n j) (Af+Bf*rankDensity n j) + ε := by
  have hs := affine_uniform (by norm_num [Bs,Ds])
    (fun t ht η hη => population_transport ht (sparse_refined hRH hNorm hUniform t ht η hη)) hβ hε
  have hf := affine_uniform (by norm_num [Bf,Df])
    (fun t ht η hη => population_transport ht (flat_refined hRH hNorm hUniform t ht η hη)) hβ hε
  filter_upwards [hs,hf] with n hs hf j hj hjcap
  rw [min_add]
  exact lt_min (hs j hj hjcap) (hf j hj hjcap)

theorem br_rank_exact (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < min (S (rankDensity n j)) (F (rankDensity n j)) := by
  filter_upwards [br_rank_refined hRH hNorm hUniform hβ (show (0:ℝ)<1/2000000 by norm_num)]
    with n hn j hj hc
  have ht := rank_nonneg (n := n) hj
  apply (hn j hj hc).trans_le
  rw [min_add]
  apply min_le_min
  · have h := mul_nonneg (show 0 ≤ (1163388/1000000 : ℝ)-Bs by norm_num [Bs,Ds]) ht
    unfold S RHWeightedPopulation.v1.sparseLine
    have ha : As+1/2000000 ≤ (944247/1000000 : ℝ) := by norm_num [As,Ds]
    nlinarith
  · have h : Bf = (16/15 : ℝ) := by norm_num [Bf,Df]
    rw [h]
    unfold F RHWeightedPopulation.v1.flatLine
    have ha : Af+1/2000000 ≤ (9/8 : ℝ) := by norm_num [Af,Df]
    linarith

theorem sharpened_envelope (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ cap β n →
      W n j < min (G (rankDensity n j)+ε)
        (min (S (rankDensity n j)) (F (rankDensity n j))) := by
  filter_upwards [rank_envelope hRH hCMS hNorm hUniform hβ hε, br_rank_exact hRH hNorm hUniform hβ]
    with n hn hb j hj hc
  apply lt_min _ (hb j hj hc)
  apply (hn j hj hc).trans_le
  exact add_le_add_left (min_le_left _ _) ε

end WitnessRefinement
end GrowingRank

#print axioms GrowingRank.count_bridge
#print axioms GrowingRank.strict_count_bridge
#print axioms GrowingRank.population_transport
#print axioms GrowingRank.combined_cap
#print axioms GrowingRank.clipped_envelope
#print axioms GrowingRank.exact_envelope_cap
#print axioms GrowingRank.population_headroom
#print axioms GrowingRank.br_rank_refined
#print axioms GrowingRank.sharpened_envelope
