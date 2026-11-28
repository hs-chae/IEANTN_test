import RH080EstimatePack

/- The named predicates remain hypotheses; no assertion of source-first PV. -/
namespace GrowingRank

open Filter IEANTN.CMSFunctional
open scoped Topology

noncomputable abbrev prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n
noncomputable abbrev p (n : ℕ) : ℝ := (prime n : ℝ)
noncomputable def scale (x : ℝ) : ℝ := Real.sqrt x * Real.log x
noncomputable def endpoint (c x : ℝ) : ℝ := x + c * scale x

theorem p_strict : StrictMono p :=
  fun _ _ h => Nat.cast_lt.mpr (Nat.nth_strictMono Nat.infinite_setOfPred_prime h)

theorem p_atTop : Tendsto p atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop

theorem p_ge_two (n : ℕ) : 2 ≤ p n := by
  exact_mod_cast (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n).two_le

theorem scale_pos (n : ℕ) : 0 < scale (p n) := by
  have := p_ge_two n
  exact mul_pos (Real.sqrt_pos.mpr (by linarith)) (Real.log_pos (by linarith))

theorem piReal_at_prime (n : ℕ) : piReal (p n) = n + 1 := by
  unfold piReal
  rw [Nat.floor_natCast]
  exact Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime n

theorem index_le_iff (k : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    p k ≤ y ↔ k + 1 ≤ piReal y := by
  have h := Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime
    (a := k) (b := ⌊y⌋₊ + 1)
  change (p k ≤ y) ↔ k + 1 ≤ Nat.count Nat.Prime (⌊y⌋₊ + 1)
  rw [Nat.succ_le_iff, h, Nat.lt_succ_iff]
  constructor
  · exact Nat.le_floor
  · intro h'
    exact le_trans (Nat.cast_le.mpr h') (Nat.floor_le hy)

theorem piReal_mono : Monotone piReal :=
  Nat.monotone_primeCounting.comp Nat.floor_mono

theorem j_le_diff_iff (n j : ℕ) {y : ℝ} (hy : p n ≤ y) :
    j ≤ piReal y - piReal (p n) ↔ p (n+j) ≤ y := by
  have H : piReal (p n) ≤ piReal y := piReal_mono hy
  have hn : 0 ≤ y := le_trans (by have := p_ge_two n; linarith) hy
  rw [Nat.le_sub_iff_add_le H, piReal_at_prime, index_le_iff _ hn]
  omega

theorem j_lt_of_extra (n j : ℕ) {y : ℝ} (hy : p n ≤ y)
    (h : j+1 ≤ piReal y - piReal (p n)) : p (n+j) < y := by
  have h' := (j_le_diff_iff n (j+1) hy).1 h
  exact (p_strict (show n+j < n+(j+1) by omega)).trans_le h'

/-- The prime endpoint condition is exact, including when the population is just j. -/
theorem j_lt_iff (n j : ℕ) (_hj : 1 ≤ j) {y : ℝ} (hy : p n ≤ y) :
    p (n+j) < y ↔
      j+1 ≤ piReal y - piReal (p n) ∨
      (piReal y - piReal (p n) = j ∧ ¬ ∃ k : ℕ, Nat.Prime k ∧ (k : ℝ) = y) := by
  constructor
  · intro h
    have hle := (j_le_diff_iff n j hy).2 h.le
    by_cases hplus : j+1 ≤ piReal y - piReal (p n)
    · exact Or.inl hplus
    · refine Or.inr ⟨by omega, ?_⟩
      rintro ⟨k, hk, rfl⟩
      have hmem : k ∈ Set.range prime :=
        Nat.subset_range_nth (p := Nat.Prime) hk
      obtain ⟨m, hm⟩ := hmem
      have hmp : p m = (k : ℝ) := congrArg (fun z : ℕ => (z : ℝ)) hm
      have hnm : n+j < m := p_strict.lt_iff_lt.mp (by rwa [hmp])
      have hp : p (n+(j+1)) ≤ (k : ℝ) := by
        rw [← hmp]
        exact p_strict.monotone (by omega)
      exact hplus ((j_le_diff_iff n (j+1) hy).2 hp)
  · rintro (h | ⟨h, hnp⟩)
    · exact j_lt_of_extra n j hy h
    · have hle := (j_le_diff_iff n j hy).1 h.ge
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hnp ⟨prime (n+j), Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _, heq⟩

theorem endpoint_ge (n : ℕ) {c : ℝ} (hc : 0 ≤ c) : p n ≤ endpoint c (p n) := by
  unfold endpoint
  exact le_add_of_nonneg_right (mul_nonneg hc (scale_pos n).le)

theorem halfOpenCount_eq (c x : ℝ) :
    halfOpenCount c x = piReal (endpoint c x) - piReal x := by
  simp only [halfOpenCount, endpoint, scale, mul_assoc]

theorem cast_count_eventually {a c : ℝ} (h : GoodCoefficient a c) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      a * Real.sqrt (p n) + K < (halfOpenCount c (p n) : ℝ) := by
  obtain ⟨_, δ, hδ, hlarge⟩ := h
  have hA := p_atTop.eventually hlarge
  have hB := ((Real.tendsto_sqrt_atTop.comp p_atTop).const_mul_atTop hδ).eventually
    (eventually_gt_atTop K)
  filter_upwards [hA, hB] with n hn hm
  have hs : 0 < Real.sqrt (p n) := Real.sqrt_pos.mpr (by have := p_ge_two n; linarith)
  have hd := (le_div_iff₀ hs).mp (show a+δ ≤ (halfOpenCount c (p n) : ℝ)/Real.sqrt (p n) from hn)
  dsimp only [Function.comp_apply] at hm
  linarith

/-- Pointwise population slack pays for the +1 rank and for a strict right endpoint.
    In fact the comparison in terms of j-1 works directly, without a floor. -/
theorem transport {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      (j : ℝ)-1 ≤ a * Real.sqrt (p n) → p (n+j)-p n < c * scale (p n) := by
  filter_upwards [cast_count_eventually h 2] with n hn j hj hr
  have he : j+1 ≤ halfOpenCount c (p n) := by
    exact_mod_cast (show (j : ℝ)+1 ≤ (halfOpenCount c (p n) : ℝ) by linarith)
  rw [halfOpenCount_eq] at he
  exact sub_lt_iff_lt_add'.mpr (j_lt_of_extra n j (endpoint_ge n h.1.le) he)

theorem transport_floor {a c : ℝ} (ha : 0 ≤ a) (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      j ≤ ⌊a * Real.sqrt (p n)⌋₊ + 1 → p (n+j)-p n < c * scale (p n) := by
  filter_upwards [transport h] with n hn j hj hcap
  have hx : 0 ≤ a * Real.sqrt (p n) := mul_nonneg ha (Real.sqrt_nonneg _)
  have hc : (j : ℝ) ≤ (⌊a * Real.sqrt (p n)⌋₊ : ℝ)+1 := by exact_mod_cast hcap
  exact hn j hj (by linarith [Nat.floor_le hx])


noncomputable def rankParameter (n j : ℕ) : ℝ := ((j : ℝ)-1) / Real.sqrt (p n)

theorem sqrt_p_pos (n : ℕ) : 0 < Real.sqrt (p n) :=
  Real.sqrt_pos.mpr (by have := p_ge_two n; linarith)

theorem rank_mem {β : ℝ} (hβ : 0 ≤ β) {n j : ℕ} (hj : 1 ≤ j)
    (hc : j ≤ ⌊β * Real.sqrt (p n)⌋₊ + 1) : rankParameter n j ∈ Set.Icc 0 β := by
  have hj' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcap : (j : ℝ) ≤ (⌊β * Real.sqrt (p n)⌋₊ : ℝ)+1 := by exact_mod_cast hc
  have hfloor := Nat.floor_le (mul_nonneg hβ (sqrt_p_pos n).le)
  exact ⟨div_nonneg (sub_nonneg.mpr hj') (sqrt_p_pos n).le,
    (div_le_iff₀ (sqrt_p_pos n)).mpr (by linarith)⟩

theorem GoodCoefficient.with_headroom {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ b, a < b ∧ GoodCoefficient b c := by
  obtain ⟨hc, δ, hδ, hn⟩ := h
  refine ⟨a + δ/2, by linarith, hc, δ/2, by positivity, ?_⟩
  filter_upwards [hn] with x hx
  linarith

/-- Compactness makes *finitely* many fixed-parameter onsets suffice. At
each t choose a fixed width strictly below the desired continuous profile. -/
theorem transport_profile_margin {β : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ a ∈ Set.Icc (0 : ℝ) β, ∃ c, c < g a ∧ GoodCoefficient a c) :
    ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rankParameter n j ∈ Set.Icc 0 β →
      p (n+j) - p n < (g (rankParameter n j) - κ) * scale (p n) := by
  classical
  let I := Set.Icc (0 : ℝ) β
  have H : ∀ a : I, ∃ c b : ℝ, (a : ℝ) < b ∧ c < g a ∧ GoodCoefficient b c := by
    intro a
    obtain ⟨c, hcg, hc⟩ := h a a.property
    obtain ⟨b, hab, hb⟩ := GoodCoefficient.with_headroom hc
    exact ⟨c, b, hab, hcg, hb⟩
  choose c b hab hcg hbc using H
  let m (a : I) := (g a - c a)/2
  have hm : ∀ a, 0 < m a := fun a => half_pos (sub_pos.mpr (hcg a))
  let U (a : I) : Set ℝ := Set.Iio (b a) ∩ {t | c a + m a < g t}
  have hU : ∀ a, IsOpen (U a) := fun a =>
    isOpen_Iio.inter (isOpen_lt continuous_const hg)
  have hcover : I ⊆ ⋃ a, U a := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hab ⟨t, ht⟩, by
      change c ⟨t, ht⟩ + (g t-c ⟨t, ht⟩)/2 < g t
      linarith [hcg ⟨t, ht⟩]⟩
  obtain ⟨S, hS⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := β)).elim_finite_subcover U hU hcover
  have hminimum : ∀ (T : Finset I), ∃ κ > (0 : ℝ), ∀ a ∈ T, κ ≤ m a := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | insert a T _ ih =>
      obtain ⟨κ, hκ, hbnd⟩ := ih
      refine ⟨min (m a) κ, lt_min (hm a) hκ, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbnd i hi)
  obtain ⟨κ, hκ, hκS⟩ := hminimum S
  refine ⟨κ, hκ, ?_⟩
  have hall := (eventually_all_finset S).2 (fun a _ => transport (hbc a))
  filter_upwards [hall] with n hn j hj ht
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hS ht)
  obtain ⟨haS, hmem⟩ := Set.mem_iUnion.mp ha
  have hbound := (div_lt_iff₀ (sqrt_p_pos n)).mp (show rankParameter n j < b a from hmem.1)
  exact (hn a haS j hj hbound.le).trans
    (mul_lt_mul_of_pos_right (show c a < g (rankParameter n j)-κ by
      have hmemb : c a + m a < g (rankParameter n j) := hmem.2
      linarith [hκS a haS]) (scale_pos n))

theorem transport_profile {β : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (h : ∀ a ∈ Set.Icc (0 : ℝ) β, ∃ c, c < g a ∧ GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → rankParameter n j ∈ Set.Icc 0 β →
      p (n+j) - p n < g (rankParameter n j) * scale (p n) := by
  obtain ⟨κ, hκ, hN⟩ := transport_profile_margin hg h
  filter_upwards [hN] with n hn j hj ht
  exact (hn j hj ht).trans (mul_lt_mul_of_pos_right (by linarith) (scale_pos n))

theorem gc_min {a c d : ℝ} (hc : GoodCoefficient a c) (hd : GoodCoefficient a d) :
    GoodCoefficient a (min c d) := by
  by_cases hcd : c ≤ d
  · simpa [min_eq_left hcd] using hc
  · simpa [min_eq_right (le_of_not_ge hcd)] using hd

noncomputable def q : ℝ := 20582561296 / 24680948495
noncomputable def G (a : ℝ) : ℝ := q*(1+2*a)
noncomputable def S := RHWeightedPopulation.v1.sparseLine
noncomputable def F := RHWeightedPopulation.v1.flatLine
noncomputable def BR (a : ℝ) := min (S a) (F a)
noncomputable def envelope (ε a : ℝ) := min (G a + ε) (BR a)

theorem gaussian_gc (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) : GoodCoefficient a (G a + ε) :=
  RH080Exposure.Estimates.gaussian hCMS hRH a ha ε hε

theorem sparse_gc (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {a : ℝ} (ha : 0 ≤ a) :
    GoodCoefficient a (S a) :=
  RH080Exposure.Estimates.sparse hNorm hUniform hRH a ha

theorem flat_gc (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {a : ℝ} (ha : 0 ≤ a) :
    GoodCoefficient a (F a) :=
  RH080Exposure.Estimates.flat hNorm hUniform hRH a ha

theorem br_gc (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {a : ℝ} (ha : 0 ≤ a) :
    GoodCoefficient a (BR a) :=
  gc_min (sparse_gc hRH hNorm hUniform ha) (flat_gc hRH hNorm hUniform ha)

theorem envelope_gc (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) : GoodCoefficient a (envelope ε a) :=
  gc_min (gaussian_gc hRH hCMS ha hε) (br_gc hRH hNorm hUniform ha)

/-- Fixed cap, with no padding on either BR branch. -/
theorem fixed_cap (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β ε : ℝ} (hβ : 0 ≤ β) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β * Real.sqrt (p n)⌋₊ + 1 →
      p (n+j)-p n < envelope ε β * scale (p n) :=
  transport_floor hβ (envelope_gc hRH hCMS hNorm hUniform hβ hε)

theorem continuous_G : Continuous G := by unfold G; fun_prop
theorem continuous_BR : Continuous BR := by
  unfold BR S F RHWeightedPopulation.v1.sparseLine RHWeightedPopulation.v1.flatLine
  fun_prop
theorem continuous_envelope (ε : ℝ) : Continuous (envelope ε) :=
  (continuous_G.add continuous_const).min continuous_BR

theorem envelope_perturb (ε a : ℝ) (he : 0 ≤ ε) :
    envelope ε a ≤ envelope 0 a + ε := by
  unfold envelope
  simp only [add_zero]
  by_cases h : G a ≤ BR a
  · rw [min_eq_left h]
    exact min_le_left _ _
  · rw [min_eq_right (le_of_not_ge h)]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right he)

/-- One uniform error allowance, including the Gaussian input's positive epsilon.
The zero in the displayed envelope is *not* a call to the Gaussian input at 0. -/
theorem adaptive (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → j ≤ ⌊β * Real.sqrt (p n)⌋₊ + 1 →
      p (n+j)-p n < (envelope 0 (rankParameter n j) + η) * scale (p n) := by
  have hn := transport_profile ((continuous_envelope 0).add continuous_const)
    (β := β) (g := fun a => envelope 0 a + η) (by
      intro a ha
      refine ⟨envelope (η/2) a, ?_, envelope_gc hRH hCMS hNorm hUniform ha.1 (by positivity)⟩
      have h := envelope_perturb (η/2) a (by positivity)
      linarith)
  filter_upwards [hn] with n hn j hj hc
  exact hn j hj (rank_mem hβ hj hc)

#print axioms j_lt_iff
#print axioms fixed_cap
#print axioms adaptive


/-- Separate literature premise: CMS (6.10), Montgomery–Vaughan, weakened to ≤. -/
def BrunTitchmarsh : Prop :=
  ∀ x y : ℝ, 1 < x → 1 < y →
    (piReal (x+y) : ℝ) - (piReal x : ℝ) ≤ 2*y/Real.log y

theorem cast_count_real {c x : ℝ} (hx : 1 ≤ x) (hc : 0 ≤ c) :
    (halfOpenCount c x : ℝ) = (piReal (endpoint c x) : ℝ) - (piReal x : ℝ) := by
  have hL : 0 ≤ scale x := mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hx)
  have h : x ≤ endpoint c x := le_add_of_nonneg_right (mul_nonneg hc hL)
  rw [halfOpenCount_eq, Nat.cast_sub (piReal_mono h)]

/-- Uniform small-endpiece estimate. Padding by sqrt x avoids any lower
restriction on the positive difference c-d. -/
theorem loss_bound (bt : BrunTitchmarsh) {c d x : ℝ}
    (hx : 4 ≤ x) (hd : 0 ≤ d) (hdc : d ≤ c) :
    normalizedPopulation c x - normalizedPopulation d x ≤ 4*(c-d) + 4/Real.log x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_pos.2 hx0
  have hs1 : 1 < Real.sqrt x := by nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  have hlog := Real.log_pos hx1
  have hL : 0 ≤ scale x := mul_nonneg hs.le hlog.le
  let y := (c-d)*scale x + Real.sqrt x
  have hys : Real.sqrt x ≤ y := le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hdc) hL)
  have hy1 := hs1.trans_le hys
  have hlogy := Real.log_pos hy1
  have hstart : 1 < endpoint d x := hx1.trans_le (le_add_of_nonneg_right (mul_nonneg hd hL))
  have hend : endpoint c x ≤ endpoint d x + y := by
    dsimp [endpoint, y]
    linarith
  have hcast : (piReal (endpoint c x) : ℝ) ≤ (piReal (endpoint d x + y) : ℝ) :=
    Nat.cast_le.mpr (piReal_mono hend)
  have hlogLe : Real.log x ≤ 2 * Real.log y := by
    have hm := Real.log_le_log hs hys
    rw [Real.log_sqrt hx0.le] at hm
    linarith
  have hquot : 2*y/Real.log y ≤ 4*y/Real.log x := by
    apply (div_le_div_iff₀ hlogy hlog).2
    nlinarith [mul_le_mul_of_nonneg_left hlogLe (show 0 ≤ 2*y by positivity)]
  have h := (sub_le_sub_right hcast (piReal (endpoint d x) : ℝ)).trans
    ((bt (endpoint d x) y hstart hy1).trans hquot)
  rw [normalizedPopulation, normalizedPopulation, ← sub_div,
    cast_count_real hx1.le (hd.trans hdc), cast_count_real hx1.le hd]
  have hiden : 4*y/Real.log x = (4*(c-d)+4/Real.log x)*Real.sqrt x := by
    dsimp [y, scale]
    field_simp
  apply (div_le_iff₀ hs).2
  rw [← hiden]
  linarith

theorem can_shave (bt : BrunTitchmarsh) {a c : ℝ} (hc : GoodCoefficient a c) :
    ∃ d, d < c ∧ GoodCoefficient a d := by
  obtain ⟨hc, δ, hδ, hpop⟩ := hc
  let u := min (c/2) (δ/16)
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  have huc : u ≤ c/2 := min_le_left _ _
  have huδ : u ≤ δ/16 := min_le_right _ _
  have hd : 0 < c-u := by linarith
  refine ⟨c-u, by linarith, hd, δ/2, by positivity, ?_⟩
  have hlogs := Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16/δ))
  filter_upwards [hpop, hlogs, eventually_ge_atTop (4 : ℝ)] with x hpop hlog hx
  have hpos : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : 16 < Real.log x * δ := (div_lt_iff₀ hδ).mp hlog
  have h2 : 4 / Real.log x ≤ δ/4 := (div_le_iff₀ hpos).2 (by nlinarith)
  have h3 := loss_bound bt hx hd.le (show c-u ≤ c by linarith)
  linarith

theorem br_uniform_saving (bt : BrunTitchmarsh) (hRH : RiemannHypothesis)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∃ κ > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, 1 ≤ j →
      j ≤ ⌊β * Real.sqrt (p n)⌋₊+1 →
      p (n+j)-p n < (BR (rankParameter n j)-κ)*scale (p n) := by
  obtain ⟨κ, hκ, H⟩ := transport_profile_margin (β := β) continuous_BR
    (fun a ha => can_shave bt (br_gc hRH hNorm hUniform ha.1))
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [H] with n hn j hj hcap
  exact hn j hj (rank_mem hβ hj hcap)

#print axioms br_uniform_saving
end GrowingRank
