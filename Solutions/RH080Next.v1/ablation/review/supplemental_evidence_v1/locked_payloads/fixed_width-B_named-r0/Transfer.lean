import RH080EstimatePack

open Filter IEANTN.CMSFunctional
open scoped Nat Real
namespace FreshTransfer
noncomputable section
abbrev G (a : ℝ) : ℝ := (20582561296 / 24680948495) * (1 + 2*a)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine
abbrev u : ℝ := 544470055511653 / 2490320656859788
abbrev v : ℝ := 542259 / 290164
abbrev a3 : ℝ := 685251 / 387796
abbrev a5 : ℝ := 465 / 128

noncomputable def envelope (a : ℝ) : ℝ := min (G a) (min (S a) (F a))

theorem sparse_sub_gaussian (a : ℝ) :
    S a - G a = (2*(20582561296 / 24680948495) - 1163388/1000000) * (u-a) := by
  dsimp [S, RHWeightedPopulation.v1.sparseLine, G, u]
  ring

theorem flat_sub_sparse (a : ℝ) :
    F a - S a = (1163388/1000000 - 16/15) * (v-a) := by
  dsimp [F, S, RHWeightedPopulation.v1.flatLine, RHWeightedPopulation.v1.sparseLine, v]
  ring

theorem sparse_gaussian_iff (a : ℝ) : G a ≤ S a ↔ a ≤ u := by
  have hp : 0 < (2*(20582561296 / 24680948495) - 1163388/1000000 : ℝ) := by norm_num
  rw [← sub_nonneg, sparse_sub_gaussian, mul_nonneg_iff_of_pos_left hp, sub_nonneg]

theorem flat_sparse_iff (a : ℝ) : S a ≤ F a ↔ a ≤ v := by
  have hp : 0 < (1163388/1000000 - 16/15 : ℝ) := by norm_num
  rw [← sub_nonneg, flat_sub_sparse, mul_nonneg_iff_of_pos_left hp, sub_nonneg]

theorem envelope_left {a : ℝ} (ha : a ≤ u) : envelope a = G a := by
  have huv : u ≤ v := by norm_num [u, v]
  simp [envelope, min_eq_left ((flat_sparse_iff a).2 (ha.trans huv)),
    min_eq_left ((sparse_gaussian_iff a).2 ha)]

theorem envelope_mid {a : ℝ} (hau : u ≤ a) (hav : a ≤ v) : envelope a = S a := by
  have h : S a ≤ G a := by
    have h' : 0 ≤ (2*(20582561296 / 24680948495) - 1163388/1000000 : ℝ) := by norm_num
    have := mul_nonpos_of_nonneg_of_nonpos h' (sub_nonpos.mpr hau)
    rw [← sparse_sub_gaussian] at this
    exact sub_nonpos.mp this
  simp [envelope, min_eq_left ((flat_sparse_iff a).2 hav), min_eq_right h]

theorem envelope_right {a : ℝ} (ha : v ≤ a) : envelope a = F a := by
  have huv : u < v := by norm_num [u, v]
  have hSG : S a ≤ G a := le_of_lt (lt_of_not_ge
    (fun h => (not_le_of_gt (huv.trans_le ha)) ((sparse_gaussian_iff a).1 h)))
  have hFS : F a ≤ S a := by
    have hp : 0 ≤ (1163388/1000000 - 16/15 : ℝ) := by norm_num
    have := mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr ha)
    rw [← flat_sub_sparse] at this
    exact sub_nonpos.mp this
  simp [envelope, min_eq_right hFS, min_eq_right (hFS.trans hSG)]

theorem envelope_attained (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) {a : ℝ} (ha : 0 ≤ a) (hu : u ≤ a) :
    GoodCoefficient a (envelope a) := by
  rcases le_total a v with hv | hv
  · rw [envelope_mid hu hv]
    exact RH080Exposure.Estimates.sparse hNorm hUniform hRH a ha
  · rw [envelope_right hv]
    exact RH080Exposure.Estimates.flat hNorm hUniform hRH a ha

theorem above_envelope (hRH : RiemannHypothesis) (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : envelope a < c) : GoodCoefficient a c := by
  rcases le_total u a with hu | hu
  · exact RHOnePrime.CMSFunctional.goodCoefficient_mono
      (envelope_attained hRH hNorm hUniform ha hu) hc.le
  · rw [envelope_left hu] at hc
    have h := RH080Exposure.Estimates.gaussian hCMS hRH a ha (c - G a) (sub_pos.mpr hc)
    convert h using 1
    dsimp [G]
    ring

theorem good_three (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) : GoodCoefficient a3 3 := by
  have h := RH080Exposure.Estimates.sparse hNorm hUniform hRH a3 (by norm_num [a3])
  convert h using 1
  norm_num [S, RHWeightedPopulation.v1.sparseLine, a3]

theorem good_five (hRH : RiemannHypothesis) (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) : GoodCoefficient a5 5 := by
  have h := RH080Exposure.Estimates.flat hNorm hUniform hRH a5 (by norm_num [a5])
  convert h using 1
  norm_num [F, RHWeightedPopulation.v1.flatLine, a5]

def upper (c x : ℝ) : ℝ := x + c * Real.sqrt x * Real.log x

def openPrimes (c x : ℝ) : Finset ℕ :=
  (Nat.primesBelow ⌈upper c x⌉₊) \ (Nat.primesLE ⌊x⌋₊)

theorem mem_openPrimes {c x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    p ∈ openPrimes c x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  simp only [openPrimes, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesBelow,
    Nat.lt_ceil, Nat.le_floor_iff hx]
  grind

theorem openPrimes_card {c x : ℝ} (hx : 0 ≤ x) (hxy : x < upper c x) :
    (openPrimes c x).card = Nat.primeCounting' ⌈upper c x⌉₊ - piReal x := by
  have hs : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesBelow ⌈upper c x⌉₊ := by
    intro p hp
    obtain ⟨hl,hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr
      ⟨Nat.lt_ceil.mpr (((Nat.le_floor_iff hx).mp hl).trans_lt hxy), hp⟩
  rw [openPrimes, Finset.card_sdiff_of_subset hs,
    Nat.primesBelow_card_eq_primeCounting', Nat.primesLE_card_eq_primeCounting]
  rfl

theorem halfOpen_le_open_add_one {c x : ℝ} (hx : 0 ≤ x) (hxy : x < upper c x) :
    halfOpenCount c x ≤ (openPrimes c x).card + 1 := by
  have hy : 0 ≤ upper c x := hx.trans hxy.le
  have hceil : ⌊upper c x⌋₊ ≤ ⌈upper c x⌉₊ := by
    exact_mod_cast (((Nat.le_floor_iff (n := ⌊upper c x⌋₊) hy).mp le_rfl).trans (Nat.le_ceil _))
  have hc : Nat.primeCounting' (⌈upper c x⌉₊ + 1) ≤
      Nat.primeCounting' ⌈upper c x⌉₊ + 1 := by
    rw [← Nat.primesBelow_card_eq_primeCounting', ← Nat.primesBelow_card_eq_primeCounting',
      Nat.primesBelow_succ]
    split
    · exact Finset.card_insert_le _ _
    · omega
  have hl := Nat.monotone_primeCounting' (Nat.add_le_add_right hceil 1)
  rw [openPrimes_card hx hxy]
  change Nat.primeCounting' (⌊upper c x⌋₊ + 1) - piReal x ≤ _
  omega

theorem upper_gt {c x : ℝ} (hc : 0 < c) (hx : 1 < x) : x < upper c x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (zero_lt_one.trans hx)
  have hl : 0 < Real.log x := Real.log_pos hx
  dsimp [upper]
  linarith [mul_pos (mul_pos hc hs) hl]

theorem eventual_open_margin {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop, (a + d) * Real.sqrt x ≤ ((openPrimes c x).card : ℝ) := by
  obtain ⟨hc,d,hd,he⟩ := h
  refine ⟨d/2, by positivity, ?_⟩
  filter_upwards [he, eventually_ge_atTop (2 : ℝ), eventually_ge_atTop ((2/d)^2)] with x hN hx hX
  have hx0 : 0 < x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hbig : 2/d ≤ Real.sqrt x := (Real.le_sqrt (by positivity) hx0.le).mpr hX
  have hprod : 2 ≤ Real.sqrt x * d := (div_le_iff₀ hd).mp hbig
  have hN' : (a + d) * Real.sqrt x ≤ (halfOpenCount c x : ℝ) := (le_div_iff₀ hs).mp hN
  have hLoss := halfOpen_le_open_add_one hx0.le (upper_gt hc (by linarith))
  have hLoss' : (halfOpenCount c x : ℝ) ≤ ((openPrimes c x).card : ℝ) + 1 := by
    exact_mod_cast hLoss
  nlinarith only [hprod, hN', hLoss']

theorem rank_iff {a k : ℕ} :
    Nat.nth Nat.Prime k < a ↔ k < Nat.primeCounting' a := by
  change _ ↔ k < Nat.count Nat.Prime a
  exact lt_iff_lt_of_le_iff_le ((Nat.gc_count_nth Nat.infinite_setOfPred_prime) (a := a) (b := k)).symm

theorem rank_in_open {c x : ℝ} (hx : 0 ≤ x) (hxy : x < upper c x) {m : ℕ}
    (hm : 0 < m) (h : m ≤ (openPrimes c x).card) :
    let p := Nat.nth Nat.Prime (piReal x + m - 1)
    x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  dsimp only
  rw [openPrimes_card hx hxy] at h
  constructor
  · apply (Nat.floor_lt hx).mp
    apply Nat.succ_le_iff.mp
    apply (Nat.gc_count_nth Nat.infinite_setOfPred_prime _ _).mp
    change piReal x ≤ piReal x + m - 1
    omega
  · exact Nat.lt_ceil.mp (rank_iff.mpr (by omega))

/-- Directly usable widths: the Gaussian width inequality is strict. -/
def Direct (a c : ℝ) : Prop := G a < c ∨ S a ≤ c ∨ F a ≤ c

theorem direct_iff {a c : ℝ} :
    Direct a c ↔ envelope a < c ∨ (u ≤ a ∧ envelope a ≤ c) := by
  rcases lt_or_ge a u with hu | hu
  · have hGS : G a < S a := by
      have hp : 0 < (2*(20582561296/24680948495) - 1163388/1000000 : ℝ) := by norm_num
      exact sub_pos.mp (sparse_sub_gaussian a ▸ mul_pos hp (sub_pos.mpr hu))
    have hSF := (flat_sparse_iff a).2 (hu.le.trans (by norm_num [u,v]))
    rw [envelope_left hu.le]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inl (hGS.trans_le h)
      · exact Or.inl ((hGS.trans_le hSF).trans_le h)
    · rintro (h | ⟨h, _⟩)
      · exact Or.inl h
      · exact (not_le_of_gt hu h).elim
  · have hc : envelope a ≤ G a ∧ envelope a ≤ S a ∧ envelope a ≤ F a :=
      ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
        (min_le_right _ _).trans (min_le_right _ _)⟩
    constructor
    · rintro (h | h | h)
      · exact Or.inl (hc.1.trans_lt h)
      · exact Or.inr ⟨hu,hc.2.1.trans h⟩
      · exact Or.inr ⟨hu,hc.2.2.trans h⟩
    · intro h
      have h' : envelope a ≤ c := h.elim le_of_lt And.right
      rcases le_total a v with hv | hv
      · exact Or.inr (Or.inl ((envelope_mid hu hv).symm.trans_le h'))
      · exact Or.inr (Or.inr ((envelope_right hv).symm.trans_le h'))

theorem direct_good (rh : RiemannHypothesis)
    (cms : CMSFunctionalInput.v1.population_reduction)
    (hn : BRFourierInput.v1.norm_identity) (hp : BRFourierInput.v1.uniform_population_q1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : Direct a c) : GoodCoefficient a c := by
  rcases direct_iff.mp hc with h | ⟨hu,h⟩
  · exact above_envelope rh cms hn hp ha h
  · exact RHOnePrime.CMSFunctional.goodCoefficient_mono (envelope_attained rh hn hp ha hu) h

theorem gaussian_at_boundary_below_target (rh : RiemannHypothesis)
    (cms : CMSFunctionalInput.v1.population_reduction)
    {a b : ℝ} (hb : 0 ≤ b) (hba : b < a) : GoodCoefficient b (G a) := by
  have hc : G b < G a := by
    dsimp [G]
    have hq : (0 : ℝ) < 20582561296 / 24680948495 := by norm_num
    exact mul_lt_mul_of_pos_left (by linarith) hq
  have h := RH080Exposure.Estimates.gaussian cms rh b hb (G a - G b) (sub_pos.mpr hc)
  convert h using 1
  dsimp [G]
  ring

theorem direct_three_iff (a : ℝ) : Direct a 3 ↔ a ≤ a3 := by
  dsimp [Direct, G, S, F, RHWeightedPopulation.v1.sparseLine,
    RHWeightedPopulation.v1.flatLine, a3]
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    exact Or.inr (Or.inl (by linarith))

theorem direct_five_iff (a : ℝ) : Direct a 5 ↔ a ≤ a5 := by
  dsimp [Direct, G, S, F, RHWeightedPopulation.v1.sparseLine,
    RHWeightedPopulation.v1.flatLine, a5]
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    exact Or.inr (Or.inr (by linarith))

theorem eventual_open_rank {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℕ, (m : ℝ) ≤ a * Real.sqrt x →
      let p := Nat.nth Nat.Prime (piReal x + m)
      x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  obtain ⟨d,hd,he⟩ := eventual_open_margin h
  filter_upwards [he,eventually_ge_atTop (2 : ℝ)] with x hN hx m hm
  have hx0 : 0 < x := by linarith
  have hxy := upper_gt h.1 (by linarith : 1 < x)
  have hm' : (m : ℝ) < ((openPrimes c x).card : ℝ) := by
    linarith [mul_pos hd (Real.sqrt_pos.2 hx0)]
  have hm'' : m < (openPrimes c x).card := by exact_mod_cast hm'
  simpa only [Nat.add_succ_sub_one] using
    (rank_in_open hx0.le hxy (Nat.succ_pos m) (Nat.succ_le_of_lt hm''))

theorem piReal_at_prime (n : ℕ) : piReal (Nat.nth Nat.Prime n) = n + 1 := by
  change Nat.primeCounting ⌊(Nat.nth Nat.Prime n : ℝ)⌋₊ = n + 1
  rw [Nat.floor_natCast, Nat.primeCounting_eq_primeCounting'_succ]
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  simp [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime]

theorem eventual_prime_shift {a c : ℝ} (ha : 0 ≤ a) (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, let p := (Nat.nth Nat.Prime n : ℝ)
      let r := n + 1 + ⌊a * Real.sqrt p⌋₊
      p < (Nat.nth Nat.Prime r : ℝ) ∧ (Nat.nth Nat.Prime r : ℝ) < upper c p := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventual_open_rank h)
  apply eventually_atTop.mpr
  refine ⟨⌈X⌉₊, ?_⟩
  intro n hn
  have hp : X ≤ (Nat.nth Nat.Prime n : ℝ) :=
    Nat.ceil_le.mp (hn.trans ((Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n)))
  have hz : 0 ≤ a * Real.sqrt (Nat.nth Nat.Prime n : ℝ) := by positivity
  simpa only [piReal_at_prime] using hX _ hp _ (Nat.floor_le hz)

/-- The original affine *leading* inverse, not an onset claim. -/
abbrev O (a : ℝ) : ℝ := (9/8)*(a + 18203/20000)
abbrev oldInv (c : ℝ) : ℝ := (8/9)*c - 18203/20000
abbrev a0 : ℝ := 48519/28000
abbrev w0 : ℝ := 104067/35000

theorem old_domain {a : ℝ} : (103/100 ≤ O a ∧ O a ≤ 16) ↔
    (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  dsimp [O]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem old_minus_flat (a : ℝ) : O a - F a = (7/120)*(a-a0) := by
  dsimp [O,F,a0,RHWeightedPopulation.v1.flatLine]
  ring


theorem envelope_gain_lower (a : ℝ) :
    13152201/1658080000 ≤ O a - envelope a := by
  have huv : u ≤ v := by norm_num [u,v]
  rcases le_total a u with hu | hu
  · rw [envelope_left hu]
    dsimp [O,G,u] at *
    linarith
  · rcases le_total a v with hv | hv
    · rw [envelope_mid hu hv]
      dsimp [O,S,RHWeightedPopulation.v1.sparseLine,v] at *
      linarith
    · rw [envelope_right hv,old_minus_flat]
      dsimp [v,a0] at *
      linarith

theorem envelope_gain_minimum :
    O v - envelope v = 13152201/1658080000 := by
  rw [envelope_right le_rfl,old_minus_flat]
  norm_num [v,a0]

theorem exact_population_gains :
    a3 - oldInv 3 = 61212941/5816940000 ∧ a5 - oldInv 5 = 70933/720000 := by
  norm_num [a3,a5,oldInv]

theorem exact_width_gains :
    O a3 - 3 = 183638823/15511840000 ∧ O a5 - 5 = 70933/640000 := by
  norm_num [O,a3,a5]

noncomputable def invG (c : ℝ) : ℝ := (c - 20582561296/24680948495) / (2*(20582561296/24680948495))
noncomputable def invS (c : ℝ) : ℝ := (c - 944247/1000000) / (1163388/1000000)
noncomputable def invF (c : ℝ) : ℝ := (c - 9/8) / (16/15)
abbrev U : ℝ := 3731134672774344/3112900821074735
abbrev V : ℝ := 9048441/2901640

theorem direct_inverse (a c : ℝ) : Direct a c ↔ a < invG c ∨ a ≤ invS c ∨ a ≤ invF c := by
  have g : G a < c ↔ a < invG c := by
    rw [invG,lt_div_iff₀ (by norm_num)]
    dsimp [G]
    constructor <;> intro h <;> linarith
  have s : S a ≤ c ↔ a ≤ invS c := by
    rw [invS,le_div_iff₀ (by norm_num)]
    dsimp [S,RHWeightedPopulation.v1.sparseLine]
    constructor <;> intro h <;> linarith
  have f : F a ≤ c ↔ a ≤ invF c := by
    rw [invF,le_div_iff₀ (by norm_num)]
    dsimp [F,RHWeightedPopulation.v1.flatLine]
    constructor <;> intro h <;> linarith
  simp only [Direct,g,s,f]

theorem inverse_order (c : ℝ) :
    (invS c ≤ invG c ↔ c ≤ U) ∧ (invF c ≤ invS c ↔ c ≤ V) := by
  dsimp [invS,invF,invG,U,V]
  constructor <;> constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

theorem inverse_knots : G u = U ∧ S u = U ∧ S v = V ∧ F v = V := by
  norm_num [G,S,F,u,v,U,V,RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine]

theorem inverse_numeric :
    (invG 3 = 53460284189/41165122592 ∧ invS 3 = a3 ∧ invF 3 = 225/128) ∧
    (invG 5 = 102822181179/41165122592 ∧ invS 5 = 4055753/1163388 ∧ invF 5 = a5) := by
  norm_num [invG,invS,invF,a3,a5]

theorem direct_gain_at_original_width (rh : RiemannHypothesis)
    (cms : CMSFunctionalInput.v1.population_reduction)
    (hn : BRFourierInput.v1.norm_identity) (hp : BRFourierInput.v1.uniform_population_q1)
    {c : ℝ} (hc : 103/100 ≤ c) :
    GoodCoefficient (oldInv c + 1/200) c := by
  have ha : 0 ≤ oldInv c + 1/200 := by dsimp [oldInv]; linarith
  apply above_envelope rh cms hn hp ha
  have h := envelope_gain_lower (oldInv c + 1/200)
  have hO : O (oldInv c + 1/200) = c + 9/1600 := by dsimp [O,oldInv]; ring
  rw [hO] at h
  linarith

end
end FreshTransfer

#print axioms FreshTransfer.above_envelope
#print axioms FreshTransfer.direct_iff
#print axioms FreshTransfer.good_three
#print axioms FreshTransfer.good_five
#print axioms FreshTransfer.eventual_open_margin
#print axioms FreshTransfer.eventual_prime_shift
#print axioms FreshTransfer.direct_gain_at_original_width
