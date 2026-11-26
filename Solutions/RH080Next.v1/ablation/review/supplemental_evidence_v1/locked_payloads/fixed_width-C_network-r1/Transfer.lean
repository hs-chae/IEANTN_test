import RH080EstimatePack

noncomputable section
open Real Filter IEANTN.CMSFunctional
open RHWeightedPopulation.v1
set_option autoImplicit false

namespace RHWidthTransfer

def G (a : ℝ) : ℝ := (20582561296/24680948495 : ℝ)*(1+2*a)
abbrev S := sparseLine
abbrev F := flatLine
def u : ℝ := 544470055511653/2490320656859788
def v : ℝ := 542259/290164
def U : ℝ := 3731134672774344/3112900821074735
def V : ℝ := 9048441/2901640
def E (a : ℝ) : ℝ := min (G a) (min (S a) (F a))
def A3 : ℝ := 685251/387796
def A5 : ℝ := 465/128

theorem switches : 0 < u ∧ u < A3 ∧ A3 < v ∧ v < A5 ∧
    G u = U ∧ S u = U ∧ S v = V ∧ F v = V ∧ U < 3 ∧ 3 < V ∧ V < 5 := by
  norm_num [u,v,U,V,G,A3,A5,sparseLine,flatLine]

theorem gs (a : ℝ) : G a ≤ S a ↔ a ≤ u := by
  unfold G S sparseLine u
  constructor <;> intro h <;> linarith

theorem sf (a : ℝ) : S a ≤ F a ↔ a ≤ v := by
  unfold S F sparseLine flatLine v
  constructor <;> intro h <;> linarith

theorem sg (a : ℝ) : S a ≤ G a ↔ u ≤ a := by
  unfold G S sparseLine u
  constructor <;> intro h <;> linarith

theorem fs (a : ℝ) : F a ≤ S a ↔ v ≤ a := by
  unfold S F sparseLine flatLine v
  constructor <;> intro h <;> linarith

theorem envelope_gaussian {a : ℝ} (h : a ≤ u) : E a = G a := by
  have h' := (gs a).2 h
  exact min_eq_left (le_min h' (h'.trans ((sf a).2 (h.trans (switches.2.1.trans switches.2.2.1).le))))

theorem envelope_sparse {a : ℝ} (hu : u ≤ a) (hv : a ≤ v) : E a = S a := by
  unfold E
  rw [min_eq_left ((sf a).2 hv), min_eq_right ((sg a).2 hu)]

theorem envelope_flat {a : ℝ} (hv : v ≤ a) : E a = F a := by
  have hs := (fs a).2 hv
  have huv : u ≤ v := (switches.2.1.trans switches.2.2.1).le
  unfold E
  rw [min_eq_right hs, min_eq_right (hs.trans ((sg a).2 (huv.trans hv)))]

theorem envelope_piecewise (a : ℝ) : E a = if a < u then G a else
    if a ≤ v then S a else F a := by
  split_ifs with h h'
  · exact envelope_gaussian h.le
  · exact envelope_sparse (le_of_not_gt h) h'
  · exact envelope_flat (le_of_not_ge h')

/-- Describes exactly the upper closure in width of the three recipe statements,
not a necessary condition for the actual prime predicate. -/
theorem recipe_iff (a c : ℝ) :
    (G a < c ∨ S a ≤ c ∨ F a ≤ c) ↔
    (E a < c ∨ (u ≤ a ∧ E a ≤ c)) := by
  by_cases hu : a < u
  · rw [envelope_gaussian hu.le]
    have hgs : G a < S a := lt_of_not_ge (fun h => (not_le_of_gt hu) ((sg a).1 h))
    have hv := hu.le.trans ((switches.2.1.trans switches.2.2.1).le)
    have hgf := hgs.trans_le ((sf a).2 hv)
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inl (hgs.trans_le h)
      · exact Or.inl (hgf.trans_le h)
    · rintro (h | ⟨h,_⟩)
      · exact Or.inl h
      · exact False.elim ((not_le_of_gt hu) h)
  · have ha : u ≤ a := le_of_not_gt hu
    have eqv : (E a < c ∨ (u ≤ a ∧ E a ≤ c)) ↔ E a ≤ c := by
      constructor
      · rintro (h | ⟨_,h⟩)
        · exact h.le
        · exact h
      · exact fun h => Or.inr ⟨ha,h⟩
    rw [eqv]
    constructor
    · rintro (h | h | h)
      · exact (min_le_left _ _).trans h.le
      · exact ((min_le_right _ _).trans (min_le_left _ _)).trans h
      · exact ((min_le_right _ _).trans (min_le_right _ _)).trans h
    · intro h
      rcases le_total a v with hv | hv
      · exact Or.inr (Or.inl ((envelope_sparse ha hv) ▸ h))
      · exact Or.inr (Or.inr ((envelope_flat hv) ▸ h))

theorem recipe_thresholds (a c : ℝ) (ha : 0 ≤ a)
    (h : E a < c ∨ (u ≤ a ∧ E a ≤ c))
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : GoodCoefficient a c := by
  rcases (recipe_iff a c).2 h with hg | hs | hf
  · have hG := RH080Exposure.Estimates.gaussian hCMS hRH a ha (c-G a) (sub_pos.mpr hg)
    convert hG using 1
    change c = G a + (c-G a)
    ring
  · exact RHOnePrime.CMSFunctional.goodCoefficient_mono
      (RH080Exposure.Estimates.sparse hNorm hUniform hRH a ha) hs
  · exact RHOnePrime.CMSFunctional.goodCoefficient_mono
      (RH080Exposure.Estimates.flat hNorm hUniform hRH a ha) hf

theorem three_candidates (a : ℝ) : (G a < 3 ∨ S a ≤ 3 ∨ F a ≤ 3) ↔ a ≤ A3 := by
  unfold G S F sparseLine flatLine A3
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    exact Or.inr (Or.inl (by linarith))

theorem five_candidates (a : ℝ) : (G a < 5 ∨ S a ≤ 5 ∨ F a ≤ 5) ↔ a ≤ A5 := by
  unfold G S F sparseLine flatLine A5
  constructor
  · rintro (h | h | h) <;> linarith
  · intro h
    exact Or.inr (Or.inr (by linarith))

theorem good_three (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : GoodCoefficient A3 3 := by
  have h := RH080Exposure.Estimates.sparse hNorm hUniform hRH A3 (by norm_num [A3])
  have hEq : sparseLine A3 = 3 := by norm_num [A3,sparseLine]
  rwa [hEq] at h

theorem good_five (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : GoodCoefficient A5 5 := by
  have h := RH080Exposure.Estimates.flat hNorm hUniform hRH A5 (by norm_num [A5])
  have hEq : flatLine A5 = 5 := by norm_num [A5,flatLine]
  rwa [hEq] at h

def endpoint (c x : ℝ) : ℝ := x+c*sqrt x*log x

/-- Use a natural ceiling and the strictly-less-than prime count at the top. -/
def strictCount (c x : ℝ) : ℕ := Nat.primeCounting' ⌈endpoint c x⌉₊ - piReal x

def strictPrimes (c x : ℝ) : Finset ℕ :=
  Nat.primesBelow ⌈endpoint c x⌉₊ \ Nat.primesLE ⌊x⌋₊

theorem mem_strictPrimes {x c : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    p ∈ strictPrimes c x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < endpoint c x := by
  have ht : p < ⌈endpoint c x⌉₊ ↔ (p : ℝ) < endpoint c x := Nat.add_one_le_ceil_iff
  have hb : ⌊x⌋₊ < p ↔ x < (p : ℝ) := Nat.floor_lt hx
  simp only [strictPrimes,Finset.mem_sdiff,Nat.mem_primesBelow,Nat.mem_primesLE]
  rw [← ht, ← hb]
  constructor
  · rintro ⟨⟨h1,h2⟩,h3⟩
    exact ⟨h2,lt_of_not_ge (fun h => h3 ⟨h,h2⟩),h1⟩
  · rintro ⟨h1,h2,h3⟩
    exact ⟨⟨h3,h1⟩,fun h => (not_le_of_gt h2) h.1⟩

theorem strictCount_eq_card {x c : ℝ} (hx : 0 < x) (hy : x < endpoint c x) :
    strictCount c x = (strictPrimes c x).card := by
  have hfloor : ⌊x⌋₊ < ⌈endpoint c x⌉₊ :=
    Nat.floor_lt_ceil_of_lt_of_pos hy (hx.trans hy)
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesBelow ⌈endpoint c x⌉₊ := by
    intro p hp
    rcases Nat.mem_primesLE.mp hp with ⟨hp1,hp2⟩
    exact Nat.mem_primesBelow.mpr ⟨hp1.trans_lt hfloor,hp2⟩
  rw [strictPrimes, Finset.card_sdiff_of_subset hsub,
      Nat.primesBelow_card_eq_primeCounting', Nat.primesLE_card_eq_primeCounting]
  rfl

theorem half_le_strict_add_one (c x : ℝ) : halfOpenCount c x ≤ strictCount c x + 1 := by
  let y := endpoint c x
  have h : Nat.primeCounting ⌊y⌋₊ ≤ Nat.primeCounting' ⌈y⌉₊ + 1 := by
    rw [Nat.primeCounting_eq_primeCounting'_succ]
    have hm := Nat.monotone_primeCounting' (Nat.succ_le_succ (Nat.floor_le_ceil y))
    have hh : Nat.primeCounting' (⌈y⌉₊+1) ≤ Nat.primeCounting' ⌈y⌉₊ + 1 := by
      unfold Nat.primeCounting'
      rw [Nat.count_succ]
      split <;> omega
    exact hm.trans hh
  change Nat.primeCounting ⌊y⌋₊ - piReal x ≤
    (Nat.primeCounting' ⌈y⌉₊ - piReal x) + 1
  omega

theorem strict_margin {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ x < endpoint c x ∧ (a+d)*sqrt x ≤ (strictCount c x : ℝ) := by
  rcases h with ⟨hc,d,hd,hh⟩
  refine ⟨d/2,by positivity,?_⟩
  filter_upwards [hh,eventually_ge_atTop (2:ℝ),eventually_ge_atTop ((2/d)^2)] with x hx hx2 hxd
  have hxpos : 0 < x := by linarith
  have hs : 0 < sqrt x := sqrt_pos.2 hxpos
  have hs1 : 2/d ≤ sqrt x := by
    have hsq := sq_sqrt hxpos.le
    by_contra! hlt
    nlinarith [sq_nonneg (sqrt x - 2/d),
      mul_pos (sub_pos.mpr hlt) (show 0 < 2/d + sqrt x by positivity)]
  have hs2 : 1 ≤ (d/2)*sqrt x := by
    have h' : 2 ≤ sqrt x*d := (div_le_iff₀ hd).mp hs1
    linarith
  have hhalf := (le_div_iff₀ hs).mp (show a+d ≤ (halfOpenCount c x : ℝ)/sqrt x from hx)
  have hone : (halfOpenCount c x : ℝ) ≤ (strictCount c x : ℝ) + 1 := by
    exact_mod_cast half_le_strict_add_one c x
  refine ⟨hx2,?_,?_⟩
  · unfold endpoint
    have : 0 < log x := log_pos (by linarith)
    linarith [show 0 < c*sqrt x*log x by positivity]
  · linarith

theorem strict_card_margin {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      (a+d)*sqrt x ≤ ((strictPrimes c x).card : ℝ) := by
  obtain ⟨d,hd,hev⟩ := strict_margin h
  refine ⟨d,hd,?_⟩
  filter_upwards [hev] with x hx
  rw [← strictCount_eq_card (by linarith [hx.1]) hx.2.1]
  exact hx.2.2

theorem strict_three (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      (A3+d)*sqrt x ≤ ((strictPrimes 3 x).card : ℝ) :=
  strict_card_margin (good_three hNorm hUniform hRH)

theorem strict_five (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ x : ℝ in atTop,
      (A5+d)*sqrt x ≤ ((strictPrimes 5 x).card : ℝ) :=
  strict_card_margin (good_five hNorm hUniform hRH)

theorem piReal_primeAt (n : ℕ) : piReal (primeAt n : ℝ) = n+1 := by
  unfold piReal primeAt
  rw [Nat.floor_natCast,Nat.primeCounting_eq_primeCounting'_succ]
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  rw [if_pos (Nat.prime_nth_prime n)]
  change Nat.primeCounting' (Nat.nth Nat.Prime n) + 1 = n + 1
  rw [Nat.primeCounting'_nth_eq]

theorem rank_lt_of_lt_count (k b : ℕ) (h : k < Nat.primeCounting' b) :
    primeAt k < b := by
  apply lt_of_not_ge
  intro hb
  have hh := Nat.monotone_primeCounting' hb
  rw [primeAt,Nat.primeCounting'_nth_eq] at hh
  exact (not_le_of_gt h) hh

/-- m=1 is the first prime after the starting prime; no index shift is hidden. -/
theorem strict_rank {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n : ℕ in atTop,
    ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ (a+d)*sqrt (primeAt n : ℝ) →
      (primeAt n : ℝ) < (primeAt (n+m) : ℝ) ∧
        (primeAt (n+m) : ℝ) < endpoint c (primeAt n : ℝ) := by
  obtain ⟨d,hd,hev⟩ := strict_margin h
  obtain ⟨X,hX⟩ := eventually_atTop.1 hev
  refine ⟨d,hd,eventually_atTop.2 ⟨⌈X⌉₊,?_⟩⟩
  intro n hn m hm hb
  have hpn : n ≤ primeAt n := le_trans (by omega) (Nat.add_two_le_nth_prime n)
  have hX' : X ≤ (primeAt n : ℝ) :=
    (Nat.le_ceil X).trans (by exact_mod_cast hn.trans hpn)
  have hcount : m ≤ strictCount c (primeAt n : ℝ) := by
    exact_mod_cast hb.trans (hX _ hX').2.2
  have hi : n+m < Nat.primeCounting' ⌈endpoint c (primeAt n : ℝ)⌉₊ := by
    rw [strictCount,piReal_primeAt] at hcount
    omega
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  constructor
  · exact_mod_cast hmono (show n < n+m by omega)
  · exact Nat.add_one_le_ceil_iff.mp (rank_lt_of_lt_count _ _ hi)

theorem good_lower_target {a b c : ℝ} (h : GoodCoefficient a c) (hab : b ≤ a) :
    GoodCoefficient b c := by
  obtain ⟨hc,d,hd,hev⟩ := h
  refine ⟨hc,d,hd,?_⟩
  filter_upwards [hev] with x hx
  linarith

/-- At a positive Gaussian target on its limiting width, every strictly
smaller nonnegative target is a GoodCoefficient; equality is not asserted. -/
theorem gaussian_limiting_width (a b : ℝ) (hb : 0 ≤ b) (hba : b < a)
    (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) : GoodCoefficient b (G a) := by
  have h : G b < G a := by unfold G; linarith
  have hg := RH080Exposure.Estimates.gaussian hCMS hRH b hb (G a-G b) (sub_pos.mpr h)
  convert hg using 1
  change G a = G b + (G a-G b)
  ring

def oldDensity (c : ℝ) : ℝ := (8/9)*c - 18203/20000
def oldWidth (a : ℝ) : ℝ := (9/8)*(a + 18203/20000)

theorem octic_comparisons :
    oldDensity 3 = 105391/60000 ∧ oldDensity 5 = 636173/180000 ∧
    A3-oldDensity 3 = 61212941/5816940000 ∧ A5-oldDensity 5 = 70933/720000 ∧
    oldWidth A3 = 46719158823/15511840000 ∧ oldWidth A5 = 3270933/640000 ∧
    oldWidth A3-3 = 183638823/15511840000 ∧ oldWidth A5-5 = 70933/640000 ∧
    103/100 ≤ oldWidth A3 ∧ oldWidth A3 ≤ 16 ∧
    103/100 ≤ oldWidth A5 ∧ oldWidth A5 ≤ 16 := by
  norm_num [oldWidth,oldDensity,A3,A5]

theorem octic_domain (a : ℝ) :
    (103/100 ≤ oldWidth a ∧ oldWidth a ≤ 16) ↔
    (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold oldWidth
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem envelope_octic (a : ℝ) (_hlo : 103/100 ≤ oldWidth a) (_hhi : oldWidth a ≤ 16) :
    E a < oldWidth a := by
  rcases le_total a 2 with h | h
  · apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    unfold oldWidth S sparseLine
    linarith
  · apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
    unfold oldWidth F flatLine
    linarith

#print axioms recipe_thresholds
#print axioms good_three
#print axioms good_five
#print axioms mem_strictPrimes
#print axioms strict_three
#print axioms strict_five
#print axioms strict_rank
#print axioms gaussian_limiting_width
#print axioms strict_card_margin
#print axioms envelope_piecewise
#print axioms three_candidates
#print axioms five_candidates
#print axioms octic_comparisons
#print axioms envelope_octic
end RHWidthTransfer
