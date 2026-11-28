import RH080EstimatePack

set_option autoImplicit false
noncomputable section
open Real Filter IEANTN.CMSFunctional
open scoped Finset

namespace RH080Transfer

def q : ℝ := 20582561296/24680948495
def G (a : ℝ) : ℝ := q*(1+2*a)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine
def A : ℝ := 544470055511653/2490320656859788
def B : ℝ := 542259/290164
def D : ℝ := 172404138261/356130660736
def E (a : ℝ) : ℝ := min (G a) (min (S a) (F a))
def octic (a : ℝ) : ℝ := (9/8)*(a+18203/20000)
def octicLead (c : ℝ) : ℝ := (8/9)*c-18203/20000
def t3 : ℝ := 685251/387796
def t5 : ℝ := 465/128

theorem ordered : 0 < A ∧ A < D ∧ D < B := by norm_num [A,D,B]

lemma gs (a : ℝ) : G a ≤ S a ↔ a ≤ A := by
  unfold G q S RHWeightedPopulation.v1.sparseLine A
  constructor <;> intro h <;> linarith
lemma sg (a : ℝ) : S a ≤ G a ↔ A ≤ a := by
  unfold G q S RHWeightedPopulation.v1.sparseLine A
  constructor <;> intro h <;> linarith
lemma sf (a : ℝ) : S a ≤ F a ↔ a ≤ B := by
  unfold S F RHWeightedPopulation.v1.sparseLine RHWeightedPopulation.v1.flatLine B
  constructor <;> intro h <;> linarith
lemma fs (a : ℝ) : F a ≤ S a ↔ B ≤ a := by
  unfold S F RHWeightedPopulation.v1.sparseLine RHWeightedPopulation.v1.flatLine B
  constructor <;> intro h <;> linarith
lemma gf (a : ℝ) : G a ≤ F a ↔ a ≤ D := by
  unfold G q F RHWeightedPopulation.v1.flatLine D
  constructor <;> intro h <;> linarith
lemma fg (a : ℝ) : F a ≤ G a ↔ D ≤ a := by
  unfold G q F RHWeightedPopulation.v1.flatLine D
  constructor <;> intro h <;> linarith

theorem left_branch {a : ℝ} (ha : a ≤ A) : E a = G a := by
  unfold E
  exact min_eq_left (le_min ((gs a).2 ha) ((gf a).2 (ha.trans ordered.2.1.le)))
theorem middle_branch {a : ℝ} (ha : A ≤ a) (hb : a ≤ B) : E a = S a := by
  simp only [E, min_eq_left ((sf a).2 hb), min_eq_right ((sg a).2 ha)]
theorem right_branch {a : ℝ} (hb : B ≤ a) : E a = F a := by
  simp only [E, min_eq_right ((fs a).2 hb), min_eq_right ((fg a).2
    (ordered.2.2.le.trans hb))]

theorem attainable (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a : ℝ} (ha : A ≤ a) {c : ℝ} (hc : E a ≤ c) :
    GoodCoefficient a c := by
  have h0 := ordered.1.le.trans ha
  apply RHOnePrime.CMSFunctional.goodCoefficient_mono _ hc
  rcases le_total a B with hb | hb
  · rw [middle_branch ha hb]
    exact RH080Exposure.Estimates.sparse hn hu rh a h0
  · rw [right_branch hb]
    exact RH080Exposure.Estimates.flat hn hu rh a h0

theorem gaussian_branch (hm : CMSFunctionalInput.v1.population_reduction)
    (rh : RiemannHypothesis) {a : ℝ} (h0 : 0 ≤ a) (ha : a ≤ A)
    {c : ℝ} (hc : E a < c) :
    GoodCoefficient a c := by
  rw [left_branch ha] at hc
  have h := RH080Exposure.Estimates.gaussian hm rh a h0 (c-G a) (sub_pos.mpr hc)
  have he : G a + (c-G a) = c := by ring
  change GoodCoefficient a (G a + (c-G a)) at h
  rwa [he] at h

theorem above_envelope (hm : CMSFunctionalInput.v1.population_reduction)
    (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a : ℝ} (h0 : 0 ≤ a) {c : ℝ} (hc : E a < c) :
    GoodCoefficient a c := by
  rcases le_total a A with ha | ha
  · exact gaussian_branch hm rh h0 ha hc
  · exact attainable hn hu rh ha hc.le

theorem numerical_widths :
    (S t3 = 3 ∧ F t5 = 5) ∧ (A ≤ t3 ∧ t3 < B ∧ B < t5) := by
  norm_num [RHWeightedPopulation.v1.sparseLine, RHWeightedPopulation.v1.flatLine,
    t3,t5,A,B]

theorem width3 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodCoefficient t3 3 := by
  rw [← numerical_widths.1.1]
  exact RH080Exposure.Estimates.sparse hn hu rh t3 (by norm_num [t3])

theorem width5 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodCoefficient t5 5 := by
  rw [← numerical_widths.1.2]
  exact RH080Exposure.Estimates.flat hn hu rh t5 (by norm_num [t5])

theorem inverse3 (a : ℝ) : E a ≤ 3 ↔ a ≤ t3 := by
  have hg : G a ≤ 3 → a ≤ t3 := by unfold G q t3; intro h; linarith
  have hs : S a ≤ 3 ↔ a ≤ t3 := by
    unfold S RHWeightedPopulation.v1.sparseLine t3
    constructor <;> intro h <;> linarith
  have hf : F a ≤ 3 → a ≤ t3 := by
    unfold F RHWeightedPopulation.v1.flatLine t3; intro h; linarith
  simp only [E, min_le_iff, hs]
  exact ⟨fun h => h.elim hg (fun h => h.elim id hf), fun h => Or.inr (Or.inl h)⟩

theorem inverse5 (a : ℝ) : E a ≤ 5 ↔ a ≤ t5 := by
  have hg : G a ≤ 5 → a ≤ t5 := by unfold G q t5; intro h; linarith
  have hs : S a ≤ 5 → a ≤ t5 := by
    unfold S RHWeightedPopulation.v1.sparseLine t5; intro h; linarith
  have hf : F a ≤ 5 ↔ a ≤ t5 := by
    unfold F RHWeightedPopulation.v1.flatLine t5
    constructor <;> intro h <;> linarith
  simp only [E, min_le_iff, hf]
  exact ⟨fun h => h.elim hg (fun h => h.elim hs id), fun h => Or.inr (Or.inr h)⟩

theorem octic_domain (a : ℝ) :
    (103/100 ≤ octic a ∧ octic a ≤ 16) ↔
      (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold octic
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem gains :
    t3-octicLead 3 = 61212941/5816940000 ∧ t5-octicLead 5 = 70933/720000 := by
  norm_num [t3,t5,octicLead,octic]

def upper (c x : ℝ) : ℝ := x+c*sqrt x*log x
def openCount (c x : ℝ) : ℕ :=
  Nat.primeCounting' ⌈upper c x⌉₊ - piReal x

theorem openCount_card {c x : ℝ} (hx : 0 ≤ x) :
    openCount c x =
      ((Nat.primesBelow ⌈upper c x⌉₊).filter (fun p : ℕ => x < (p : ℝ))).card := by
  have he : (Nat.primesBelow ⌈upper c x⌉₊).filter (fun p : ℕ => x < (p : ℝ)) =
      Nat.primesBelow ⌈upper c x⌉₊ \ Nat.primesLE ⌊x⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesBelow,
      Nat.le_floor_iff hx]
    grind
  rw [he]
  by_cases hy : x < upper c x
  · have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesBelow ⌈upper c x⌉₊ := by
      intro p hp
      rw [Nat.mem_primesLE, Nat.le_floor_iff hx] at hp
      exact Nat.mem_primesBelow.mpr ⟨Nat.lt_ceil.mpr (hp.1.trans_lt hy),hp.2⟩
    rw [Finset.card_sdiff_of_subset hsub, Nat.primesLE_card_eq_primeCounting,
      Nat.primesBelow_card_eq_primeCounting']
    rfl
  · have hsub : Nat.primesBelow ⌈upper c x⌉₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
      intro p hp
      rw [Nat.mem_primesBelow, Nat.lt_ceil] at hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).2
        (hp.1.le.trans (le_of_not_gt hy)), hp.2⟩
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hsub, Finset.card_empty, openCount, piReal]
    apply Nat.sub_eq_zero_of_le
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
    exact Finset.card_le_card hsub

theorem open_member (c x : ℝ) (p : ℕ) :
    p ∈ (Nat.primesBelow ⌈upper c x⌉₊).filter (fun p : ℕ => x < (p : ℝ)) ↔
      p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  simp only [Finset.mem_filter, Nat.mem_primesBelow, Nat.lt_ceil]
  tauto

theorem endpoints (c x : ℝ) :
    openCount c x ≤ halfOpenCount c x ∧ halfOpenCount c x ≤ openCount c x + 1 := by
  let y := upper c x
  have hlo := Nat.monotone_primeCounting' (Nat.floor_le_ceil y)
  have hhi := Nat.monotone_primeCounting' (Nat.ceil_le_floor_add_one y)
  have hs : Nat.primeCounting' (⌊y⌋₊+1) ≤ Nat.primeCounting' ⌊y⌋₊ + 1 := by
    unfold Nat.primeCounting'
    rw [Nat.count_succ]
    split <;> omega
  change Nat.primeCounting' ⌈y⌉₊ - piReal x ≤
      Nat.primeCounting' (⌊y⌋₊+1) - piReal x ∧
    Nat.primeCounting' (⌊y⌋₊+1) - piReal x ≤
      Nat.primeCounting' ⌈y⌉₊ - piReal x + 1
  omega

def GoodOpen (a c : ℝ) : Prop :=
  0 < c ∧ ∃ d : ℝ, 0 < d ∧
    ∀ᶠ x : ℝ in atTop, a+d ≤ (openCount c x : ℝ)/sqrt x

theorem goodOpen_iff {a c : ℝ} : GoodOpen a c ↔ GoodCoefficient a c := by
  constructor
  · rintro ⟨hc,d,hd,h⟩
    refine ⟨hc,d,hd,?_⟩
    filter_upwards [h] with x hx
    exact hx.trans (div_le_div_of_nonneg_right (by exact_mod_cast (endpoints c x).1)
      (sqrt_nonneg _))
  · rintro ⟨hc,d,hd,h⟩
    have hz : 0 ≤ 2/d := by positivity
    refine ⟨hc,d/2,by positivity,?_⟩
    filter_upwards [h,eventually_ge_atTop ((2/d)^2),eventually_ge_atTop (1 : ℝ)]
      with x hx hxx hx1
    have hs : 0 < sqrt x := sqrt_pos.mpr (by linarith)
    have hl : 2/d ≤ sqrt x := by
      simpa only [sqrt_sq hz] using sqrt_le_sqrt hxx
    have ht : 2 ≤ sqrt x*d := (div_le_iff₀ hd).mp hl
    change a+d ≤ (halfOpenCount c x : ℝ)/sqrt x at hx
    have hp := (le_div_iff₀ hs).mp hx
    have he : (halfOpenCount c x : ℝ) ≤ (openCount c x : ℝ)+1 := by
      exact_mod_cast (endpoints c x).2
    apply (le_div_iff₀ hs).mpr
    linarith

def p (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem pi_at_prime (n : ℕ) : piReal (p n : ℝ) = n+1 := by
  rw [piReal, Nat.floor_natCast, Nat.primeCounting, Nat.primeCounting',
    Nat.count_succ]
  change Nat.primeCounting' (p n) + (if Nat.Prime (p n) then 1 else 0) = n+1
  simp [p]

theorem prime_rank_open {c : ℝ} {n k : ℕ} (hk : 0 < k)
    (h : k ≤ openCount c (p n : ℝ)) :
    (p n : ℝ) < (p (n+k) : ℝ) ∧ (p (n+k) : ℝ) < upper c (p n : ℝ) := by
  have hm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  constructor
  · exact_mod_cast hm (show n < n+k by omega)
  · by_contra! hbad
    have hy : ⌈upper c (p n : ℝ)⌉₊ ≤ p (n+k) := Nat.ceil_le.mpr hbad
    have ht := Nat.monotone_primeCounting' hy
    change Nat.primeCounting' ⌈upper c (p n : ℝ)⌉₊ ≤
      Nat.primeCounting' (Nat.nth Nat.Prime (n+k)) at ht
    rw [Nat.primeCounting'_nth_eq] at ht
    rw [openCount, pi_at_prime] at h
    omega

theorem prime_rank_halfOpen {c : ℝ} {n k : ℕ} (hk : 0 < k)
    (h : k ≤ halfOpenCount c (p n : ℝ)) :
    (p n : ℝ) < (p (n+k) : ℝ) ∧ (p (n+k) : ℝ) ≤ upper c (p n : ℝ) := by
  have hm := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  constructor
  · exact_mod_cast hm (show n < n+k by omega)
  · by_contra! hbad
    have hy : ⌊upper c (p n : ℝ)⌋₊ < p (n+k) :=
      (Nat.floor_lt' (Nat.prime_nth_prime (n+k)).ne_zero).2 hbad
    have ht := Nat.monotone_primeCounting' (Nat.succ_le_of_lt hy)
    change piReal (upper c (p n : ℝ)) ≤ Nat.primeCounting' (Nat.nth Nat.Prime (n+k)) at ht
    rw [Nat.primeCounting'_nth_eq] at ht
    change k ≤ piReal (upper c (p n : ℝ)) - piReal (p n : ℝ) at h
    rw [pi_at_prime] at h
    omega

theorem eventual_ranks {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → (k : ℝ) ≤ a*sqrt (p n : ℝ) →
      (p n : ℝ) < (p (n+k) : ℝ) ∧ (p (n+k) : ℝ) < upper c (p n : ℝ) := by
  obtain ⟨_,d,hd,hev⟩ := goodOpen_iff.mpr h
  have hp : Tendsto (fun n : ℕ => (p n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast (show n ≤ p n from (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))
  filter_upwards [hp.eventually hev] with n hn
  intro k hk hk'
  have hs : 0 < sqrt (p n : ℝ) := sqrt_pos.mpr (by
    exact_mod_cast (Nat.prime_nth_prime n).pos)
  apply prime_rank_open hk
  have hmul := (le_div_iff₀ hs).mp hn
  exact_mod_cast (show (k : ℝ) ≤ (openCount c (p n : ℝ) : ℝ) by
    nlinarith [mul_pos hd hs])

#print axioms above_envelope
#print axioms width3
#print axioms width5
#print axioms inverse3
#print axioms inverse5
#print axioms openCount_card
#print axioms eventual_ranks


def wA : ℝ := 3731134672774344/3112900821074735
def wB : ℝ := 9048441/2901640

def gInv (c : ℝ) : ℝ := (c-q)/(2*q)
def sInv (c : ℝ) : ℝ := (c-944247/1000000)/(1163388/1000000)
def fInv (c : ℝ) : ℝ := (c-9/8)/(16/15)

theorem break_widths : G A = wA ∧ S A = wA ∧ S B = wB ∧ F B = wB := by
  norm_num [G,q,A,B,wA,wB,RHWeightedPopulation.v1.sparseLine,
    RHWeightedPopulation.v1.flatLine]

theorem inverse_piecewise (c : ℝ) :
    (c ≤ wA → max (gInv c) (max (sInv c) (fInv c)) = gInv c) ∧
    (wA ≤ c → c ≤ wB → max (gInv c) (max (sInv c) (fInv c)) = sInv c) ∧
    (wB ≤ c → max (gInv c) (max (sInv c) (fInv c)) = fInv c) := by
  have hg (x : ℝ) : gInv x = (24680948495/41165122592)*x-1/2 := by
    unfold gInv q
    ring
  have hs (x : ℝ) : sInv x = (250000/290847)*x-314749/387796 := by
    unfold sInv
    ring
  have hab : wA ≤ wB := by norm_num [wA,wB]
  refine ⟨?_,?_,?_⟩
  · intro hc
    have hcf := hc.trans hab
    have h₁ : sInv c ≤ gInv c := by
      rw [hg,hs]
      unfold wA at *
      linarith
    have h₂ : fInv c ≤ sInv c := by
      unfold fInv sInv wB at *
      linarith
    simp only [max_eq_left h₂, max_eq_left h₁]
  · intro hc hb
    have h₁ : gInv c ≤ sInv c := by
      rw [hg,hs]
      unfold wA at *
      linarith
    have h₂ : fInv c ≤ sInv c := by
      unfold fInv sInv wB at *
      linarith
    simp only [max_eq_left h₂, max_eq_right h₁]
  · intro hc
    have hca := hab.trans hc
    have h₁ : gInv c ≤ sInv c := by
      rw [hg,hs]
      unfold wA at *
      linarith
    have h₂ : sInv c ≤ fInv c := by
      unfold fInv sInv wB at *
      linarith
    simp only [max_eq_right h₂, max_eq_right (h₁.trans h₂)]

def minWidthGain : ℝ := 13152201/1658080000

/-- Scalar comparison; the domain of the original application is octic_domain. -/
theorem min_gain (a : ℝ) :
    minWidthGain ≤ octic a-E a ∧ (octic a-E a = minWidthGain ↔ a = B) := by
  rcases lt_trichotomy a B with hb | rfl | hb
  · have hS : minWidthGain < octic a-S a := by
      unfold minWidthGain octic S RHWeightedPopulation.v1.sparseLine B at *
      linarith
    have hE : E a ≤ S a := (min_le_right _ _).trans (min_le_left _ _)
    have h : minWidthGain < octic a-E a := by linarith
    exact ⟨h.le, ⟨fun he => (ne_of_gt h he).elim, fun he => (hb.ne he).elim⟩⟩
  · rw [right_branch le_rfl]
    norm_num [minWidthGain, octic, RHWeightedPopulation.v1.flatLine, B]
  · have hF : minWidthGain < octic a-F a := by
      unfold minWidthGain octic F RHWeightedPopulation.v1.flatLine B at *
      linarith
    rw [right_branch hb.le]
    exact ⟨hF.le, ⟨fun he => (ne_of_gt hF he).elim, fun he => (hb.ne' he).elim⟩⟩

theorem octic_width_gains :
    octic t3-3 = 183638823/15511840000 ∧ octic t5-5 = 70933/640000 ∧
    octic 1-E 1 = 33027/800000 := by
  rw [middle_branch (by norm_num [A] : A ≤ 1) (by norm_num [B] : (1:ℝ) ≤ B)]
  norm_num [octic,t3,t5,RHWeightedPopulation.v1.sparseLine]

theorem strictOpen_width3 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodOpen t3 3 := goodOpen_iff.mpr (width3 hn hu rh)

theorem strictOpen_width5 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis) :
    GoodOpen t5 5 := goodOpen_iff.mpr (width5 hn hu rh)

theorem strictOpen_leading {a c : ℝ} (h : GoodOpen a c) :
    ∀ᶠ x : ℝ in atTop, a*sqrt x < (openCount c x : ℝ) := by
  obtain ⟨_,d,hd,hev⟩ := h
  filter_upwards [hev,eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hs : 0 < sqrt x := sqrt_pos.mpr (by linarith)
  exact (lt_div_iff₀ hs).mp ((lt_add_of_pos_right _ hd).trans_le hx)

theorem strictOpen_rank_floor {a c : ℝ} (ha : 0 ≤ a) (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k ≤ ⌊a * sqrt (p n : ℝ)⌋₊ + 1 →
      (p n : ℝ) < (p (n+k) : ℝ) ∧ (p (n+k) : ℝ) < upper c (p n : ℝ) := by
  have hp : Tendsto (fun n : ℕ => (p n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    exact_mod_cast (show n ≤ p n from (Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))
  filter_upwards [hp.eventually (strictOpen_leading (goodOpen_iff.mpr h))] with n hn
  intro k hk hk'
  apply prime_rank_open hk
  have hh := (Nat.floor_lt (mul_nonneg ha (sqrt_nonneg _))).mpr hn
  omega

#print axioms inverse_piecewise
#print axioms min_gain
#print axioms strictOpen_width3
#print axioms strictOpen_width5
#print axioms strictOpen_rank_floor


section WitnessRefinement
open RH080Next.Explicit AffineFourierPrograms.v1

def u3 : ℝ := 193269011844967139/109374342622661960
def u5 : ℝ := 31036198331144443607/8533333333333333328

/-- Separate from the three rounded input curves: use the underlying certified
norm upper bound and the general BR consumer directly. -/
theorem witness_width3 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < u3) : GoodCoefficient a 3 := by
  obtain ⟨_,hN,hJ,h0,hBound,hAttain⟩ :=
    RH080Next.PopulationCanonical.kernel_only_sparse_witness hn
  have hD : brDenominatorFour sparseNodes 8 =
      1-4*(119725872611533800/(8*1000000000000000000) : ℝ) := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
  have hN' : brAmplitudeMass sparseNodes 8 ≤
      (887721072633027910/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hu sparseNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,sparseNodes,sparseNumerators])
    (546871713113309800/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) 3 a (by norm_num) _ rh
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(546871713113309800/1000000000000000000))).2
  unfold u3 at ha
  linarith

theorem witness_width5 (hn : BRFourierInput.v1.norm_identity)
    (hu : BRFourierInput.v1.uniform_population_q1) (rh : RiemannHypothesis)
    {a : ℝ} (ha : a < u5) : GoodCoefficient a 5 := by
  obtain ⟨_,hN,hJ,h0,hBound,hAttain⟩ :=
    RH080Next.PopulationCanonical.kernel_only_flat_witness hn
  have hD : brDenominatorFour flatNodes 8 =
      ((15*533333333333333333)/(8*1000000000000000000) : ℝ) := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]; ring
  have hN' : brAmplitudeMass flatNodes 8 ≤
      (1120475208606944546/1000000000000000000 : ℝ) := hN
  apply source_BR_population_goodCoefficient hu flatNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,flatNodes,flatNumerators])
    (533333333333333333/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) 5 a (by norm_num) _ rh
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(533333333333333333/1000000000000000000))).2
  unfold u5 at ha
  linarith

theorem witness_gains :
    u3-t3 = 18015227286470921/10603733142924454360040 ∧
    u5-t5 = 289586649155549011/68266666666666666624 ∧
    u3-octicLead 3 = 1726734183826542841/164061513933992940000 ∧
    u5-octicLead 5 = 9864964558708324124141/95999999999999999940000 := by
  norm_num [u3,u5,t3,t5,octicLead]

#print axioms witness_width3
#print axioms witness_width5
#print axioms witness_gains
end WitnessRefinement

end RH080Transfer
