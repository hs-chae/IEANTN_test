import RH080EstimatePack
import PopulationActualConsumers
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Filter IEANTN.CMSFunctional
open scoped Topology

namespace WidthTransfer

abbrev q : ℝ := 20582561296 / 24680948495
def G (a : ℝ) : ℝ := q * (1 + 2*a)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine
abbrev u : ℝ := 544470055511653 / 2490320656859788
abbrev v : ℝ := 542259 / 290164
def envelope (a : ℝ) : ℝ := min (G a) (min (S a) (F a))

theorem breakpoints : 0 < u ∧ u < v ∧ G u = S u ∧ S v = F v := by
  norm_num [G, RHWeightedPopulation.v1.sparseLine, RHWeightedPopulation.v1.flatLine]

theorem gaussian_le_sparse {a : ℝ} : G a ≤ S a ↔ a ≤ u := by
  simp only [G, RHWeightedPopulation.v1.sparseLine, q, u]
  constructor <;> intro h <;> linarith only [h]

theorem sparse_le_gaussian {a : ℝ} : S a ≤ G a ↔ u ≤ a := by
  simp only [G, RHWeightedPopulation.v1.sparseLine, q, u]
  constructor <;> intro h <;> linarith only [h]

theorem sparse_le_flat {a : ℝ} : S a ≤ F a ↔ a ≤ v := by
  simp only [RHWeightedPopulation.v1.sparseLine, RHWeightedPopulation.v1.flatLine, v]
  constructor <;> intro h <;> linarith only [h]

theorem flat_le_sparse {a : ℝ} : F a ≤ S a ↔ v ≤ a := by
  simp only [RHWeightedPopulation.v1.sparseLine, RHWeightedPopulation.v1.flatLine, v]
  constructor <;> intro h <;> linarith only [h]

theorem envelope_gaussian {a : ℝ} (h : a ≤ u) : envelope a = G a := by
  rw [envelope, min_eq_left (sparse_le_flat.mpr (h.trans breakpoints.2.1.le)),
    min_eq_left (gaussian_le_sparse.mpr h)]

theorem envelope_sparse {a : ℝ} (hu : u ≤ a) (hv : a ≤ v) : envelope a = S a := by
  rw [envelope, min_eq_left (sparse_le_flat.mpr hv), min_eq_right (sparse_le_gaussian.mpr hu)]

theorem envelope_flat {a : ℝ} (hv : v ≤ a) : envelope a = F a := by
  rw [envelope, min_eq_right (flat_le_sparse.mpr hv),
    min_eq_right ((flat_le_sparse.mpr hv).trans
      (sparse_le_gaussian.mpr (breakpoints.2.1.le.trans hv)))]

theorem envelope_piecewise (a : ℝ) :
    envelope a = if a < u then G a else if a ≤ v then S a else F a := by
  split_ifs with h hv
  · exact envelope_gaussian h.le
  · exact envelope_sparse (le_of_not_gt h) hv
  · exact envelope_flat (le_of_not_ge hv)

abbrev monoWidth := @RHOnePrime.CMSFunctional.goodCoefficient_mono

theorem attained (hS : RHWeightedPopulation.v1.sparse_curve)
    (hF : RHWeightedPopulation.v1.flat_curve) {a : ℝ} (ha : u ≤ a) :
    GoodCoefficient a (envelope a) := by
  have h0 : 0 ≤ a := breakpoints.1.le.trans ha
  by_cases hv : a ≤ v
  · rw [envelope_sparse ha hv]; exact hS a h0
  · rw [envelope_flat (le_of_not_ge hv)]; exact hF a h0

theorem aboveEnvelope (hG : RHAsymptoticGaussian.v4.population_curve)
    (hS : RHWeightedPopulation.v1.sparse_curve) (hF : RHWeightedPopulation.v1.flat_curve)
    {a c : ℝ} (ha : 0 ≤ a) (hc : envelope a < c) : GoodCoefficient a c := by
  by_cases h : a < u
  · rw [envelope_gaussian h.le] at hc
    have hw := hG a ha (c-G a) (sub_pos.mpr hc)
    change GoodCoefficient a (G a+(c-G a)) at hw
    rwa [show G a+(c-G a)=c by ring] at hw
  · exact monoWidth (attained hS hF (le_of_not_gt h)) hc.le

theorem aboveEnvelope_sourceFirstBR (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hNorm : BRFourierInput.v1.norm_identity) (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) {a c : ℝ} (ha : 0 ≤ a) (hc : envelope a < c) :
    GoodCoefficient a c :=
  aboveEnvelope (RH080Exposure.Estimates.gaussian hCMS hRH)
    (RH080Next.PopulationCanonical.source_first_sparse_curve hNorm hUniform hRH)
    (RH080Next.PopulationCanonical.source_first_flat_curve hNorm hUniform hRH) ha hc

theorem attained_sourceFirstBR (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {a : ℝ} (ha : u ≤ a) : GoodCoefficient a (envelope a) :=
  attained (RH080Next.PopulationCanonical.source_first_sparse_curve hNorm hUniform hRH)
    (RH080Next.PopulationCanonical.source_first_flat_curve hNorm hUniform hRH) ha

def gInv (c : ℝ) : ℝ := (c/q - 1)/2
def sInv (c : ℝ) : ℝ := (c-944247/1000000)/(1163388/1000000)
def fInv (c : ℝ) : ℝ := (c-9/8)/(16/15)
def invEnvelope (c : ℝ) : ℝ := max (gInv c) (max (sInv c) (fInv c))
abbrev a3 : ℝ := 685251/387796
abbrev a5 : ℝ := 465/128

theorem inverse_iff {a c : ℝ} : envelope a ≤ c ↔ a ≤ invEnvelope c := by
  have hg : G a ≤ c ↔ a ≤ gInv c := by
    simp only [G, gInv, q]
    constructor <;> intro h <;> linarith only [h]
  have hs : S a ≤ c ↔ a ≤ sInv c := by
    simp only [RHWeightedPopulation.v1.sparseLine, sInv]
    constructor <;> intro h <;> linarith only [h]
  have hf : F a ≤ c ↔ a ≤ fInv c := by
    simp only [RHWeightedPopulation.v1.flatLine, fInv]
    constructor <;> intro h <;> linarith only [h]
  simp only [envelope, invEnvelope, min_le_iff, le_max_iff, hg, hs, hf]

theorem widths_inverse : invEnvelope 3 = a3 ∧ invEnvelope 5 = a5 := by
  norm_num [invEnvelope, gInv, sInv, fInv, q, a3, a5, max_def]

theorem envelope_at_widths : envelope a3 = 3 ∧ envelope a5 = 5 := by
  constructor
  · rw [envelope_sparse (by norm_num [u, a3]) (by norm_num [v, a3])]
    norm_num [RHWeightedPopulation.v1.sparseLine, a3]
  · rw [envelope_flat (by norm_num [v, a5])]
    norm_num [RHWeightedPopulation.v1.flatLine, a5]

theorem good_three (hS : RHWeightedPopulation.v1.sparse_curve) : GoodCoefficient a3 3 := by
  have h := hS a3 (by norm_num [a3])
  rwa [show RHWeightedPopulation.v1.sparseLine a3 = 3 by norm_num [RHWeightedPopulation.v1.sparseLine, a3]] at h

theorem good_five (hF : RHWeightedPopulation.v1.flat_curve) : GoodCoefficient a5 5 := by
  have h := hF a5 (by norm_num [a5])
  rwa [show RHWeightedPopulation.v1.flatLine a5 = 5 by norm_num [RHWeightedPopulation.v1.flatLine, a5]] at h

def upper (c x : ℝ) : ℝ := x+c*Real.sqrt x*Real.log x
def halfPrimes (c x : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊upper c x⌋₊ \ Nat.primesLE ⌊x⌋₊
def strictPrimes (c x : ℝ) : Finset ℕ :=
  (halfPrimes c x).filter (fun p : ℕ => (p : ℝ) < upper c x)
abbrev strictCount (c x : ℝ) : ℕ := (strictPrimes c x).card

theorem mem_halfPrimes {c x : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ upper c x) {p : ℕ} :
    p ∈ halfPrimes c x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ upper c x := by
  simp only [halfPrimes, Finset.mem_sdiff, Nat.mem_primesLE, Nat.le_floor_iff hx,
    Nat.le_floor_iff hy]
  constructor
  · intro h
    exact ⟨h.1.2, lt_of_not_ge (fun hp => h.2 ⟨hp,h.1.2⟩), h.1.1⟩
  · intro h
    exact ⟨⟨h.2.2,h.1⟩, fun hp => (not_le_of_gt h.2.1) hp.1⟩

theorem mem_strictPrimes {c x : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ upper c x) {p : ℕ} :
    p ∈ strictPrimes c x ↔ p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  simp only [strictPrimes, Finset.mem_filter, mem_halfPrimes hx hy]
  exact ⟨fun h => ⟨h.1.1,h.1.2.1,h.2⟩, fun h => ⟨⟨h.1,h.2.1,h.2.2.le⟩,h.2.2⟩⟩

theorem halfPrimes_card {c x : ℝ} (h : x ≤ upper c x) :
    (halfPrimes c x).card = halfOpenCount c x := by
  have hs := Finset.card_sdiff_add_card_eq_card
    (Nat.primesLE_mono (Nat.floor_mono h))
  change (halfPrimes c x).card + (Nat.primesLE ⌊x⌋₊).card =
    (Nat.primesLE ⌊upper c x⌋₊).card at hs
  simp only [Nat.primesLE_card_eq_primeCounting] at hs
  unfold halfOpenCount piReal upper at *
  omega

theorem endpoint_loss {c x : ℝ} (hx : 0 ≤ x) (h : x ≤ upper c x) :
    strictCount c x ≤ halfOpenCount c x ∧
    halfOpenCount c x ≤ strictCount c x + 1 := by
  classical
  let p : ℕ → Prop := fun n => (n : ℝ) < upper c x
  let bad := (halfPrimes c x).filter (fun n => ¬ p n)
  have hb : bad.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ea (n : ℕ) (hn : n ∈ bad) : (n : ℝ) = upper c x := by
      have hh := Finset.mem_filter.mp hn
      exact le_antisymm ((mem_halfPrimes hx (hx.trans h)).1 hh.1).2.2
        (le_of_not_gt hh.2)
    exact_mod_cast (ea a ha).trans (ea b hb).symm
  have hcard := Finset.card_filter_add_card_filter_not (s := halfPrimes c x) p
  change strictCount c x + bad.card = (halfPrimes c x).card at hcard
  rw [halfPrimes_card h] at hcard
  omega

theorem lower_le_upper {c x : ℝ} (hc : 0 ≤ c) (hx : 1 ≤ x) : x ≤ upper c x := by
  unfold upper
  have hnon := mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg x)) (Real.log_nonneg hx)
  linarith

theorem strictMargin_of_good {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop, a+d ≤ (strictCount c x : ℝ)/Real.sqrt x := by
  rcases h with ⟨hc,d,hd,he⟩
  have hd2 : 0 < d/2 := by positivity
  refine ⟨d/2,hd2,?_⟩
  filter_upwards [he, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2/d)^2)] with x hx hx2 hxsq
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_pos.2 hx0
  have hs2 : 2/d ≤ Real.sqrt x := by
    simpa [Real.sqrt_sq (by positivity : 0 ≤ 2/d)] using Real.sqrt_le_sqrt hxsq
  have h1 : 1 ≤ (d/2)*Real.sqrt x := by
    have hm := (div_le_iff₀ hd).mp hs2
    nlinarith only [hm]
  have hcount : (halfOpenCount c x : ℝ) ≤ (strictCount c x : ℝ) + 1 := by
    exact_mod_cast (endpoint_loss hx0.le (lower_le_upper hc.le (by linarith))).2
  have hpop := (le_div_iff₀ hs).mp hx
  apply (le_div_iff₀ hs).2
  linarith only [hcount,hpop,h1]

theorem strict_of_margin {a c : ℝ}
    (h : ∃ d > 0, ∀ᶠ x : ℝ in atTop, a+d ≤ (strictCount c x : ℝ)/Real.sqrt x) :
    ∀ᶠ x : ℝ in atTop, a*Real.sqrt x < (strictCount c x : ℝ) := by
  rcases h with ⟨d,hd,he⟩
  filter_upwards [he, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hs := Real.sqrt_pos.2 (show 0 < x by linarith)
  exact (lt_div_iff₀ hs).mp ((lt_add_of_pos_right _ hd).trans_le hx)

theorem strict_of_good {a c : ℝ} (h : GoodCoefficient a c) :
    ∀ᶠ x : ℝ in atTop, a*Real.sqrt x < (strictCount c x : ℝ) :=
  strict_of_margin (strictMargin_of_good h)

theorem widths3and5_kernel (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    GoodCoefficient a3 3 ∧ GoodCoefficient a5 5 ∧
      ∀ᶠ x : ℝ in atTop, a3*Real.sqrt x < (strictCount 3 x : ℝ) ∧
        a5*Real.sqrt x < (strictCount 5 x : ℝ) := by
  have h3 := good_three (RH080Exposure.Estimates.sparse hNorm hUniform hRH)
  have h5 := good_five (RH080Exposure.Estimates.flat hNorm hUniform hRH)
  exact ⟨h3,h5,(strict_of_good h3).and (strict_of_good h5)⟩

theorem widths3and5_sourceFirst (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    GoodCoefficient a3 3 ∧ GoodCoefficient a5 5 ∧
      ∀ᶠ x : ℝ in atTop, a3*Real.sqrt x < (strictCount 3 x : ℝ) ∧
        a5*Real.sqrt x < (strictCount 5 x : ℝ) := by
  have h3 := good_three (RH080Next.PopulationCanonical.source_first_sparse_curve hNorm hUniform hRH)
  have h5 := good_five (RH080Next.PopulationCanonical.source_first_flat_curve hNorm hUniform hRH)
  exact ⟨h3,h5,(strict_of_good h3).and (strict_of_good h5)⟩

theorem liminfInv_lower
    (hG : RHAsymptoticGaussian.v4.population_curve)
    (hS : RHWeightedPopulation.v1.sparse_curve) (hF : RHWeightedPopulation.v1.flat_curve)
    {c η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, max 0 (invEnvelope c)-η ≤ (strictCount c x : ℝ)/Real.sqrt x := by
  by_cases h : 0 ≤ max 0 (invEnvelope c)-η
  · have hap : max 0 (invEnvelope c)-η < invEnvelope c := by
      rcases le_total 0 (invEnvelope c) with hpos | hneg
      · rw [max_eq_right hpos]; linarith
      · rw [max_eq_left hneg] at h; linarith
    let a := max 0 (invEnvelope c)-η
    have hE : envelope a < c := by
      rcases (lt_max_iff.mp hap) with hg | hsf
      · apply lt_of_le_of_lt (min_le_left _ _)
        simp only [gInv, q] at hg
        unfold G q
        linarith only [hg]
      · rcases (lt_max_iff.mp hsf) with hs | hf
        · apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
          simp only [sInv] at hs
          simp only [S, RHWeightedPopulation.v1.sparseLine]
          linarith only [hs]
        · apply lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
          simp only [fInv] at hf
          simp only [F, RHWeightedPopulation.v1.flatLine]
          linarith only [hf]
    obtain ⟨d,hd,he⟩ := strictMargin_of_good (aboveEnvelope hG hS hF h hE)
    filter_upwards [he] with x hx
    linarith
  · exact Eventually.of_forall fun x => (le_of_not_ge h).trans (by positivity)

def oldWidth (a : ℝ) : ℝ := (9/8)*(a+18203/20000)
def oldLead (c : ℝ) : ℝ := (8/9)*c-18203/20000

theorem oldDomain (a : ℝ) :
    (103/100 ≤ oldWidth a ∧ oldWidth a ≤ 16) ↔
      (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold oldWidth
  constructor <;> intro h <;> constructor <;> linarith only [h.1,h.2]

theorem exact_gains_width :
    (∀ a ≤ u, oldWidth a-envelope a = 163827/160000-q+(9/8-2*q)*a) ∧
    (∀ a, u ≤ a → a ≤ v → oldWidth a-envelope a =
      318687/4000000-(9597/250000)*a) ∧
    (∀ a ≥ v, oldWidth a-envelope a = -(16173/160000)+(7/120)*a) := by
  refine ⟨?_,?_,?_⟩
  · intro a h; rw [envelope_gaussian h]; unfold oldWidth G; ring
  · intro a hu hv; rw [envelope_sparse hu hv]; simp only [oldWidth,S,RHWeightedPopulation.v1.sparseLine]; ring
  · intro a h; rw [envelope_flat h]; simp only [oldWidth,F,RHWeightedPopulation.v1.flatLine]; ring

theorem gain_on_old_domain {a : ℝ} (_hlo : 103/100 ≤ oldWidth a)
    (_hhi : oldWidth a ≤ 16) : envelope a < oldWidth a := by
  rcases le_total a 2 with h | h
  · have hh : S a < oldWidth a := by
      simp only [oldWidth,S,RHWeightedPopulation.v1.sparseLine]; linarith only [h]
    exact ((min_le_right _ _).trans (min_le_left _ _)).trans_lt hh
  · have hh : F a < oldWidth a := by
      simp only [oldWidth,F,RHWeightedPopulation.v1.flatLine]; linarith only [h]
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt hh

theorem gain_at_widths :
    a3-oldLead 3 = 61212941/5816940000 ∧ a5-oldLead 5 = 70933/720000 ∧
    oldWidth a3-3 = 183638823/15511840000 ∧ oldWidth a5-5 = 70933/640000 := by
  norm_num [oldWidth, oldLead, a3, a5]

open RH080Next.Explicit AffineFourierPrograms.v1

abbrev Ds : ℝ := 1-4*(119725872611533800/(8*1000000000000000000))
abbrev Ms : ℝ := 546871713113309800/1000000000000000000
abbrev Ls : ℝ := 887721072633027910/1000000000000000000
abbrev Df : ℝ := (15*533333333333333333)/(8*1000000000000000000)
abbrev Mf : ℝ := 533333333333333333/1000000000000000000
abbrev Lf : ℝ := 1120475208606944546/1000000000000000000
def rawSparse (c : ℝ) : ℝ := (c*Ds-Ls)/(2*Ms)
def rawFlat (c : ℝ) : ℝ := (c*Df-Lf)/(2*Mf)
abbrev b3 : ℝ := 193269011844967139/109374342622661960
abbrev b5 : ℝ := 31036198331144443607/8533333333333333328

theorem good_of_rawSparse (hW : sparse_witness)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {a c : ℝ} (hc : 0 < c) (ha : a < rawSparse c) : GoodCoefficient a c := by
  rcases hW with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 = Ds := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
  apply source_BR_population_goodCoefficient hUniform sparseNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,sparseNodes,sparseNumerators])
    Ms (by norm_num [Ms]) hBound hAttain (by rw [hD]; norm_num [Ds]) c a hc _ hRH
  change brAmplitudeMass sparseNodes 8 ≤ Ls at hN
  rw [hD]
  exact ha.trans_le (div_le_div_of_nonneg_right (sub_le_sub_left hN _)
    (by norm_num [Ms]))

theorem good_of_rawFlat (hW : flat_witness)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {a c : ℝ} (hc : 0 < c) (ha : a < rawFlat c) : GoodCoefficient a c := by
  rcases hW with ⟨_,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 = Df := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]; ring
  apply source_BR_population_goodCoefficient hUniform flatNodes 8 (by norm_num)
    (by decide) (by decide) (by norm_num [node,flatNodes,flatNumerators])
    Mf (by norm_num [Mf]) hBound hAttain (by rw [hD]; norm_num [Df]) c a hc _ hRH
  change brAmplitudeMass flatNodes 8 ≤ Lf at hN
  rw [hD]
  exact ha.trans_le (div_le_div_of_nonneg_right (sub_le_sub_left hN _)
    (by norm_num [Mf]))

theorem raw_gains :
    max (rawSparse 3) (rawFlat 3) = b3 ∧ max (rawSparse 5) (rawFlat 5) = b5 ∧
    a3 < b3 ∧ a5 < b5 ∧
    b3-oldLead 3 = 1726734183826542841/164061513933992940000 ∧
    b5-oldLead 5 = 9864964558708324124141/95999999999999999940000 := by
  norm_num [rawSparse,rawFlat,Ds,Ms,Ls,Df,Mf,Lf,b3,b5,a3,a5,oldLead,max_def]

theorem raw_widths_sourceFirst (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    (∀ a < b3, GoodCoefficient a 3) ∧ (∀ a < b5, GoodCoefficient a 5) := by
  have h3 : rawSparse 3 = b3 := by norm_num [rawSparse,Ds,Ls,Ms,b3]
  have h5 : rawFlat 5 = b5 := by norm_num [rawFlat,Df,Lf,Mf,b5]
  exact ⟨fun a ha => good_of_rawSparse (challenge_sparse_witness hNorm)
    hUniform hRH (by norm_num) (h3.symm ▸ ha),
    fun a ha => good_of_rawFlat (challenge_flat_witness hNorm)
    hUniform hRH (by norm_num) (h5.symm ▸ ha)⟩

theorem raw_strict_lower_sourceFirst (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, b3-η ≤ (strictCount 3 x : ℝ)/Real.sqrt x ∧
      b5-η ≤ (strictCount 5 x : ℝ)/Real.sqrt x := by
  obtain ⟨h3,h5⟩ := raw_widths_sourceFirst hNorm hUniform hRH
  obtain ⟨d3,hd3,e3⟩ := strictMargin_of_good (h3 (b3-η) (by linarith))
  obtain ⟨d5,hd5,e5⟩ := strictMargin_of_good (h5 (b5-η) (by linarith))
  filter_upwards [e3,e5] with x hx hy
  exact ⟨by linarith,by linarith⟩

theorem primeAt_rank (n : ℕ) : piReal (primeAt n : ℝ) = n+1 := by
  rw [piReal, Nat.floor_natCast, Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (primeAt n+1) = n+1
  rw [Nat.count_succ]
  change (primeAt n).primeCounting' + (if (primeAt n).Prime then 1 else 0) = n+1
  simp [primeAt]

theorem strictCount_at_prime {c : ℝ} (hc : 0 < c) (n : ℕ) :
    strictCount c (primeAt n : ℝ) =
      Nat.primeCounting' ⌈upper c (primeAt n : ℝ)⌉₊ - (n+1) := by
  let x : ℝ := primeAt n
  let y := upper c x
  have hx : 1 < x := by
    have hp := Nat.add_two_le_nth_prime n
    change 1 < (Nat.nth Nat.Prime n : ℝ)
    exact_mod_cast (show 1 < Nat.nth Nat.Prime n by omega)
  have hxy : x < y := by
    dsimp [y,upper]
    have hp := mul_pos (mul_pos hc (Real.sqrt_pos.2 (by linarith))) (Real.log_pos hx)
    linarith
  have hip : primeAt n < ⌈y⌉₊ := Nat.lt_ceil.mpr hxy
  have hs : Nat.primesLE (primeAt n) ⊆ Nat.primesBelow ⌈y⌉₊ := by
    intro p hp
    obtain ⟨hp1,hp2⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesBelow.mpr ⟨hp1.trans_lt hip,hp2⟩
  have heq : strictPrimes c x = Nat.primesBelow ⌈y⌉₊ \ Nat.primesLE (primeAt n) := by
    ext p
    simp only [mem_strictPrimes (by linarith : 0 ≤ x) (by linarith : 0 ≤ y),
      Finset.mem_sdiff, Nat.mem_primesBelow, Nat.mem_primesLE, Nat.lt_ceil]
    constructor
    · intro h
      exact ⟨⟨h.2.2,h.1⟩, fun h' => (not_le_of_gt h.2.1) (by change (p : ℝ) ≤ (primeAt n : ℝ); exact_mod_cast h'.1)⟩
    · intro h
      refine ⟨h.1.2, lt_of_not_ge (fun hp => h.2 ⟨?_,h.1.2⟩), h.1.1⟩
      change (p : ℝ) ≤ (primeAt n : ℝ) at hp
      exact_mod_cast hp
  have hr : (primeAt n).primeCounting = n+1 := by
    simpa only [piReal, Nat.floor_natCast] using primeAt_rank n
  have hcard := Finset.card_sdiff_add_card_eq_card hs
  rw [← heq, Nat.primesLE_card_eq_primeCounting, hr,
    Nat.primesBelow_card_eq_primeCounting'] at hcard
  change (strictPrimes c x).card = Nat.primeCounting' ⌈y⌉₊ - (n+1)
  omega

theorem rank_from_strict {c : ℝ} (hc : 0 < c) (n k : ℕ) (hk : 0 < k)
    (h : k ≤ strictCount c (primeAt n : ℝ)) :
    (primeAt (n+k) : ℝ) < upper c (primeAt n : ℝ) := by
  rw [strictCount_at_prime hc n] at h
  apply Nat.lt_ceil.mp
  by_contra! ht
  have hb := Nat.monotone_primeCounting' ht
  have hn : (primeAt (n+k)).primeCounting' = n+k := Nat.primeCounting'_nth_eq _
  rw [hn] at hb
  omega

theorem primeAt_tendsto : Tendsto (fun n : ℕ => (primeAt n : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro x
  filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
  apply (Nat.ceil_le).mp
  exact hn.trans ((Nat.le_add_right n 2).trans (Nat.add_two_le_nth_prime n))

theorem eventual_rank_of_good {a c : ℝ} (ha : 0 ≤ a) (h : GoodCoefficient a c) :
    ∀ᶠ n : ℕ in atTop, (primeAt (n+(⌊a*Real.sqrt (primeAt n : ℝ)⌋₊+1)) : ℝ) <
      upper c (primeAt n : ℝ) := by
  have he := primeAt_tendsto.eventually (strict_of_good h)
  filter_upwards [he] with n hn
  apply rank_from_strict h.1 n _ (by omega)
  exact Nat.succ_le_of_lt ((Nat.floor_lt (mul_nonneg ha (Real.sqrt_nonneg _))).2 hn)

end WidthTransfer

#print axioms WidthTransfer.aboveEnvelope_sourceFirstBR
#print axioms WidthTransfer.attained_sourceFirstBR
#print axioms WidthTransfer.widths3and5_kernel
#print axioms WidthTransfer.widths3and5_sourceFirst

#print axioms WidthTransfer.liminfInv_lower
#print axioms WidthTransfer.raw_strict_lower_sourceFirst
#print axioms WidthTransfer.exact_gains_width

#print axioms WidthTransfer.eventual_rank_of_good
