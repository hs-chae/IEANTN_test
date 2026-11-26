import RH080EstimatePack
import PopulationActualConsumers

set_option autoImplicit false
noncomputable section
open Filter Real IEANTN.CMSFunctional
open scoped Nat
namespace Transfer

def q : ℝ := 20582561296/24680948495
def G (a : ℝ) : ℝ := q*(1+2*a)
abbrev S := RHWeightedPopulation.v1.sparseLine
abbrev F := RHWeightedPopulation.v1.flatLine
def A : ℝ := 544470055511653/2490320656859788
def B : ℝ := 542259/290164
def T : ℝ := 172404138261/356130660736
def E (a : ℝ) : ℝ := min (G a) (min (S a) (F a))
def t3 : ℝ := 685251/387796
def t5 : ℝ := 465/128

theorem crossings : G A = S A ∧ S B = F B ∧ G T = F T ∧
    0 < A ∧ A < T ∧ T < B := by
  norm_num [G,S,F,q,A,B,T,RHWeightedPopulation.v1.sparseLine,
    RHWeightedPopulation.v1.flatLine]

theorem envelope_left {a : ℝ} (h : a ≤ A) : E a = G a := by
  have h' : a ≤ T := h.trans crossings.2.2.2.2.1.le
  unfold E
  apply min_eq_left
  apply le_min <;>
    unfold A T at * <;>
    dsimp [G,q,S,F,RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine] <;>
    linarith

theorem envelope_middle {a : ℝ} (h : A ≤ a) (k : a ≤ B) : E a = S a := by
  have hGS : S a ≤ G a := by
    unfold A at h
    dsimp [G,q,S,RHWeightedPopulation.v1.sparseLine]
    linarith
  have hSF : S a ≤ F a := by
    unfold B at k
    dsimp [S,F,RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine]
    linarith
  simp [E,min_eq_left hSF,min_eq_right hGS]

theorem envelope_right {a : ℝ} (h : B ≤ a) : E a = F a := by
  have h' : T ≤ a := crossings.2.2.2.2.2.le.trans h
  have hGF : F a ≤ G a := by
    unfold T at h'
    dsimp [G,q,F,RHWeightedPopulation.v1.flatLine]
    linarith
  have hSF : F a ≤ S a := by
    unfold B at h
    dsimp [S,F,RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine]
    linarith
  simp [E,min_eq_right hSF,min_eq_right hGF]


/-- Widths certified by these three line statements and upward transport.
This is not a definition of every GoodCoefficient for the actual primes. -/
def LineCertificate (a c : ℝ) : Prop := G a < c ∨ S a ≤ c ∨ F a ≤ c

theorem line_certificate_exact {a c : ℝ} :
    LineCertificate a c ↔ E a < c ∨ (A ≤ a ∧ E a = c) := by
  constructor
  · intro h
    have hc : E a ≤ c := by
      rcases h with hg | hs | hf
      · exact (min_le_left _ _).trans hg.le
      · exact (min_le_right _ _).trans ((min_le_left _ _).trans hs)
      · exact (min_le_right _ _).trans ((min_le_right _ _).trans hf)
    rcases lt_or_eq_of_le hc with hlt | heq
    · exact Or.inl hlt
    · refine Or.inr ⟨?_,heq⟩
      by_contra! hab
      have he := envelope_left hab.le
      have hat : a < T := hab.trans crossings.2.2.2.2.1
      have hs' : G a < S a := by
        dsimp [A] at hab
        dsimp [G,q,S,RHWeightedPopulation.v1.sparseLine]
        linarith
      have hf' : G a < F a := by
        dsimp [T] at hat
        dsimp [G,q,F,RHWeightedPopulation.v1.flatLine]
        linarith
      rw [he] at heq
      rcases h with hg | hs | hf <;> linarith
  · intro h
    rcases le_or_gt A a with hab | hab
    · have hc : E a ≤ c := h.elim (fun hh => hh.le) (fun hh => hh.2.le)
      rcases le_total a B with hB | hB
      · rw [envelope_middle hab hB] at hc
        exact Or.inr (Or.inl hc)
      · rw [envelope_right hB] at hc
        exact Or.inr (Or.inr hc)
    · rcases h with hlt | ⟨ha,_⟩
      · rw [envelope_left hab.le] at hlt
        exact Or.inl hlt
      · exact False.elim ((not_le_of_gt hab) ha)

abbrev CMS := CMSFunctionalInput.v1.population_reduction
abbrev BRNorm := BRFourierInput.v1.norm_identity
abbrev BRPop := BRFourierInput.v1.uniform_population_q1
open RH080Exposure.Estimates
open RH080Next.PopulationCanonical

theorem good_at_envelope (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis)
    {a : ℝ} (ha : 0 ≤ a) (hA : A ≤ a) : GoodCoefficient a (E a) := by
  rcases le_total a B with hb | hb
  · rw [envelope_middle hA hb]
    exact source_first_sparse_curve hn hu rh a ha
  · rw [envelope_right hb]
    exact source_first_flat_curve hn hu rh a ha

theorem good_above_envelope (hc : CMS) (hn : BRNorm) (hu : BRPop)
    (rh : RiemannHypothesis) {a c : ℝ} (ha : 0 ≤ a) (h : E a < c) :
    GoodCoefficient a c := by
  rcases le_total A a with hA | hA
  · exact RHOnePrime.CMSFunctional.goodCoefficient_mono
      (good_at_envelope hn hu rh ha hA) h.le
  · rw [envelope_left hA] at h
    have hg := gaussian hc rh a ha (c-G a) (sub_pos.mpr h)
    change GoodCoefficient a (G a + (c-G a)) at hg
    rwa [show G a + (c-G a)=c by ring] at hg

theorem good_below_gaussian_target (hc : CMS) (rh : RiemannHypothesis)
    {a b : ℝ} (hb : 0 ≤ b) (h : b < a) : GoodCoefficient b (G a) := by
  have hd : 0 < G a - G b := by
    dsimp [G,q]
    linarith
  have hg := gaussian hc rh b hb (G a-G b) hd
  change GoodCoefficient b (G b+(G a-G b)) at hg
  rwa [show G b+(G a-G b)=G a by ring] at hg

def upper (c x : ℝ) : ℝ := x+c*sqrt x*log x

def halfSet (c x : ℝ) : Finset ℕ :=
  Nat.primesLE (Nat.floor (upper c x)) \ Nat.primesLE (Nat.floor x)

def openSet (c x : ℝ) : Finset ℕ :=
  (halfSet c x).filter (fun p : ℕ => (p : ℝ) < upper c x)

theorem mem_halfSet {c x : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ upper c x) (p : ℕ) :
    p ∈ halfSet c x ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ upper c x := by
  simp only [halfSet, Finset.mem_sdiff, Nat.mem_primesLE,
    Nat.le_floor_iff hx, Nat.le_floor_iff hy]
  constructor
  · rintro ⟨⟨hq,hp⟩,hn⟩
    exact ⟨hp,lt_of_not_ge (fun h => hn ⟨h,hp⟩),hq⟩
  · rintro ⟨hp,hl,hq⟩
    exact ⟨⟨hq,hp⟩,fun h => (not_le_of_gt hl) h.1⟩

theorem mem_openSet {c x : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ upper c x) (p : ℕ) :
    p ∈ openSet c x ↔ Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < upper c x := by
  simp only [openSet,Finset.mem_filter,mem_halfSet hx hy]
  constructor
  · rintro ⟨⟨hp,hx',_⟩,hy'⟩
    exact ⟨hp,hx',hy'⟩
  · rintro ⟨hp,hx',hy'⟩
    exact ⟨⟨hp,hx',hy'.le⟩,hy'⟩

theorem halfSet_card {c x : ℝ} (h : x ≤ upper c x) :
    (halfSet c x).card = halfOpenCount c x := by
  have hs := Nat.primesLE_mono (Nat.floor_mono (show x ≤ x+c*sqrt x*log x from h))
  simp only [halfSet, Finset.card_sdiff, Finset.inter_eq_left.mpr hs,
    Nat.primesLE_card_eq_primeCounting, halfOpenCount, piReal, upper]

theorem endpoint_bound {c x : ℝ} (hx : 0 ≤ x) (h : x ≤ upper c x) :
    halfOpenCount c x ≤ (openSet c x).card + 1 := by
  rw [← halfSet_card h]
  have hs : halfSet c x ⊆ insert (Nat.floor (upper c x)) (openSet c x) := by
    intro p hp
    obtain ⟨_,_,hy⟩ := (mem_halfSet hx (hx.trans h) p).1 hp
    rcases lt_or_eq_of_le hy with hh | hh
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp,hh⟩)
    · rw [← hh, Nat.floor_natCast]
      exact Finset.mem_insert_self _ _
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

theorem both_counts_of_good {a c : ℝ} (h : GoodCoefficient a c) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop,
      (a+d)*sqrt x ≤ (halfOpenCount c x : ℝ) ∧
      (a+d)*sqrt x ≤ ((openSet c x).card : ℝ) := by
  rcases h with ⟨hc,δ,hδ,hev⟩
  refine ⟨δ/2,by positivity,?_⟩
  filter_upwards [hev, eventually_ge_atTop (2 : ℝ),
    eventually_ge_atTop ((2/δ)^2)] with x hp hx hbig
  have hx0 : 0 ≤ x := by linarith
  have hs : 0 < sqrt x := sqrt_pos.mpr (by linarith)
  have ht : x ≤ upper c x := by
    unfold upper
    exact le_add_of_nonneg_right
      (mul_nonneg (mul_nonneg hc.le hs.le) (log_nonneg (by linarith)))
  have hn : (a+δ)*sqrt x ≤ (halfOpenCount c x : ℝ) := (le_div_iff₀ hs).1 hp
  have hs' : 2/δ ≤ sqrt x := by
    have hh := Real.sq_sqrt hx0
    by_contra! hab
    have hprod : 0 < (2/δ-sqrt x)*(2/δ+sqrt x) :=
      mul_pos (sub_pos.mpr hab) (add_pos (by positivity) hs)
    nlinarith only [hh,hprod,hbig]
  have hk : 1 ≤ (δ/2)*sqrt x := by
    have hh := (div_le_iff₀ hδ).1 hs'
    linarith
  have hb : (halfOpenCount c x : ℝ) ≤ ((openSet c x).card : ℝ) + 1 := by
    exact_mod_cast endpoint_bound hx0 ht
  have hid : (a+δ/2)*sqrt x + (δ/2)*sqrt x = (a+δ)*sqrt x := by ring
  constructor <;> linarith

theorem width3_good_of (h : RHWeightedPopulation.v1.sparse_curve) : GoodCoefficient t3 3 := by
  have ht : S t3 = 3 := by norm_num [t3,RHWeightedPopulation.v1.sparseLine]
  rw [← ht]
  exact h t3 (by norm_num [t3])

theorem width5_good_of (h : RHWeightedPopulation.v1.flat_curve) : GoodCoefficient t5 5 := by
  have ht : F t5 = 5 := by norm_num [t5,RHWeightedPopulation.v1.flatLine]
  rw [← ht]
  exact h t5 (by norm_num [t5])

theorem width3_kernel (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    GoodCoefficient t3 3 := width3_good_of (sparse hn hu rh)
theorem width5_kernel (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    GoodCoefficient t5 5 := width5_good_of (flat hn hu rh)

theorem width3_actual (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    GoodCoefficient t3 3 := width3_good_of (source_first_sparse_curve hn hu rh)
theorem width5_actual (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    GoodCoefficient t5 5 := width5_good_of (source_first_flat_curve hn hu rh)

theorem width3_counts (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop,
      (t3+d)*sqrt x ≤ (halfOpenCount 3 x : ℝ) ∧
      (t3+d)*sqrt x ≤ ((openSet 3 x).card : ℝ) :=
  both_counts_of_good (width3_actual hn hu rh)
theorem width5_counts (hn : BRNorm) (hu : BRPop) (rh : RiemannHypothesis) :
    ∃ d > 0, ∀ᶠ x : ℝ in atTop,
      (t5+d)*sqrt x ≤ (halfOpenCount 5 x : ℝ) ∧
      (t5+d)*sqrt x ≤ ((openSet 5 x).card : ℝ) :=
  both_counts_of_good (width5_actual hn hu rh)

def oldCount (c : ℝ) : ℝ := (8/9)*c-18203/20000
def oldWidth (a : ℝ) : ℝ := (9/8)*(a+18203/20000)

theorem old_domain (a : ℝ) :
    (103/100 ≤ oldWidth a ∧ oldWidth a ≤ 16) ↔
    (973/180000 ≤ a ∧ a ≤ 2396173/180000) := by
  unfold oldWidth
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem exact_gains : t3-oldCount 3 = 61212941/5816940000 ∧
    t5-oldCount 5 = 70933/720000 := by norm_num [t3,t5,oldCount]

theorem inverses_at_widths :
    G (53460284189/41165122592) = 3 ∧
    S t3 = 3 ∧ F (225/128) = 3 ∧
    G (102822181179/41165122592) = 5 ∧
    S (4055753/1163388) = 5 ∧ F t5 = 5 ∧
    (53460284189/41165122592 : ℝ) < 225/128 ∧ (225/128 : ℝ) < t3 ∧
    (102822181179/41165122592 : ℝ) < 4055753/1163388 ∧
    (4055753/1163388 : ℝ) < t5 := by
  norm_num [G,q,t3,t5,RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine]

theorem old_gap {a : ℝ} (_ : 103/100 ≤ oldWidth a) (_ : oldWidth a ≤ 16) :
    0 < oldWidth a-E a := by
  have h := RH080Next.Primal.new_frontier_lt_octic a
  change min (S a) (F a) < oldWidth a at h
  exact sub_pos.mpr ((min_le_right (G a) _).trans_lt h)

#print axioms line_certificate_exact
#print axioms envelope_left
#print axioms envelope_middle
#print axioms envelope_right
#print axioms good_at_envelope
#print axioms good_above_envelope
#print axioms good_below_gaussian_target
#print axioms mem_openSet
#print axioms width3_kernel
#print axioms width5_kernel
#print axioms width3_counts
#print axioms width5_counts
#print axioms exact_gains
#print axioms old_gap
end Transfer
