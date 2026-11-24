import OcticDerivativeBounds
import AbsoluteStieltjes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Genuine infinite BPT transport on the actual zeta-zero subtype.
The integrability and vanishing-boundary conditions are explicit analytic conditions,
not a renamed zero-estimate target or a finite-height replacement. -/
namespace RHOcticPush.BPTInfinite
open Real Set MeasureTheory Filter
open RHLimit.BPTZeroCount
set_option maxHeartbeats 0

def PositiveZero (a : ℝ) := IEANTN.zetaZeroesIn univ (Ioi a)

lemma order_nonneg {a : ℝ} (ha : 0 ≤ a) (z : PositiveZero a) :
    (0 : ℝ) ≤ IEANTN.zetaOrder z.val :=
  CH2Section7Z.zetaOrder_nonneg_of_mem (fun t ht => ha.trans_lt ht) z.property

lemma finite_subsum_le {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ)
    (s : Finset (PositiveZero a)) (hs : ∀ z ∈ s, z.val.im ≤ b) :
    (∑ z ∈ s, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      IEANTN.zetaZeroesSum univ (Ioc a b) (fun z => |f z.im|) := by
  classical
  let T := (CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha).toFinset
  have hsub : s.image Subtype.val ⊆ T := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    exact (Set.Finite.mem_toFinset _).mpr
      ⟨Set.mem_univ _, ⟨v.property.2.1, hs v hv⟩, v.property.2.2⟩
  rw [CH2Section7Z.zetaZeroesSum_eq_sum
    (CH2Section7Z.finite_zeros_Ioc (a := a) (b := b) ha)]
  calc
    _ = ∑ z ∈ s.image Subtype.val, |f z.im| * (IEANTN.zetaOrder z : ℝ) := by
      rw [Finset.sum_image]
      intro z _ v _ hv
      exact Subtype.ext hv
    _ ≤ ∑ z ∈ T, |f z.im| * (IEANTN.zetaOrder z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hz _
      exact mul_nonneg (abs_nonneg _) (CH2Section7Z.zetaOrder_nonneg_of_mem
        (fun t ht => ha.trans_lt ht.1) ((Set.Finite.mem_toFinset _).mp hz))

/-- General infinite absolute BPT bound, with summability proved rather than assumed. -/
theorem infinite_absolute_bound (h : PublishedBound) {a : ℝ}
    (ha : 2 * Real.pi ≤ a) {f f' : ℝ → ℝ}
    (hd : ∀ t ∈ Ici a, HasDerivAt f (f' t) t)
    (hc : ContinuousOn f' (Ici a))
    (hI : IntegrableOn (fun t => |f t| * density t) (Ioi a))
    (hD : IntegrableOn (fun t => |f' t| * log t) (Ioi a))
    (hb : Tendsto (fun t => |f t| * log t) atTop (nhds 0)) :
    Summable (fun z : PositiveZero a => |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ∧
    (∑' z : PositiveZero a, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤
      (∫ t in Ioi a, |f t| * density t) +
      (7 / 25) * (|f a| * log a + ∫ t in Ioi a, |f' t| * log t) := by
  classical
  let B := (∫ t in Ioi a, |f t| * density t) +
    (7 / 25) * (|f a| * log a + ∫ t in Ioi a, |f' t| * log t)
  have ha0 : 0 ≤ a := by linarith [pi_pos]
  have hnonneg (z : PositiveZero a) :
      0 ≤ |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ) :=
    mul_nonneg (abs_nonneg _) (order_nonneg ha0 z)
  have hsum (s : Finset (PositiveZero a)) :
      (∑ z ∈ s, |f z.val.im| * (IEANTN.zetaOrder z.val : ℝ)) ≤ B := by
    let M := ∑ z ∈ s, max z.val.im 0
    have hM (z : PositiveZero a) (hz : z ∈ s) : z.val.im ≤ M := by
      exact (le_max_left _ _).trans (Finset.single_le_sum
        (fun v _ => le_max_right v.val.im 0) hz)
    have hmain := intervalIntegral_tendsto_integral_Ioi a hI tendsto_id
    have hder := intervalIntegral_tendsto_integral_Ioi a hD tendsto_id
    have hrest := ((hb.add_const (|f a| * log a)).add hder).const_mul (7 / 25 : ℝ)
    have hlim := hmain.add hrest
    have hlim' : Tendsto
        (fun b : ℝ => (∫ t in a..b, |f t| * density t) +
          (7 / 25) * (|f b| * log b + |f a| * log a +
            ∫ t in a..b, |f' t| * log t)) atTop (nhds B) := by
      simpa [B] using hlim
    apply ge_of_tendsto hlim'
    filter_upwards [eventually_ge_atTop (max a M)] with b hlarge
    have hab : a ≤ b := (le_max_left _ _).trans hlarge
    have hs : ∀ z ∈ s, z.val.im ≤ b := fun z hz =>
      (hM z hz).trans ((le_max_right _ _).trans hlarge)
    apply (finite_subsum_le ha0 f s hs).trans
    apply RHLimit.AbsoluteStieltjes.finite_absolute_bound h ha hab
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact hd t ht.1
    · exact hc.mono (by intro t ht; rw [uIcc_of_le hab] at ht; exact ht.1)
  exact ⟨summable_of_sum_le hnonneg hsum, Real.tsum_le_of_sum_le hnonneg hsum⟩

#print axioms finite_subsum_le
#print axioms infinite_absolute_bound
end RHOcticPush.BPTInfinite
