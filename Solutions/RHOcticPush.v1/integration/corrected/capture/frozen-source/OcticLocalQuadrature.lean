import OcticQuadrature
import OcticSecondDecay
namespace RHOcticPush.Moments
open Real Set MeasureTheory
set_option maxHeartbeats 0
lemma abs_chord_on {f : ℝ → ℝ} {M a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    (hp : ConvexOn ℝ (Icc a b) (fun x => f x + M / 2 * x ^ 2))
    (hm : ConvexOn ℝ (Icc a b) (fun x => -f x + M / 2 * x ^ 2)) :
    |f t| ≤ (b - t) / (b - a) * |f a| + (t - a) / (b - a) * |f b| +
      M / 2 * (t - a) * (b - t) := by
  let α := (b - t) / (b - a)
  let β := (t - a) / (b - a)
  have h0 : 0 < b - a := sub_pos.mpr hab
  have ha : 0 ≤ α := div_nonneg (sub_nonneg.mpr ht.2) h0.le
  have hb : 0 ≤ β := div_nonneg (sub_nonneg.mpr ht.1) h0.le
  have hs : α + β = 1 := by dsimp [α, β]; field_simp; ring
  have hx : α * a + β * b = t := by dsimp [α, β]; field_simp; ring
  have hq : M / 2 * (α * a ^ 2 + β * b ^ 2 - t ^ 2) =
      M / 2 * (t - a) * (b - t) := by
    dsimp [α, β]
    field_simp
    ring
  have hplus := hp.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ ha hb hs
  have hminus := hm.2 ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ ha hb hs
  simp only [smul_eq_mul] at hplus hminus
  rw [hx] at hplus hminus
  have hpa := mul_le_mul_of_nonneg_left (le_abs_self (f a)) ha
  have hpb := mul_le_mul_of_nonneg_left (le_abs_self (f b)) hb
  have hma := mul_le_mul_of_nonneg_left (neg_le_abs (f a)) ha
  have hmb := mul_le_mul_of_nonneg_left (neg_le_abs (f b)) hb
  apply abs_le.mpr
  constructor <;> change _ ≤ _
  · nlinarith
  · nlinarith

theorem abs_trapezoid_on {f : ℝ → ℝ} {M a b : ℝ} (hab : a < b) (hc : Continuous f)
    (hp : ConvexOn ℝ (Icc a b) (fun x => f x + M / 2 * x ^ 2))
    (hm : ConvexOn ℝ (Icc a b) (fun x => -f x + M / 2 * x ^ 2)) :
    (∫ t in a..b, |f t|) ≤
      (b - a) / 2 * (|f a| + |f b|) + M * (b - a) ^ 3 / 12 := by
  have hmajor : Continuous (chordMajorant f M a b) := by
    unfold chordMajorant
    fun_prop
  calc
    _ ≤ ∫ t in a..b, chordMajorant f M a b t :=
      intervalIntegral.integral_mono_on hab.le (hc.abs.intervalIntegrable a b)
        (hmajor.intervalIntegrable a b) (fun t ht => abs_chord_on hab ht hp hm)
    _ = _ := chord_integral f hab

lemma quadratic_convex_on {f f' f'' : ℝ → ℝ} {M a b : ℝ}
    (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : ∀ x, HasDerivAt f' (f'' x) x)
    (hM : ∀ x ∈ Icc a b, -M ≤ f'' x) :
    ConvexOn ℝ (Icc a b) (fun x => f x + M / 2 * x ^ 2) := by
  have hq1 (x : ℝ) : HasDerivAt (fun x => f x + M / 2 * x ^ 2)
      (f' x + M * x) x := by
    apply ((h1 x).add ((hasDerivAt_id x).pow 2 |>.const_mul (M / 2))).congr_deriv
    dsimp
    ring
  have hq2 (x : ℝ) : HasDerivAt (fun x => f' x + M * x) (f'' x + M) x := by
    apply ((h2 x).add ((hasDerivAt_id x).const_mul M)).congr_deriv
    ring
  exact convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc a b)
    (fun x _ => (hq1 x).continuousAt.continuousWithinAt)
    (fun x _ => (hq1 x).hasDerivWithinAt)
    (fun x _ => (hq2 x).hasDerivWithinAt)
    (fun x hx => by linarith [hM x (interior_subset hx)])


theorem octic_abs_trapezoid_decay {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ y in a..b, |EvenKernel.transform 4 y|) ≤
      (b-a)/2*(|EvenKernel.transform 4 a|+|EvenKernel.transform 4 b|)+
      (40/a^2)*(b-a)^3/12 := by
  have hbound (x : ℝ) (hx : x ∈ Icc a b) : |DerivativeBounds.second x| ≤ 40/a^2 := by
    have hax : a^2 ≤ x^2 := by nlinarith [hx.1]
    have ha2 : 0 < a^2 := sq_pos_of_pos ha
    have hp := SecondDecay.second_quadratic_decay x
    apply (le_div_iff₀ ha2).mpr
    nlinarith [abs_nonneg (DerivativeBounds.second x)]
  have hp := quadratic_convex_on (a := a) (b := b)
    DerivativeBounds.transform_hasDerivAt DerivativeBounds.first_hasDerivAt
    (fun x hx => (abs_le.mp (hbound x hx)).1)
  have hm := quadratic_convex_on (M := 40/a^2) (a := a) (b := b)
    (fun x => (DerivativeBounds.transform_hasDerivAt x).neg)
    (fun x => (DerivativeBounds.first_hasDerivAt x).neg)
    (fun x hx => by linarith [(abs_le.mp (hbound x hx)).2])
  exact abs_trapezoid_on hab
    (continuous_iff_continuousAt.mpr fun x =>
      (DerivativeBounds.transform_hasDerivAt x).continuousAt) hp hm
#print axioms octic_abs_trapezoid_decay
end RHOcticPush.Moments
