import BoxIntegratedDefs
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RealDeriv

/-! Actual population identities for integrated Perron transport.
These are unconditional analytic identities, with no RH, explicit-formula,
numerical-program, or prime-table assumption. -/
namespace RHOcticPush.BoxPerron
open Real Set Filter MeasureTheory
open scoped Topology
set_option maxHeartbeats 0

lemma psi_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable Chebyshev.psi volume a b :=
  Chebyshev.psi_mono.intervalIntegrable

lemma psi_right_continuous (x : ℝ) :
    ContinuousWithinAt Chebyshev.psi (Ici x) x := by
  have h := Filter.tendsto_pure.1 (tendsto_floor_right_pure_floor x)
  apply (continuousWithinAt_const :
    ContinuousWithinAt (fun _ : ℝ => Chebyshev.psi x) (Ici x) x).congr_of_eventuallyEq
  · filter_upwards [h] with y hy
    simp only [Chebyshev.psi, ← Int.floor_toNat, hy]
  · rfl

lemma psi1_continuous : Continuous psi1 :=
  intervalIntegral.continuous_primitive psi_intervalIntegrable 1

lemma psi1_right_derivative (x : ℝ) :
    HasDerivWithinAt psi1 (Chebyshev.psi x) (Ioi x) x := by
  have h : HasDerivWithinAt psi1 (Chebyshev.psi x) (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right (psi_intervalIntegrable 1 x)
      Chebyshev.psi_mono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter
      ((psi_right_continuous x).mono Ioi_subset_Ici_self)
  exact h.mono Ioi_subset_Ici_self

/-- The logarithmic change of variable remains valid for the discontinuous
actual Chebyshev function; no continuity of psi is assumed. -/
theorem box_logchange (x s d : ℝ) (hx : 0 < x) (hd : 0 < d) :
    (∫ u in (-1 : ℝ)..1, (1 / 2 : ℝ) *
      Chebyshev.psi (x * Real.exp ((s + u) * d))) =
      (1 / (2 * d)) * ∫ v in x * Real.exp ((s - 1) * d)..
        x * Real.exp ((s + 1) * d), Chebyshev.psi v / v := by
  let f : ℝ → ℝ := fun u => x * Real.exp ((s + u) * d)
  have hfpos (u : ℝ) : 0 < f u := mul_pos hx (Real.exp_pos _)
  have hfderiv (u : ℝ) : HasDerivAt f (d * f u) u := by
    exact ((((hasDerivAt_id u).const_add s).mul_const d).exp.const_mul x).congr_deriv
      (by dsimp [f]; ring)
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := -1) (b := 1)
    (f := f) (f' := fun u => d * f u) (g := fun v => Chebyshev.psi v / v)
    (by dsimp [f]; fun_prop)
    (fun u _ => hfderiv u) (fun u _ => (mul_pos hd (hfpos u)).le)
  have hscale : (∫ u in (-1 : ℝ)..1,
      (Chebyshev.psi (f u) / f u) * (d * f u)) =
      d * ∫ u in (-1 : ℝ)..1, Chebyshev.psi (f u) := by
    calc
      _ = ∫ u in (-1 : ℝ)..1, d * Chebyshev.psi (f u) := by
        apply intervalIntegral.integral_congr
        intro u _
        field_simp [(hfpos u).ne']
      _ = _ := intervalIntegral.integral_const_mul _ _
  rw [intervalIntegral.integral_const_mul]
  change (1 / 2 : ℝ) * (∫ u in (-1 : ℝ)..1, Chebyshev.psi (f u)) = _
  have hends : f (-1) = x * Real.exp ((s - 1) * d) := by
    dsimp [f]
    congr 2
  rw [hends] at hchange
  change (∫ u in (-1 : ℝ)..1,
    (Chebyshev.psi (f u) / f u) * (d * f u)) = _ at hchange
  rw [hscale] at hchange
  rw [← hchange]
  field_simp [hd.ne']

/-- The exact original Box average on its full intended real domain, for every
real shift s (hence in particular both required shifts -1 and +1). -/
theorem actual_box_log_integral {L : ℝ} (hL : 35 ≤ L) (s : ℝ) :
    IEANTN.RHSmoothing.average IEANTN.RHSmoothing.box s L =
      (1 / (2 * IEANTN.RHSmoothing.delta L)) *
        ∫ v in Real.exp L * Real.exp ((s - 1) * IEANTN.RHSmoothing.delta L)..
          Real.exp L * Real.exp ((s + 1) * IEANTN.RHSmoothing.delta L),
          Chebyshev.psi v / v := by
  have hp : 0 < L := by linarith
  have hd : 0 < IEANTN.RHSmoothing.delta L := by
    unfold IEANTN.RHSmoothing.delta
    positivity
  exact box_logchange (Real.exp L) s (IEANTN.RHSmoothing.delta L) (Real.exp_pos L) hd

lemma positive_on_interval {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : x ∈ uIcc a b) : 0 < x := by
  rw [uIcc_of_le hab] at hx
  exact ha.trans_le hx.1

/-- Integration by parts uses the actual primitive's right derivative, so the
jumps of psi require no exceptional-set or continuity assumption. -/
theorem psi1_real_transport {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    realTransport a b psi1 = ∫ t in a..b, Chebyshev.psi t / t := by
  have hv : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc a b) :=
    continuousOn_id.inv₀ (fun x hx => (positive_on_interval ha hab hx).ne')
  have hvd : ContinuousOn (fun x : ℝ => -(x ^ 2)⁻¹) (uIcc a b) :=
    ((continuousOn_id.pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (positive_on_interval ha hab hx).ne')).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := psi1) (u' := Chebyshev.psi) (v := fun x : ℝ => x⁻¹)
    (v' := fun x : ℝ => -(x ^ 2)⁻¹)
    psi1_continuous.continuousOn hv
    (fun x _ => psi1_right_derivative x)
    (fun x hx => (hasDerivAt_inv (positive_on_interval ha hab
      (by rw [uIcc_of_le hab]; simpa [min_eq_left hab, max_eq_right hab] using
        (show x ∈ Icc (min a b) (max a b) from ⟨hx.1.le, hx.2.le⟩))).ne').hasDerivWithinAt)
    (psi_intervalIntegrable a b) hvd.intervalIntegrable
  have he : (∫ t in a..b, psi1 t * -(t ^ 2)⁻¹) =
      -(∫ t in a..b, psi1 t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [div_eq_mul_inv]
    ring
  rw [he] at h
  unfold realTransport
  simp only [div_eq_mul_inv] at h ⊢
  linarith

lemma transport_ofReal (a b : ℝ) (f : ℝ → ℝ) :
    transport a b (fun x => (f x : ℂ)) = (realTransport a b f : ℂ) := by
  unfold transport realTransport
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_div]
  congr 1
  have h := intervalIntegral.integral_ofReal (f := fun x => f x / x ^ 2)
    (μ := volume) (a := a) (b := b)
  simp only [Complex.ofReal_div, Complex.ofReal_pow] at h
  exact h

/-- Exact requested complex transport of the original integrated population. -/
theorem psi1_transport {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    transport a b (fun x => (psi1 x : ℂ)) =
      ∫ t in a..b, (Chebyshev.psi t : ℂ) / (t : ℂ) := by
  rw [transport_ofReal, psi1_real_transport (by linarith : 0 < a) hab]
  have h := intervalIntegral.integral_ofReal (f := fun x => Chebyshev.psi x / x)
    (μ := volume) (a := a) (b := b)
  simp only [Complex.ofReal_div] at h
  exact h.symm

/-- Generic complex substitution for the exact same exponential window.
Monotone change of variables allows arbitrary F, not merely continuous F. -/
theorem complex_box_logchange (x s d : ℝ) (hx : 0 < x) (hd : 0 < d)
    (F : ℝ → ℂ) :
    (∫ u in (-1 : ℝ)..1,
      F (x * Real.exp ((s + u) * d)) * (d : ℂ) *
        (x * Real.exp ((s + u) * d) : ℝ)) =
      ∫ v in x * Real.exp ((s - 1) * d)..x * Real.exp ((s + 1) * d), F v := by
  let f : ℝ → ℝ := fun u => x * Real.exp ((s + u) * d)
  have hfpos (u : ℝ) : 0 < f u := mul_pos hx (Real.exp_pos _)
  have hfderiv (u : ℝ) : HasDerivAt f (d * f u) u :=
    ((((hasDerivAt_id u).const_add s).mul_const d).exp.const_mul x).congr_deriv
      (by dsimp [f]; ring)
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := -1) (b := 1) (f := f) (f' := fun u => d * f u) (g := F)
    (by dsimp [f]; fun_prop)
    (fun u _ => hfderiv u) (fun u _ => (mul_pos hd (hfpos u)).le)
  have he : f (-1) = x * Real.exp ((s - 1) * d) := by dsimp [f]; congr 2
  rw [he] at h
  calc
    _ = ∫ u in (-1 : ℝ)..1, (d * f u) • F (f u) := by
      apply intervalIntegral.integral_congr
      intro u _
      simp only [Complex.real_smul, Complex.ofReal_mul]
      dsimp [f]
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := h

/-- C1 complex transport, suitable for each zero or trivial-zero primitive.
The only analytic input is the stated derivative and its interval integrability. -/
theorem transport_of_hasDerivAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {F F' : ℝ → ℂ} (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' x) x)
    (hF' : IntervalIntegrable F' volume a b) :
    transport a b F = ∫ t in a..b, F' t / (t : ℂ) := by
  have hinv (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => (t : ℂ)⁻¹) (-((x : ℂ) ^ 2)⁻¹) x := by
    have h := (hasDerivAt_inv (positive_on_interval ha hab hx).ne').ofReal_comp
    simp only [Complex.ofReal_inv, Complex.ofReal_neg, Complex.ofReal_pow] at h
    exact h
  have hv : ContinuousOn (fun x : ℝ => (x : ℂ)⁻¹) (uIcc a b) :=
    fun x hx => (hinv x hx).continuousAt.continuousWithinAt
  have hvd : ContinuousOn (fun x : ℝ => -((x : ℂ) ^ 2)⁻¹) (uIcc a b) :=
    ((Complex.continuous_ofReal.continuousOn.pow 2).inv₀
      (fun x hx => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr
        (positive_on_interval ha hab hx).ne'))).neg
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := F) (u' := F') (v := fun x : ℝ => (x : ℂ)⁻¹)
    (v' := fun x : ℝ => -((x : ℂ) ^ 2)⁻¹)
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt) hv
    (fun x hx => (hF x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    (fun x hx => (hinv x ⟨hx.1.le, hx.2.le⟩).hasDerivWithinAt)
    hF' hvd.intervalIntegrable
  have he : (∫ t in a..b, F t * -((t : ℂ) ^ 2)⁻¹) =
      -(∫ t in a..b, F t / (t : ℂ) ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [div_eq_mul_inv]
    ring
  rw [he] at h
  unfold transport
  simp only [div_eq_mul_inv] at h ⊢
  linear_combination -h

#print axioms psi_right_continuous
#print axioms psi1_right_derivative
#print axioms box_logchange
#print axioms actual_box_log_integral
#print axioms psi1_real_transport
#print axioms psi1_transport
#print axioms complex_box_logchange
#print axioms transport_of_hasDerivAt
end RHOcticPush.BoxPerron
