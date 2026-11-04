/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalculusAssembly
import Numerics
import ForwardRamanujan.Math

/-!
# Generic calibration adapter: theta input + one number Δ ⟹ two-sided π expansion

`Solutions/DudekPlattNumerics.v4` (Comparator-accepted, unchanged here) proves the π expansion
at `x > exp 9400` with its four scalar constants written into the statement
(`3110`, `1/2`, `1/10`, `1/1000`). This file restates its coefficient step with those constants
as parameters, and adds the monotonicity argument that lets one evaluation at the left
endpoint `L₀` cover every `x > exp L₀`. Every analytic lemma used (`primeCounting_expansion`,
`errorIntegral_split_bound`, `I7_bound`, `normalize_error_majorant`, `normalize_I7_majorant`,
`poly_exp_decreasing`) is v4's own, imported, not copied.

The deviation `Δ` is the single number program A computes:
`P + dPiece K L₀ + iPiece L₀ + aPiece L₀ < Δ` gives the coefficients `120 ∓ Δ`.
-/

namespace CalibrationPilot
open Real DudekPlattNumerics.Calculus

/-- Error-integral piece of the normalized deviation, with tail constant `K`. -/
noncomputable def dPiece (K L : ℝ) : ℝ := 4 * L ^ 6 * exp (-L / 100) + K / ((99 / 100 : ℝ) ^ 7 * L)
/-- `720·I₇` piece. -/
noncomputable def iPiece (L : ℝ) : ℝ :=
  720 * (1 / L + 7 * (L ^ 6 * exp (-L / 2) / log 2 ^ 8 + 256 / L ^ 2))
/-- Lower-endpoint constant piece `2A`. -/
noncomputable def aPiece (L : ℝ) : ℝ := 2 * A * L ^ 6 * exp (-L)

theorem S5_eq_mainTerm (x : ℝ) : S5 x = DudekPlatt.v3.mainTerm x := rfl

/-- v4's `coefficients_from_logarithmic_certificates`, with the constants as parameters. -/
theorem normalized_bounds (hlog2 : (2 / 3 : ℝ) < log 2) {L K P : ℝ} (hL : 9400 ≤ L)
    (hK : 0 ≤ K)
    (hpoint : |thetaError (exp L)| ≤ P * exp L / L ^ 5)
    (htail : ∀ t : ℝ, exp ((99 / 100 : ℝ) * L) ≤ t → |thetaError t| ≤ K * t / log t ^ 5) :
    120 - P - dPiece K L - aPiece L ≤
        L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) ∧
      L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) ≤
        120 + iPiece L + P + dPiece K L := by
  have hLpos : 0 < L := by linarith
  have hx : 2 ≤ exp L := by linarith [add_one_le_exp L]
  have hq : 0 < L ^ 6 / exp L := by positivity
  have hp : |L ^ 6 / exp L * (thetaError (exp L) / L)| ≤ P := by
    rw [abs_mul, abs_of_pos hq, abs_div, abs_of_pos hLpos]
    calc
      _ ≤ L ^ 6 / exp L * ((P * exp L / L ^ 5) / L) := by gcongr
      _ = _ := by field_simp
  have hs : 2 ≤ exp ((99 / 100 : ℝ) * L) := by
    linarith [add_one_le_exp ((99 / 100 : ℝ) * L)]
  have hsx : exp ((99 / 100 : ℝ) * L) ≤ exp L := by
    apply exp_le_exp.mpr
    linarith
  have hb := errorIntegral_split_bound hlog2 hs hsx hK (fun t ht ↦ htail t ht.1)
  have he : |L ^ 6 / exp L * errorIntegral (exp L)| ≤ dPiece K L := by
    rw [abs_mul, abs_of_pos hq]
    calc
      _ ≤ L ^ 6 / exp L * (4 * exp ((99 / 100 : ℝ) * L) +
          K * exp L / log (exp ((99 / 100 : ℝ) * L)) ^ 7) :=
        mul_le_mul_of_nonneg_left hb hq.le
      _ = _ := by rw [normalize_error_majorant hLpos, dPiece]
  have hx4 : 4 ≤ exp L := by linarith [add_one_le_exp L]
  have hi : L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) ≤ iPiece L := by
    calc
      _ ≤ L ^ 6 / exp L * (720 * (exp L / log (exp L) ^ 7 +
          7 * (sqrt (exp L) / log 2 ^ 8 + 256 * exp L / log (exp L) ^ 8))) := by
        gcongr
        exact I7_bound hx4
      _ = _ := by rw [normalize_I7_majorant hLpos, iPiece]
  have hi0 : 0 ≤ L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) (logIntegral_nonneg 7 hx))
  have ha : L ^ 6 / exp L * (2 * A) = aPiece L := by
    rw [aPiece, exp_neg]
    ring
  have ha0 : 0 ≤ L ^ 6 / exp L * (2 * A) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) A_nonneg)
  have hn : L ^ 6 / exp L * (IEANTN.primeCounting (exp L) - S5 (exp L)) =
      120 + L ^ 6 / exp L * (720 * logIntegral 7 (exp L)) -
        L ^ 6 / exp L * (2 * A) + L ^ 6 / exp L * (thetaError (exp L) / L) +
        L ^ 6 / exp L * errorIntegral (exp L) := by
    rw [primeCounting_expansion hx, log_exp]
    field_simp
    ring
  rw [hn]
  rcases abs_le.mp hp with ⟨hp1, hp2⟩
  rcases abs_le.mp he with ⟨he1, he2⟩
  constructor <;> linarith

theorem dPiece_antitone {K L₀ L : ℝ} (hK : 0 ≤ K) (hL₀ : 9400 ≤ L₀) (hL : L₀ ≤ L) :
    dPiece K L ≤ dPiece K L₀ := by
  have h0 : 0 < L₀ := by linarith
  have h1 := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 6 (c := 1 / 100) h0
    (by rw [div_le_div_iff₀ h0 (by norm_num)]; push_cast; linarith) hL
  have h2 : K / ((99 / 100 : ℝ) ^ 7 * L) ≤ K / ((99 / 100 : ℝ) ^ 7 * L₀) := by
    apply div_le_div_of_nonneg_left hK (by positivity)
    exact mul_le_mul_of_nonneg_left hL (by norm_num)
  have e1 : exp (-L / 100) = exp (-(1 / 100) * L) := by ring_nf
  have e2 : exp (-L₀ / 100) = exp (-(1 / 100) * L₀) := by ring_nf
  unfold dPiece
  rw [e1, e2]
  nlinarith

theorem iPiece_antitone {L₀ L : ℝ} (hL₀ : 9400 ≤ L₀) (hL : L₀ ≤ L) :
    iPiece L ≤ iPiece L₀ := by
  have h0 : 0 < L₀ := by linarith
  have hLp : 0 < L := by linarith
  have h1 := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 6 (c := 1 / 2) h0
    (by rw [div_le_div_iff₀ h0 (by norm_num)]; push_cast; linarith) hL
  have e1 : exp (-L / 2) = exp (-(1 / 2) * L) := by ring_nf
  have e2 : exp (-L₀ / 2) = exp (-(1 / 2) * L₀) := by ring_nf
  have hl2 : 0 < log (2 : ℝ) ^ 8 := by positivity
  have h3 : 1 / L ≤ 1 / L₀ := one_div_le_one_div_of_le h0 hL
  have h4 : 256 / L ^ 2 ≤ 256 / L₀ ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    nlinarith
  have h5 : L ^ 6 * exp (-L / 2) / log 2 ^ 8 ≤ L₀ ^ 6 * exp (-L₀ / 2) / log 2 ^ 8 := by
    rw [e1, e2]
    exact div_le_div_of_nonneg_right h1 hl2.le
  unfold iPiece
  nlinarith

theorem aPiece_antitone {L₀ L : ℝ} (hL₀ : 9400 ≤ L₀) (hL : L₀ ≤ L) :
    aPiece L ≤ aPiece L₀ := by
  have h0 : 0 < L₀ := by linarith
  have h1 := DudekPlattNumerics.v4.Numerics.poly_exp_decreasing 6 (c := 1) h0
    (by rw [div_le_iff₀ h0]; push_cast; linarith) hL
  have hA : 0 ≤ 2 * A := mul_nonneg (by norm_num) A_nonneg
  have e1 : exp (-L) = exp (-1 * L) := by ring_nf
  have e2 : exp (-L₀) = exp (-1 * L₀) := by ring_nf
  unfold aPiece
  rw [e1, e2]
  nlinarith

theorem pieces_nonneg {K L : ℝ} (hK : 0 ≤ K) (hL : 9400 ≤ L) :
    0 ≤ dPiece K L ∧ 0 ≤ iPiece L ∧ 0 ≤ aPiece L := by
  have hLp : 0 < L := by linarith
  refine ⟨by unfold dPiece; positivity, by unfold iPiece; positivity, ?_⟩
  have := A_nonneg
  unfold aPiece
  positivity

/-- **Whole-ray calibration.** A pointwise theta bound with constant `P` on the whole ray, a tail
bound with constant `K` from `exp (0.99 L₀)`, and one number `Δ` exceeding the deviation at the
left endpoint give the two-sided π expansion with coefficients `120 ∓ Δ` for every `x > exp L₀`.
Monotonicity in `L = log x`, not sampling, carries the endpoint value to the whole ray. -/
theorem calibrated_pi (hlog2 : (2 / 3 : ℝ) < log 2) {L₀ P K Δ : ℝ} (hL₀ : 9400 ≤ L₀)
    (hK : 0 ≤ K)
    (hpoint : ∀ L ≥ L₀, |thetaError (exp L)| ≤ P * exp L / L ^ 5)
    (htail : ∀ t : ℝ, exp ((99 / 100 : ℝ) * L₀) ≤ t → |thetaError t| ≤ K * t / log t ^ 5)
    (hΔ : P + dPiece K L₀ + iPiece L₀ + aPiece L₀ < Δ) :
    ∀ x > exp L₀,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6 := by
  intro x hx
  have hx0 : 0 < x := (exp_pos _).trans hx
  have hlx : L₀ < log x := by
    have := log_lt_log (exp_pos _) hx
    rwa [log_exp] at this
  set L := log x with hLdef
  have hL : 9400 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hxe : exp L = x := exp_log hx0
  have hpt := hpoint L hlx.le
  have htl : ∀ t : ℝ, exp ((99 / 100 : ℝ) * L) ≤ t → |thetaError t| ≤ K * t / log t ^ 5 := by
    intro t ht
    apply htail t
    exact (exp_le_exp.mpr (by nlinarith)).trans ht
  have hP : 0 ≤ P := by
    have h1 : 0 ≤ P * exp L / L ^ 5 := (abs_nonneg _).trans hpt
    have h2 : 0 < exp L / L ^ 5 := by positivity
    have h3 : P * exp L / L ^ 5 = P * (exp L / L ^ 5) := by ring
    rw [h3] at h1
    exact nonneg_of_mul_nonneg_left h1 h2
  obtain ⟨hlo, hhi⟩ := normalized_bounds hlog2 hL hK hpt htl
  have hd := dPiece_antitone hK hL₀ hlx.le
  have hi := iPiece_antitone hL₀ hlx.le
  have ha := aPiece_antitone hL₀ hlx.le
  obtain ⟨hd0, hi0, ha0⟩ := pieces_nonneg hK hL
  obtain ⟨hd0', hi0', ha0'⟩ := pieces_nonneg hK hL₀
  rw [hxe] at hlo hhi
  have hw : 0 < x / L ^ 6 := by positivity
  have hnorm : L ^ 6 / x * (IEANTN.primeCounting x - S5 x) * (x / L ^ 6) =
      IEANTN.primeCounting x - S5 x := by field_simp
  have lo : (120 - Δ) * (x / L ^ 6) < IEANTN.primeCounting x - S5 x := by
    rw [← hnorm]
    apply mul_lt_mul_of_pos_right _ hw
    linarith
  have hi' : IEANTN.primeCounting x - S5 x < (120 + Δ) * (x / L ^ 6) := by
    rw [← hnorm]
    apply mul_lt_mul_of_pos_right _ hw
    linarith
  rw [← S5_eq_mainTerm]
  constructor
  · have : (120 - Δ) * x / L ^ 6 = (120 - Δ) * (x / L ^ 6) := by ring
    linarith
  · have : (120 + Δ) * x / L ^ 6 = (120 + Δ) * (x / L ^ 6) := by ring
    linarith

/-- The calibrated expansion in program B's input shape (`ForwardRamanujan.PiInput`): the lower
half is needed from `exp A`, the upper half only from `exp (A+1)`. -/
theorem piInput_of_calibrated {L₀ Δ : ℝ}
    (h : ∀ x > exp L₀,
      DudekPlatt.v3.mainTerm x + (120 - Δ) * x / log x ^ 6 < IEANTN.primeCounting x ∧
        IEANTN.primeCounting x < DudekPlatt.v3.mainTerm x + (120 + Δ) * x / log x ^ 6) :
    ForwardRamanujan.PiInput (120 - Δ) (120 + Δ) L₀ := by
  constructor
  · intro x hx
    exact (h x hx).1
  · intro x hx
    exact (h x ((exp_lt_exp.mpr (by linarith)).trans hx)).2

/-- For `m ≥ 0` the repaired lower term is the `m = 0` term plus `m` (the `εPos` branch), so a
budget certified for `(0, M)` gives one for `(m, M)` after subtracting `m` in exact arithmetic.
Used when the frozen program shape needs a positive output. -/
theorem epsilon_shift_nonneg {m M xa x C : ℝ} (hm : 0 ≤ m)
    (h : DudekPlatt.v3.εUpper M x - DudekPlatt.v3.εLower 0 xa x ≤ C) :
    DudekPlatt.v3.εUpper M x - DudekPlatt.v3.εLower m xa x ≤ C - m := by
  unfold DudekPlatt.v3.εLower at h ⊢
  simp only [le_refl, ↓reduceIte] at h
  simp only [hm, ↓reduceIte]
  unfold DudekPlatt.v3.εPos at h ⊢
  linarith

end CalibrationPilot
