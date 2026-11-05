/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Table4Evolution.Instance

/-!
# The θ → π transport for a power profile, in closed form

For `Eθ ≤ K·t^{-1/8}` on `t ≥ e^300` the cell sum of `whole_ray` is not needed: the kernel
`t^{-1/8}/log² t` has the explicit majorant antiderivative `κ·t^{7/8}/log² t`, `κ = 600/521`, on
`t ≥ e^300` (its derivative is `κ·t^{-1/8}·(7/8·log t − 2)/log³ t`, and `κ·(7/8 − 2/300) = 1`).
With the anchor `Eπ(e^300) ≤ 1.6997·10⁻¹²` this gives, for every `x ≥ e^330` (`power_ray`),

  `Eπ(x) ≤ (K·(1 + κ/330) + (330/300)·e^{45/4}·(1.6997·10⁻¹² + u₀))·x^{-1/8}`,  `u₀ ≥ Eθ(e^300)`,

a **decaying** bound, where `whole_ray` gave a constant on the ray. The output of the program is now
the coefficient of `x^{-1/8}`; the program has two inputs and one constant instead of a partition
(`power_pi_bound`, with `powerOK` checking the literals). A decaying output can feed the Ramanujan
budget, which a constant on an infinite ray cannot.
-/

namespace Table4Evolution

open Real IEANTN MeasureTheory Set intervalIntegral FKS2Table4 FKS2Scalar PVCore

/-- The power kernel `t^{-1/8}/log² t` integrates below `κ·x^{7/8}/log² x` from `e^300`. -/
theorem power_kernel_integral {x : ℝ} (hx : exp 300 ≤ x) :
    (∫ t in exp 300..x, t ^ ((7 : ℝ) / 8 - 1) * kernel t) ≤
      600 / 521 * x ^ ((7 : ℝ) / 8) / (log x) ^ 2 := by
  have h300 : ∀ t ∈ uIcc (exp 300) x, 0 < t ∧ 300 ≤ log t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    exact ⟨(exp_pos _).trans_le ht.1, by simpa using log_le_log (exp_pos (300 : ℝ)) ht.1⟩
  let G : ℝ → ℝ := fun t => 600 / 521 * t ^ ((7 : ℝ) / 8) / (log t) ^ 2
  let D : ℝ → ℝ := fun t => 600 / 521 * t ^ ((7 : ℝ) / 8 - 1) * (7 / 8 * log t - 2) / (log t) ^ 3
  have hD : ∀ t ∈ uIcc (exp 300) x, HasDerivAt G (D t) t := by
    intro t ht
    obtain ⟨ht0, hl⟩ := h300 t ht
    have hl0 : 0 < log t := by linarith
    have hr := Real.hasDerivAt_rpow_const (p := (7 : ℝ) / 8) (Or.inl ht0.ne')
    have hh := ((hasDerivAt_const t (600 / 521 : ℝ)).mul hr).div
      ((hasDerivAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl0.ne')
    apply hh.congr_deriv
    have hsplit : t ^ ((7 : ℝ) / 8) = t ^ ((7 : ℝ) / 8 - 1) * t := by
      rw [rpow_sub_one ht0.ne']; field_simp
    dsimp [D]
    rw [hsplit]
    field_simp
    ring
  have hcont : ContinuousOn D (uIcc (exp 300) x) := by
    intro t ht
    obtain ⟨ht0, hl⟩ := h300 t ht
    have hl0 : 0 < log t := by linarith
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div _ ((continuousAt_log ht0.ne').pow 3) (pow_ne_zero 3 hl0.ne')
    exact (continuousAt_const.mul (continuousAt_id.rpow_const (Or.inl ht0.ne'))).mul
      (continuousAt_const.mul (continuousAt_log ht0.ne') |>.sub continuousAt_const)
  have hiD := hcont.intervalIntegrable (μ := volume)
  have hif : IntervalIntegrable (fun t => t ^ ((7 : ℝ) / 8 - 1) * kernel t) volume (exp 300) x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨ht0, hl⟩ := h300 t ht
    have hl0 : 0 < log t := by linarith
    apply ContinuousAt.continuousWithinAt
    unfold kernel
    exact (continuousAt_id.rpow_const (Or.inl ht0.ne')).mul
      (continuousAt_const.div ((continuousAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl0.ne'))
  have hcomp : (∫ t in exp 300..x, t ^ ((7 : ℝ) / 8 - 1) * kernel t) ≤ G x - G (exp 300) := by
    rw [← integral_eq_sub_of_hasDerivAt hD hiD]
    apply integral_mono_on hx hif hiD
    intro t ht
    have ht' : t ∈ uIcc (exp 300) x := by rw [uIcc_of_le hx]; exact ht
    obtain ⟨ht0, hl⟩ := h300 t ht'
    have hl0 : 0 < log t := by linarith
    have hp : 0 < t ^ ((7 : ℝ) / 8 - 1) := rpow_pos_of_pos ht0 _
    unfold kernel
    dsimp [D]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hk : log t ^ 2 ≤ 600 / 521 * (7 / 8 * log t - 2) * log t := by
      nlinarith [mul_nonneg hl0.le (sub_nonneg.mpr hl)]
    have hm := mul_le_mul_of_nonneg_left hk (le_of_lt (mul_pos hp hl0))
    nlinarith [hm]
  have hG : 0 ≤ G (exp 300) := by dsimp [G]; positivity
  dsimp [G] at hcomp
  linarith

/-- `|∫ err| ≤ K·∫ t^{-1/8}/log² t` under the power profile. -/
theorem power_integral_error {K x : ℝ} (hx : exp 300 ≤ x)
    (hθ : ∀ t ≥ exp 300, Eθ t ≤ K * t ^ ((7 : ℝ) / 8 - 1)) :
    |∫ t in exp 300..x, err t| ≤ K * ∫ t in exp 300..x, t ^ ((7 : ℝ) / 8 - 1) * kernel t := by
  have h2 : (2 : ℝ) ≤ exp 300 := by linarith [add_one_le_exp (300 : ℝ)]
  have hi : IntervalIntegrable err volume (exp 300) x := FKS2Sol.intervalIntegrable_sub_div
    (by linarith) hx
  have hif : IntervalIntegrable (fun t => t ^ ((7 : ℝ) / 8 - 1) * kernel t) volume (exp 300) x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < log t := log_pos (by linarith [ht.1])
    apply ContinuousAt.continuousWithinAt
    unfold kernel
    exact (continuousAt_id.rpow_const (Or.inl ht0.ne')).mul
      (continuousAt_const.div ((continuousAt_log ht0.ne').pow 2) (pow_ne_zero 2 hl0.ne'))
  calc |∫ t in exp 300..x, err t| ≤ ∫ t in exp 300..x, |err t| := abs_integral_le_integral_abs hx
    _ ≤ ∫ t in exp 300..x, K * (t ^ ((7 : ℝ) / 8 - 1) * kernel t) := by
      apply integral_mono_on hx hi.abs (hif.const_mul K)
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hl : 0 < log t := log_pos (by linarith [ht.1])
      have he : |err t| = Eθ t * kernel t := by
        unfold err Eθ kernel
        rw [abs_div, abs_of_pos (by positivity : 0 < t * (log t) ^ 2)]
        ring
      rw [he, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hθ t ht.1) (by unfold kernel; positivity)
    _ = _ := integral_const_mul _ _

/-- `log x / x ≤ 330·e^{-7·330/8}·x^{-1/8}` for `x ≥ e^330`: `L·e^{-7L/8}` decreases. -/
theorem logx_div_le {x : ℝ} (hx : exp 330 ≤ x) :
    log x / x ≤ 330 * exp (-(7 / 8 * 330)) * x ^ ((7 : ℝ) / 8 - 1) := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 330 ≤ log x := by simpa using log_le_log (exp_pos (330 : ℝ)) hx
  set L := log x with hLd
  have hxL : x = exp L := (exp_log hx0).symm
  have hpow : x ^ ((7 : ℝ) / 8 - 1) = exp (-(L / 8)) := by
    rw [rpow_def_of_pos hx0, ← hLd]; ring_nf
  rw [hpow, hxL]
  -- L·e^{-L} ≤ 330·e^{-7·330/8}·e^{-L/8}  ⟺  L/330 ≤ e^{7(L-330)/8}
  have hkey : L / 330 ≤ exp (7 / 8 * (L - 330)) := by
    have := add_one_le_exp (7 / 8 * (L - 330))
    have h1 : L / 330 ≤ 7 / 8 * (L - 330) + 1 := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  rw [div_eq_mul_inv, ← exp_neg]
  have hpos : 0 < exp (-(7 / 8 * 330)) * exp (-(L / 8)) := by positivity
  calc L * exp (-L) = 330 * (L / 330) * exp (-L) := by ring
    _ ≤ 330 * exp (7 / 8 * (L - 330)) * exp (-L) := by gcongr
    _ = 330 * exp (-(7 / 8 * 330)) * exp (-(L / 8)) := by
        rw [show (330 : ℝ) * exp (7 / 8 * (L - 330)) * exp (-L) =
          330 * (exp (7 / 8 * (L - 330)) * exp (-L)) by ring, ← exp_add]
        rw [show (330 : ℝ) * exp (-(7 / 8 * 330)) * exp (-(L / 8)) =
          330 * (exp (-(7 / 8 * 330)) * exp (-(L / 8))) by ring, ← exp_add]
        congr 2; ring

/-- **Power-form transport.** -/
theorem power_ray {K u0 : ℝ} (hK : 0 ≤ K)
    (hθ : HasPowerLogBound Eθ K 0 (7 / 8) (exp 300)) (h0 : Eθ (exp 300) ≤ u0)
    (hOld : Eπ (exp 300) ≤ 1.6997e-12) :
    ∀ x ≥ exp 330, Eπ x ≤ (K * (1 + 600 / 521 / 330) +
      330 / 300 * exp (45 / 4) * (1.6997e-12 + u0)) * x ^ ((7 : ℝ) / 8 - 1) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 330 ≤ log x := by simpa using log_le_log (exp_pos (330 : ℝ)) hx
  have hl0 : 0 < log x := by linarith
  have h300 : 2 ≤ exp (300 : ℝ) := by linarith [add_one_le_exp (300 : ℝ)]
  have hab : exp (300 : ℝ) ≤ x := (exp_le_exp.mpr (by norm_num)).trans hx
  have hθ' : ∀ t ≥ exp 300, Eθ t ≤ K * t ^ ((7 : ℝ) / 8 - 1) := by
    intro t ht
    have := hθ t ht
    simpa using this
  have hp := FKS2Sol.Epi_le h300 hab
  rw [log_exp] at hp
  have hA := FKS2Pair.bounded_anchor h0 hOld
  have hw : 0 < x ^ ((7 : ℝ) / 8 - 1) := rpow_pos_of_pos hx0 _
  have hm : 0 ≤ log x / x := by positivity
  -- anchor
  have hld := logx_div_le hx
  have hanchor : log x / x * |primeCounting (exp 300) - Li (exp 300) -
      (Chebyshev.theta (exp 300) - exp 300) / 300| ≤
      330 / 300 * exp (45 / 4) * (1.6997e-12 + u0) * x ^ ((7 : ℝ) / 8 - 1) := by
    have hu : 0 ≤ 1.6997e-12 + u0 := by
      have : 0 ≤ Eθ (exp 300) := by unfold Eθ; positivity
      linarith
    calc _ ≤ (330 * exp (-(7 / 8 * 330)) * x ^ ((7 : ℝ) / 8 - 1)) *
            (exp 300 / 300 * (1.6997e-12 + u0)) := mul_le_mul hld hA (abs_nonneg _) (by positivity)
      _ = 330 / 300 * (exp (-(7 / 8 * 330)) * exp 300) * (1.6997e-12 + u0) *
            x ^ ((7 : ℝ) / 8 - 1) := by ring
      _ = _ := by rw [← exp_add]; norm_num
  -- integral
  have hI := power_integral_error hab hθ'
  have hJ := power_kernel_integral hab
  have hint : log x / x * |∫ t in exp 300..x, err t| ≤
      K * (600 / 521 / 330) * x ^ ((7 : ℝ) / 8 - 1) := by
    have h1 : log x / x * |∫ t in exp 300..x, err t| ≤
        log x / x * (K * (600 / 521 * x ^ ((7 : ℝ) / 8) / (log x) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hI.trans (mul_le_mul_of_nonneg_left hJ hK)) hm
    have hsplit : x ^ ((7 : ℝ) / 8) = x ^ ((7 : ℝ) / 8 - 1) * x := by
      rw [rpow_sub_one hx0.ne']; field_simp
    have h2 : log x / x * (K * (600 / 521 * x ^ ((7 : ℝ) / 8) / (log x) ^ 2)) =
        K * (600 / 521) * x ^ ((7 : ℝ) / 8 - 1) / log x := by
      rw [hsplit]; field_simp
    have h3 : K * (600 / 521) * x ^ ((7 : ℝ) / 8 - 1) / log x ≤
        K * (600 / 521 / 330) * x ^ ((7 : ℝ) / 8 - 1) := by
      rw [div_le_iff₀ hl0]
      have : 0 ≤ K * (600 / 521) * x ^ ((7 : ℝ) / 8 - 1) := by positivity
      have e : K * (600 / 521 / 330) * x ^ ((7 : ℝ) / 8 - 1) * log x =
          K * (600 / 521) * x ^ ((7 : ℝ) / 8 - 1) * (log x / 330) := by ring
      rw [e]
      have : 1 ≤ log x / 330 := by rw [le_div_iff₀ (by norm_num)]; linarith
      nlinarith
    linarith
  have hpt := hθ' x hab
  have hint' : log x / x * |∫ t in exp 300..x, (Chebyshev.theta t - t) / (t * (log t) ^ 2)| ≤
      K * (600 / 521 / 330) * x ^ ((7 : ℝ) / 8 - 1) := hint
  nlinarith

/-! ### The program instance -/

/-- `κ/330` as a rational. -/
def kappaQ : ℚ := 600 / 521 / 330

/-- The literal checks of a power transport program: inputs `[x₁, x₂]` at scale `2^{-k}` bound `K`
and `K·κ/330`, and the anchor literal `a` bounds `(330/300)·e^{45/4}·(1.6997·10⁻¹² + K·e^{-75/2})`. -/
def powerOK (K : ℚ) (k : ℕ) (xs : List ℚ) (a : ℚ) : Bool :=
  match xs with
  | [x₁, x₂] =>
      decide (0 ≤ K) && decide (K ≤ x₁ / 2 ^ k) && decide (K * kappaQ ≤ x₂ / 2 ^ k) &&
        expUpOK (45 / 16) && expUpOK (-75 / 8) &&
        decide (330 / 300 * expUp (45 / 16) * (1.6997e-12 + K * expUp (-75 / 8)) ≤ a)
  | _ => false

/-- The program part: a single-call certificate with one added constant. -/
theorem program_bound1 {src : String} {prog : Program} {eps B a : ℚ} {k : ℕ}
    (h : upperCheck src prog eps B = true) (hscale : (valuesOf prog).scale = 1 / 2 ^ k)
    (hops : (valuesOf prog).ops = [(.plus, a)]) :
    ((1 / 2 ^ k : ℚ) : ℝ) * ((valuesOf prog).xs.sum : ℝ) + (a : ℝ) ≤ B := by
  apply le_bound_of_check h
  rw [hscale, hops]
  simp only [opsConst]
  push_cast
  linarith

/-- **One theorem for every power configuration.** -/
theorem power_pi_bound {K : ℚ} {k : ℕ} {xs : List ℚ} {a B : ℚ}
    (hθ : HasPowerLogBound Eθ (K : ℝ) 0 (7 / 8) (exp 300)) (hAnchor : FKS2.v6.table4_anchor_300)
    (hok : powerOK K k xs a = true)
    (hB : ((1 / 2 ^ k : ℚ) : ℝ) * (xs.sum : ℝ) + (a : ℝ) ≤ B) :
    HasPowerLogBound Eπ (B : ℝ) 0 (7 / 8) (exp 330) := by
  match xs, hok with
  | [x₁, x₂], hok =>
    simp only [powerOK, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨⟨⟨⟨hK0, h1⟩, h2⟩, he1⟩, he2⟩, ha⟩ := hok
    have hK : (0 : ℝ) ≤ K := by exact_mod_cast hK0
    -- Eθ(e^300) ≤ K·e^{-75/2} ≤ K·expUp(-75/8)
    have hE1 := exp_le_expUp he1
    have hE2 := exp_le_expUp he2
    have h0 : Eθ (exp 300) ≤ (K : ℝ) * (expUp (-75 / 8) : ℝ) := by
      have := hθ (exp 300) le_rfl
      simp only [pow_zero, mul_one] at this
      refine this.trans (mul_le_mul_of_nonneg_left ?_ hK)
      have e : (exp 300 : ℝ) ^ ((7 : ℝ) / 8 - 1) = exp (4 * ((-75 / 8 : ℚ) : ℝ)) := by
        rw [rpow_def_of_pos (exp_pos _), log_exp]
        congr 1
        norm_num
      rw [e]
      exact hE2
    have hr := power_ray hK hθ h0 hAnchor
    intro x hx
    have hx0 : 0 < x := (exp_pos _).trans_le hx
    have hw : 0 < x ^ ((7 : ℝ) / 8 - 1) := rpow_pos_of_pos hx0 _
    refine (hr x hx).trans ?_
    simp only [pow_zero, mul_one]
    apply mul_le_mul_of_nonneg_right _ hw.le
    -- the coefficient is at most `2^{-k}(x₁ + x₂) + a ≤ B`
    have h1' : (K : ℝ) ≤ (x₁ : ℝ) / 2 ^ k := by exact_mod_cast h1
    have h2' : (K : ℝ) * (600 / 521 / 330) ≤ (x₂ : ℝ) / 2 ^ k := by
      have := (Rat.cast_le (K := ℝ)).2 h2
      simpa [kappaQ] using this
    have ha' : (330 / 300 : ℝ) * (expUp (45 / 16) : ℝ) *
        (1.6997e-12 + (K : ℝ) * (expUp (-75 / 8) : ℝ)) ≤ a := by
      have := (Rat.cast_le (K := ℝ)).2 ha
      push_cast at this
      linarith
    have hexp : exp (45 / 4 : ℝ) ≤ (expUp (45 / 16) : ℝ) := by
      have e : exp (45 / 4 : ℝ) = exp (4 * ((45 / 16 : ℚ) : ℝ)) := by
        congr 1
        norm_num
      rw [e]
      exact hE1
    have hu0 : 0 ≤ 1.6997e-12 + (K : ℝ) * (expUp (-75 / 8) : ℝ) := by
      have : (0 : ℝ) ≤ (expUp (-75 / 8) : ℝ) := (exp_pos _).le.trans hE2
      positivity
    have hanc : 330 / 300 * exp (45 / 4) * (1.6997e-12 + (K : ℝ) * (expUp (-75 / 8) : ℝ)) ≤ a := by
      refine le_trans ?_ ha'
      gcongr
    have hsum : ((1 / 2 ^ k : ℚ) : ℝ) * (([x₁, x₂].sum : ℚ) : ℝ) =
        (x₁ : ℝ) / 2 ^ k + (x₂ : ℝ) / 2 ^ k := by
      simp only [List.sum_cons, List.sum_nil]
      push_cast
      ring
    rw [hsum] at hB
    nlinarith

end Table4Evolution
