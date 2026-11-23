import GlobalW640
import Mathlib.Analysis.Calculus.SmoothSeries
namespace RHContinuation.Ramanujan
open Real Set Filter RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def eiDerivTerm (z : ℝ) (n : ℕ) : ℝ :=
  z^n / (Nat.factorial (n+1):ℝ)

lemma eiTerm_hasDerivAt (z : ℝ) (n : ℕ) :
    HasDerivAt (fun t => eiTerm t n) (eiDerivTerm z n) z := by
  have hn : (n+1:ℝ) ≠ 0 := by positivity
  have hf : (Nat.factorial (n+1):ℝ) ≠ 0 := by positivity
  convert! (((hasDerivAt_id z).pow (n+1)).div_const
    ((n+1:ℝ)*(Nat.factorial (n+1):ℝ))) using 1 <;> first | rfl | skip
  dsimp [eiDerivTerm]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, mul_one]
  field_simp

lemma eiDerivTerm_norm_bound {R y : ℝ} (hR : 0 ≤ R) (hy : ‖y‖ ≤ R) (n : ℕ) :
    ‖eiDerivTerm y n‖ ≤ R^n / (Nat.factorial n:ℝ) := by
  have hp := pow_le_pow_left₀ (norm_nonneg y) hy n
  have hf : (Nat.factorial n:ℝ) ≤ Nat.factorial (n+1) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  have hf0 : (0:ℝ) < Nat.factorial n := by positivity
  dsimp [eiDerivTerm]
  rw [abs_div,abs_pow,abs_of_pos (show (0:ℝ) < (Nat.factorial (n+1):ℝ) by positivity)]
  change |y|^n / (Nat.factorial (n+1):ℝ) ≤ _
  exact div_le_div₀ (pow_nonneg hR _) hp hf0 hf

lemma eiSeries_hasDerivAt (z : ℝ) :
    HasDerivAt (fun t => ∑' n, eiTerm t n) (∑' n, eiDerivTerm z n) z := by
  let R := ‖z‖+1
  have hR : 0 < R := by dsimp [R];positivity
  have hz : z ∈ Metric.ball (0:ℝ) R := by
    rw [Metric.mem_ball,dist_zero_right]
    dsimp [R]
    linarith
  have hzero : (0:ℝ) ∈ Metric.ball (0:ℝ) R := by simpa using hR
  exact hasDerivAt_tsum_of_isPreconnected (Real.summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0:ℝ) R).isPreconnected
    (fun n y _ => eiTerm_hasDerivAt y n)
    (fun n y hy => eiDerivTerm_norm_bound hR.le
      (by exact le_of_lt (by simpa [Metric.mem_ball,dist_zero_right] using hy)) n)
    hzero (by simp [eiTerm]) hz

lemma eiDerivTerm_summable (z : ℝ) : Summable (fun n => eiDerivTerm z n) := by
  exact (Real.summable_pow_div_factorial ‖z‖).of_norm_bounded
    (fun n => eiDerivTerm_norm_bound (norm_nonneg z) (le_refl _) n)

lemma eiDerivTerm_sum_mul (z : ℝ) :
    z*(∑' n, eiDerivTerm z n) = exp z-1 := by
  have hshift := tsum_eq_zero_add'
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial z))
  have he : exp z = 1 + ∑' n, z^(n+1)/(Nat.factorial (n+1):ℝ) := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    simpa using hshift
  rw [← tsum_mul_left]
  have hf : (∑' n, z*eiDerivTerm z n) =
      ∑' n, z^(n+1)/(Nat.factorial (n+1):ℝ) := by
    apply tsum_congr
    intro n
    unfold eiDerivTerm
    rw [pow_succ]
    ring
  rw [hf]
  linarith

/-- Exact derivative of the full Ei power series with any additive constant. -/
theorem li_series_model_hasDerivAt (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => C+log (log y)+∑' n, eiTerm (log y) n) (1/log x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl0 : 0 < log x := log_pos hx
  have hlog := Real.hasDerivAt_log hx0
  have hll := (Real.hasDerivAt_log hl0.ne').comp x hlog
  have hseries := (eiSeries_hasDerivAt (log x)).comp x hlog
  have hd := ((hll.const_add C).add hseries)
  have he := eiDerivTerm_sum_mul (log x)
  rw [exp_log (by linarith : 0 < x)] at he
  have hcoeff : (log x)⁻¹ * x⁻¹ + (∑' n, eiDerivTerm (log x) n)*x⁻¹ =
      1/log x := by
    field_simp [hx0,hl0.ne']
    nlinarith [he]
  convert! hd using 1 <;> first | exact hcoeff.symm | rfl

/-- Termwise differentiation proves the entire-series derivative.
The retained identity with principal-value li is enough; a separate derivative
identity no longer needs to be assumed. -/
theorem li_derivative_from_series {li : ℝ → ℝ}
    (hs : LogIntegralSeriesIdentity li) :
    Ramanujan640.AnalyticBarrier.LiDerivativeFromOne li := by
  intro x hx
  have hx0 : x ≠ 0 := by linarith
  have hl0 : 0 < log x := log_pos hx
  have hlog := Real.hasDerivAt_log hx0
  have hll := (Real.hasDerivAt_log hl0.ne').comp x hlog
  have hseries := (eiSeries_hasDerivAt (log x)).comp x hlog
  have hd := ((hll.const_add Real.eulerMascheroniConstant).add hseries)
  have he := eiDerivTerm_sum_mul (log x)
  rw [exp_log (by linarith : 0 < x)] at he
  have hcoeff : (log x)⁻¹ * x⁻¹ + (∑' n, eiDerivTerm (log x) n)*x⁻¹ =
      1/log x := by
    field_simp [hx0,hl0.ne']
    nlinarith [he]
  have hd' : HasDerivAt
      (fun y => Real.eulerMascheroniConstant+log (log y)+∑' n, eiTerm (log y) n)
      (1/log x) x := by
    convert! hd using 1 <;> first | exact hcoeff.symm | rfl
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact hs y hy

#print axioms eiSeries_hasDerivAt
#print axioms li_derivative_from_series
end RHContinuation.Ramanujan
