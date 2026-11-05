/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.ClosedMoment
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Actual KLN Eqs.2.4--2.11 source objects for k=1, without importing an
axiom identifying an abstract F with the intended cumulative square integral.
The original raw Minkowski and smoothing relations remain named source inputs;
all new normalization, source-object regularity and U=1.34 are proved. -/
namespace WinnerBetaA.ActualObject
open Real Complex Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.Minkowski WinnerBetaA.ClosedMoment

noncomputable def vertical (σ t : ℝ) : ℂ := (σ:ℂ)+(t:ℂ)*Complex.I

noncomputable def mollifier (X : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius n:ℂ)*(n:ℂ)^(-s)

noncomputable def mollifiedError (X : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s*mollifier X s-1

noncomputable def cumulativeSquare (X σ t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, ‖mollifiedError X (vertical σ u)‖^2

/-- X=kT=T here; the argument of F_X is the actual xT. -/
noncomputable def scaledCriticalF (T x : ℝ) : ℝ := cumulativeSquare T (1/2) (x*T)

noncomputable def smoothingWeight (T : ℝ) (s : ℂ) : ℂ :=
  ((s-1)/s)*Complex.exp (((601/5000:ℝ):ℂ)*(s/(T:ℂ))^2)

noncomputable def sourceMoment (T σ : ℝ) : ℝ :=
  ∫ t : ℝ, ‖smoothingWeight T (vertical σ t)*mollifiedError T (vertical σ t)‖^2

theorem vertical_continuous (σ : ℝ) : Continuous (vertical σ) := by
  unfold vertical
  fun_prop

theorem mollifier_continuous (X : ℝ) : Continuous (mollifier X) := by
  unfold mollifier
  apply continuous_finsetSum
  intro n hn
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n≠0)
  exact continuous_const.mul (continuous_neg.const_cpow (Or.inl hn0))

theorem critical_error_continuous (X : ℝ) :
    Continuous (fun t : ℝ => mollifiedError X (vertical (1/2) t)) := by
  have hζ : Continuous (fun t : ℝ => riemannZeta (vertical (1/2) t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hs : vertical (1/2) t ≠ 1 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num [vertical] at hr
    exact (differentiableAt_riemannZeta hs).continuousAt.comp
      (vertical_continuous (1/2)).continuousAt
  exact (hζ.mul ((mollifier_continuous X).comp (vertical_continuous (1/2)))).sub continuous_const

theorem cumulative_critical_continuous (X : ℝ) :
    Continuous (cumulativeSquare X (1/2)) := by
  have hi : Continuous (fun u : ℝ => ‖mollifiedError X (vertical (1/2) u)‖^2) :=
    (critical_error_continuous X).norm.pow 2
  exact (intervalIntegral.differentiable_integral_of_continuous hi).continuous

theorem scaledCriticalF_continuous (T : ℝ) : Continuous (scaledCriticalF T) := by
  exact (cumulative_critical_continuous T).comp (continuous_id.mul continuous_const)

theorem scaledCriticalF_nonneg {T x : ℝ} (hT : 0 ≤ T) (hx : 0 ≤ x) :
    0 ≤ scaledCriticalF T x := by
  unfold scaledCriticalF cumulativeSquare
  exact intervalIntegral.integral_nonneg_of_forall (mul_nonneg hx hT) (by intro u; positivity)

/-- The source boundary has exactly two independently named relations, rather
than an abstract F, its regularity, or an assumed new moment/density estimate. -/
theorem actual_source_left_U134 {T : ℝ}
    (hHT : height ≤ T)
    (hRawMinkowski : ∀ x > 0,
      scaledCriticalF T x ≤ rawAmplitude (309/500) (1413/500) sourceM1 sourceM2 T x ^ 2)
    (hSourceSmoothing : sourceMoment T (1/2) ≤
      (8*(601/5000:ℝ)*Real.exp ((601/5000:ℝ)/(2*T^2)))*
        (∫ x in Ioi 0, gaussianWeight x * scaledCriticalF T x)) :
    sourceMoment T (1/2) ≤ (67/50:ℝ)*T^((4:ℝ)/3)*Real.log T^3 := by
  have hT : 0 ≤ T := le_trans (by norm_num [height]) hHT
  exact source_left_moment_U134_count_form hHT (scaledCriticalF_continuous T).continuousOn
    (fun x hx => scaledCriticalF_nonneg hT hx.le) hRawMinkowski hSourceSmoothing

#print axioms scaledCriticalF_continuous
#print axioms scaledCriticalF_nonneg
#print axioms actual_source_left_U134
#check actual_source_left_U134
end WinnerBetaA.ActualObject
