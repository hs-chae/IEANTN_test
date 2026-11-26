/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSPositiveInfinite
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit.ZeroSummation

/-- Kernel proof of the positive-ordinate part of the formerly assumed CMS
scheme. Only the literal counting input and proved admissibility are supplied. -/
theorem positive_transfer (hcount : SourceCMSZeroCounting) (a : ℝ) (ha : exp 1≤ a)
    (zero : cmsPositiveZeroCount a=0) (root : cmsQ a=0)
    (F F' : ℝ → ℝ) (Δ : ℝ) (hΔ : 0<Δ) (hadm : CMSZeroAdmissible F F' Δ a) :
    Summable (cmsSignedAmplitude F Δ 1) ∧
      (∑'ρ : CMSZeroIndex,cmsSignedAmplitude F Δ 1 ρ)≤ cmsZeroMain F Δ a+Δ*cmsZeroRemainder F' Δ a:=by
  rcases hadm with ⟨hDeriv,hCont,hEven,hTail,hMain,hError,hQ,hR⟩
  let f : ℝ → ℝ:=fun t=>Δ*F (Δ*t)
  let f' : ℝ → ℝ:=fun t=>Δ^2*F' (Δ*t)
  have fd (t : ℝ) : HasDerivAt f (f' t) t:=by
    have inner : HasDerivAt (fun x : ℝ=>Δ*x) Δ t:=by simpa only [mul_one,id_eq] using! (hasDerivAt_id t).const_mul Δ
    have composed:=((hDeriv (Δ*t)).comp t inner).const_mul Δ
    exact composed.congr_deriv (by dsimp [f'];ring)
  have fc : Continuous f':=continuous_const.mul (hCont.comp (continuous_const.mul continuous_id))
  let mainFunction : ℝ → ℝ:=fun u=> log (u/(2*π*Δ))/(2*π)*|F u|
  let errorFunction : ℝ → ℝ:=fun u=>((3/20:ℝ)*log (u/Δ)+3)*|F' u|
  have mainEq (t : ℝ) : qDensity t*|f t|=Δ*mainFunction (Δ*t):=by
    have arg : Δ*t/(2*π*Δ)=t/(2*π):=by field_simp <;> ring
    dsimp [qDensity,f,mainFunction]
    rw [arg,abs_mul,abs_of_pos hΔ]
    ring
  have errorEq (t : ℝ) : countError t*|f' t|=Δ^2*errorFunction (Δ*t):=by
    dsimp [countError,f',errorFunction]
    rw [mul_div_cancel_left₀ _ hΔ.ne',abs_mul,abs_of_nonneg (sq_nonneg Δ)]
    ring
  have mainComp : IntegrableOn (fun t=> mainFunction (Δ*t)) (Ioi a):=
    (integrableOn_Ioi_comp_mul_left_iff mainFunction a hΔ).mpr hMain
  have errorComp : IntegrableOn (fun t=> errorFunction (Δ*t)) (Ioi a):=
    (integrableOn_Ioi_comp_mul_left_iff errorFunction a hΔ).mpr hError
  have mainInt : IntegrableOn (fun t=> qDensity t*|f t|) (Ioi a):=by
    apply (mainComp.const_mul Δ).congr
    filter_upwards [] with t
    exact (mainEq t).symm
  have errorInt : IntegrableOn (fun t=> countError t*|f' t|) (Ioi a):=by
    apply (errorComp.const_mul (Δ^2)).congr
    filter_upwards [] with t
    exact (errorEq t).symm
  have mainIntegral : (∫t in Ioi a,qDensity t*|f t|)=cmsZeroMain F Δ a:=by
    simp_rw [mainEq]
    rw [integral_const_mul,integral_comp_mul_left_Ioi mainFunction a hΔ]
    change Δ*(Δ⁻¹*(∫u in Ioi (Δ*a),mainFunction u))=cmsZeroMain F Δ a
    rw [←mul_assoc,mul_inv_cancel₀ hΔ.ne',one_mul]
    rfl
  have errorIntegral : (∫t in Ioi a,countError t*|f' t|)=Δ*cmsZeroRemainder F' Δ a:=by
    simp_rw [errorEq]
    rw [integral_const_mul,integral_comp_mul_left_Ioi errorFunction a hΔ]
    change Δ^2*(Δ⁻¹*(∫u in Ioi (Δ*a),errorFunction u))=Δ*cmsZeroRemainder F' Δ a
    rw [←mul_assoc,show Δ^2*Δ⁻¹=Δ by field_simp]
    rfl
  have boundary : Tendsto (fun T : ℝ=>|f T| * cmsCountRemainder T) atTop (𝓝 0):=by
    simpa only [f,abs_mul,abs_of_pos hΔ] using hR
  obtain ⟨sum,bound⟩:=actual_positive_infinite hcount a ha zero root f f' fd fc mainInt errorInt boundary
  have same : positiveFamily f=cmsSignedAmplitude F Δ 1:=by
    funext ρ
    simp only [positiveFamily,cmsSignedAmplitude,one_mul,f,abs_mul,abs_of_pos hΔ]
    split_ifs <;> ring
  rw [same] at sum bound
  rw [mainIntegral,errorIntegral] at bound
  exact ⟨sum,bound⟩

#print axioms positive_transfer
end RH080Next.Explicit.ZeroSummation
