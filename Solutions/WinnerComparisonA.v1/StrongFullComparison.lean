/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongComparison
import StrongFullRegularity
import RectangleMono
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors
set_option maxHeartbeats 0
/-- Full original log/window density contribution for T=exp(L/3). Every
source C7/C8 and Rosser error term is retained. This component is not by
itself an upper bound for prime error. -/
noncomputable def oldDensityComponent (L : ℝ) : ℝ :=
  2*L*(∫s in (3/4:ℝ)..(7/8),∫v in (0:ℝ)..(L/3-h),weightedAllowance L s v)
/-- Positive endpoint in the original reciprocal-ordinate partial summation. -/
noncomputable def oldEndpointAllowance (L : ℝ) : ℝ :=
  2*L*(∫s in (3/4:ℝ)..(7/8),weightedAllowance L s (L/3-h))
/-- The original CH2 low-strip Rosser spectral allowance at log T=L/3. -/
noncomputable def oldLowAllowance (L : ℝ) : ℝ :=
  exp (-L/8)*((L/3)^2/(2*Real.pi)+(2+1/Real.pi)*(L/3))
/-- Named old parameter instance with the same integrated-zero transfer.
Original source-layer validity is supplied separately: this definition records
its full positive functional, rather than claiming that a lower benchmark
is a zero-count or prime-error upper bound. -/
noncomputable def oldFullAllowance (L : ℝ) : ℝ :=
  (1001/1000)*(oldDensityComponent L+oldEndpointAllowance L+oldLowAllowance L)+1/100000000
 theorem density_component_nonnegative {L : ℝ} (hL : 300 ≤ L) : 0 ≤ oldDensityComponent L := by
  have hh : h ≤ 29 := WinnerOldOuter.Assembly.height_log_bounds.2
  have hb : 0 ≤ L/3-h := by linarith
  unfold oldDensityComponent
  apply mul_nonneg (by linarith)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  apply intervalIntegral.integral_nonneg hb
  intro v hv
  exact weightedAllowance_nonnegative hs.2 hv.1
 theorem endpoint_nonnegative {L : ℝ} (hL : 300 ≤ L) : 0 ≤ oldEndpointAllowance L := by
  have hh : h ≤ 29 := WinnerOldOuter.Assembly.height_log_bounds.2
  have hb : 0 ≤ L/3-h := by linarith
  unfold oldEndpointAllowance
  apply mul_nonneg (by linarith)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun s hs=>weightedAllowance_nonnegative hs.2 hb)
 theorem low_nonnegative {L : ℝ} (hL : 300 ≤ L) : 0 ≤ oldLowAllowance L := by
  unfold oldLowAllowance
  have hLp : 0 ≤ L := by linarith
  positivity
 theorem density_le_full {L : ℝ} (hL : 300 ≤ L) : oldDensityComponent L ≤ oldFullAllowance L := by
  have hd:=density_component_nonnegative hL
  have he:=endpoint_nonnegative hL
  have hl:=low_nonnegative hL
  unfold oldFullAllowance
  nlinarith
 theorem benchmark_le_full_density {L : ℝ} (hL : 300 ≤ L) (hL' : L ≤ 30001/100) :
    benchmark ≤ oldDensityComponent L := by
  have hh : h ≤ 29 := WinnerOldOuter.Assembly.height_log_bounds.2
  have hb : (16:ℝ) ≤ L/3-h := by linarith
  have hFG : ∀s∈Icc (33/40:ℝ) (7/8),∀v∈Icc (1/10000:ℝ) 16,
      weighted s v ≤ weightedAllowance L s v := by
    intro s hs v hv
    have hexp : exp ((30001/100:ℝ)*(s-7/8)) ≤ exp (L*(s-7/8)) :=
      exp_le_exp.mpr (mul_le_mul_of_nonpos_right hL' (by linarith [hs.2]))
    exact mul_le_mul hexp (witness_le_full_allowance hs.2 (by linarith [hv.1]))
      (witness_nonnegative (by linarith [hv.1])) (exp_pos _).le
  have hMono:=WinnerOldOuter.Rectangles.rowIntegral_mono_box
    (F:=weighted) (G:=weightedAllowance L) (lo:=33/40) (hi:=7/8) (lo':=3/4) (hi':=7/8)
    (a:=1/10000) (b:=16) (a':=0) (b':=L/3-h)
    (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num) hb
    continuousOn_rectangle (full_regular L (3/4) (7/8) (L/3-h)) hFG
    (fun s hs v hv=>weightedAllowance_nonnegative hs.2 hv.1)
  change benchmark ≤ 600*(∫s in (3/4:ℝ)..(7/8),∫v in (0:ℝ)..(L/3-h),weightedAllowance L s v) at hMono
  have hI : 0 ≤ (∫s in (3/4:ℝ)..(7/8),∫v in (0:ℝ)..(L/3-h),weightedAllowance L s v) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro s hs
    exact intervalIntegral.integral_nonneg (by linarith) (fun v hv=>weightedAllowance_nonnegative hs.2 hv.1)
  unfold oldDensityComponent
  exact hMono.trans (mul_le_mul_of_nonneg_right (by linarith : (600:ℝ) ≤ 2*L) hI)
 theorem oldFullAllowance_lower {L : ℝ} (hL : 300 ≤ L) (hL' : L ≤ 30001/100) :
    (18973/2000000:ℝ) ≤ oldFullAllowance L :=
  benchmark_rounded_lower.trans ((benchmark_le_full_density hL hL').trans (density_le_full hL))
 theorem uniform_coefficient_strict {L : ℝ} (hL : 300 ≤ L) (hL' : L ≤ 30001/100) :
    (2371/250000:ℝ)<oldFullAllowance L := by linarith [oldFullAllowance_lower hL hL']
 theorem uniform_margin {L : ℝ} (hL : 300 ≤ L) (hL' : L ≤ 30001/100) :
    (1/400000:ℝ) ≤ oldFullAllowance L-(2371/250000) := by linarith [oldFullAllowance_lower hL hL']
#print axioms uniform_coefficient_strict
#print axioms benchmark_le_full_density
end WinnerStrongEnvelope
