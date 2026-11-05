/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongWarmRowConsumer
import SourceBoundaryNonneg
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldC4Source WinnerOriginalScalars
set_option maxHeartbeats 0
/-- Exact positive source boundary allowance in the old log-density expression,
normalized by T=exp(WinnerOldFloors.h+v). It is not a zero-count lower bound. -/
noncomputable def boundaryAllowance (s v : ℝ) : ℝ :=
  ((sourceCSeven eulerMascheroniConstant*(boundaryMu-(s-d/(WinnerOldFloors.h+v)))+
      sourceCEight eulerMascheroniConstant/2)*(WinnerOldFloors.h+v)^2*exp (-(WinnerOldFloors.h+v)))/(2*Real.pi*d)
noncomputable def rosserError (u : ℝ) : ℝ := (137/1000)*u+(443/1000)*log u+397/250
/-- G/2: the full original Rosser difference allowance, divided by T. -/
noncomputable def windowAllowance (v : ℝ) : ℝ :=
  windowMain v+exp (-(WinnerOldFloors.h+v))*(rosserError (WinnerOldFloors.h+v)+rosserError WinnerOldFloors.h)/2
/-- Complete old positive log/window allowance before the downstream spectral
functional. Its validity consumes the named original source relationships. -/
noncomputable def allowance (s v : ℝ) : ℝ :=
  min (main s v+boundaryAllowance s v) (windowAllowance v)
 theorem boundary_nonnegative {s v : ℝ} (hs : s ≤ 7/8) (hv : 0 ≤ v) : 0 ≤ boundaryAllowance s v := by
  have hh : 0<WinnerOldFloors.h := by linarith [h_lower]
  have hup : 0<WinnerOldFloors.h+v := by positivity
  have hshift : 0 ≤ boundaryMu-(s-d/(WinnerOldFloors.h+v)) := by
    have hd : 0 ≤ d/(WinnerOldFloors.h+v) := by unfold d;positivity
    unfold boundaryMu
    linarith
  have hd : 0<d := by norm_num [d]
  have hC7:=source_cseven_nonnegative
  have hC8:=source_ceight_nonnegative
  unfold boundaryAllowance
  positivity
 theorem rosserError_nonnegative {u : ℝ} (hu : 1 ≤ u) : 0 ≤ rosserError u := by
  have hu0 : 0 ≤ u := by linarith
  have hul : 0 ≤ log u := log_nonneg hu
  unfold rosserError
  positivity
 theorem window_dominates {v : ℝ} (hv : 0 ≤ v) : windowMain v ≤ windowAllowance v := by
  have h1:=rosserError_nonnegative (show 1 ≤ WinnerOldFloors.h+v by linarith [h_lower])
  have h2:=rosserError_nonnegative (show 1 ≤ WinnerOldFloors.h by linarith [h_lower])
  unfold windowAllowance
  have hp : 0 ≤ exp (-(WinnerOldFloors.h+v))*(rosserError (WinnerOldFloors.h+v)+rosserError WinnerOldFloors.h)/2 := by positivity
  linarith
 theorem witness_le_full_allowance {s v : ℝ} (hs : s ≤ 7/8) (hv : 0 ≤ v) : witness s v ≤ allowance s v :=
  min_le_min (by linarith [boundary_nonnegative hs hv]) (window_dominates hv)
 theorem weighted_le_full_allowance {s v : ℝ} (hs : s ≤ 7/8) (hv : 0 ≤ v) :
    weighted s v ≤ exp ((30001/100:ℝ)*(s-7/8))*allowance s v :=
  mul_le_mul_of_nonneg_left (witness_le_full_allowance hs hv) (exp_pos _).le
#print axioms witness_le_full_allowance
end WinnerStrongEnvelope
