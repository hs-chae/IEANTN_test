/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldFloorConsumer
namespace WinnerStrongC4Source
open Real Set MeasureTheory
open WinnerOldFloors WinnerOldAnalytic
set_option maxHeartbeats 0
noncomputable def a1 : ℝ := 611/1000
noncomputable def a3 : ℝ := 551/20
noncomputable def a2 : ℝ := 6*a1/exp 1+a3
noncomputable def alpha : ℝ := 2371/20000
noncomputable def mzero : ℝ := sqrt (1+(2/3)*sqrt (6/5))
noncomputable def mone (u : ℝ) : ℝ := 6/Real.pi^2+(131/125)/u
noncomputable def mtwo (u : ℝ) : ℝ :=
  Real.pi*mzero*(31/50)/u+6*mzero/Real.pi*exp (-u)+
    Real.pi*mzero*(131/125)*exp (-u)/u
noncomputable def oldC4 (u : ℝ) : ℝ := a1^2*(sqrt (mone u)+1/(a3*sqrt u))^2
noncomputable def oldRatio (u : ℝ) : ℝ := mtwo u/mone u
noncomputable def oldRzero (u : ℝ) : ℝ := a2/(a1*exp (u/6)*u)
noncomputable def oldKernel (u y : ℝ) : ℝ :=
  exp (2*y-2*alpha*exp (2*y))*(exp (y/6)*(1+y/u)+oldRzero u)^2*(exp y+oldRatio u)
noncomputable def oldU (u : ℝ) : ℝ :=
  8*alpha*oldC4 u*exp (alpha/(2*exp (2*u)))*(∫ y : ℝ, oldKernel u y)

theorem mone_pos {u : ℝ} (hu : 0<u) : 0<mone u := by unfold mone;positivity
theorem mzero_pos : 0<mzero := by unfold mzero;positivity
theorem mtwo_nonneg {u : ℝ} (hu : 0<u) : 0≤mtwo u := by
  have hm:=mzero_pos
  unfold mtwo
  positivity
theorem oldRatio_nonneg {u : ℝ} (hu : 0<u) : 0≤oldRatio u :=
  div_nonneg (mtwo_nonneg hu) (mone_pos hu).le


end WinnerStrongC4Source
