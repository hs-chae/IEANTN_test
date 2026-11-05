/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldFloorConsumer
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors WinnerOldAnalytic
set_option maxHeartbeats 0
noncomputable def a1 : ℝ := 611/1000
noncomputable def a3 : ℝ := 1461/1000
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

theorem oldC4_lower {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    c4Floor v≤oldC4 u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hvp : 0<h+v := by positivity
  have hm : mone (h+v)≤mone u := by
    unfold mone
    gcongr
  have hs := sqrt_le_sqrt hm
  have hsqrt : sqrt u≤sqrt (h+v) := sqrt_le_sqrt hur
  have hrecip : 1/(a3*sqrt (h+v))≤1/(a3*sqrt u) := by
    apply one_div_le_one_div_of_le (by unfold a3;positivity)
    unfold a3
    gcongr
  unfold c4Floor oldC4 a1
  have hsum : sqrt (mone (h+v))+1/(a3*sqrt (h+v))≤sqrt (mone u)+1/(a3*sqrt u) := by linarith
  have hzero : 0≤sqrt (mone (h+v))+1/(a3*sqrt (h+v)) := by unfold a3;positivity
  have hsq:=pow_le_pow_left₀ hzero hsum 2
  unfold mone a3 at hsq
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

theorem oldRatio_lower {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    ratioFloor v≤oldRatio u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hvp : 0<h+v := by positivity
  have hM:=mzero_pos
  have hm:=mone_pos hup
  have hbase : Real.pi*mzero*(31/50)/u≤mtwo u := by
    unfold mtwo
    have h1 : 0≤6*mzero/Real.pi*exp (-u) := by positivity
    have h2 : 0≤Real.pi*mzero*(131/125)*exp (-u)/u := by positivity
    linarith
  have he : (Real.pi*mzero*(31/50)/u)/mone u=
      Real.pi*mzero*(31/50)/(6/Real.pi^2*u+131/125) := by
    unfold mone
    field_simp [hup.ne',Real.pi_ne_zero]
    <;> ring
  have hl : Real.pi*mzero*(31/50)/(6/Real.pi^2*(h+v)+131/125)≤
      Real.pi*mzero*(31/50)/(6/Real.pi^2*u+131/125) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  unfold oldRatio ratioFloor
  change Real.pi*mzero*(31/50)/(6/Real.pi^2*(h+v)+131/125)≤mtwo u/mone u
  exact hl.trans (he ▸ div_le_div_of_nonneg_right hbase hm.le)

/-- On a fixed compact log window the old global-C4 kernel dominates the
same lower integrand whose executable cells were checked. -/
theorem oldKernel_lower {u v y : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v)
    (hy : y∈Icc (-3:ℝ) 3) :
    kernel alpha (if y≤0 then h else h+v) (ratioFloor v) y≤oldKernel u y := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hvp : 0<h+v := by positivity
  have hrat:=oldRatio_lower hv hlu hur
  have hr0 : 0≤oldRzero u := by unfold oldRzero a2 a1 a3;positivity
  have hfrac : y/(if y≤0 then h else h+v)≤y/u := by
    split_ifs with hy0
    · apply (div_le_div_iff₀ hh hup).mpr
      have hm:=mul_le_mul_of_nonpos_left hlu hy0
      nlinarith
    · exact div_le_div_of_nonneg_left (by linarith) hup hur
  have hfpos : 0≤1+y/(if y≤0 then h else h+v) := by
    have hden : 0<(if y≤0 then h else h+v) := by split_ifs <;> positivity
    have hd28 : 28≤(if y≤0 then h else h+v) := by split_ifs <;> linarith [h_lower]
    have hydiv : (-1:ℝ)≤y/(if y≤0 then h else h+v) :=
      (le_div_iff₀ hden).mpr (by linarith [hy.1])
    linarith
  have hAmp : exp (y/6)*(1+y/(if y≤0 then h else h+v))≤exp (y/6)*(1+y/u)+oldRzero u := by
    have hm:=mul_le_mul_of_nonneg_left hfrac (exp_pos (y/6)).le
    nlinarith
  have hPow:=pow_le_pow_left₀ (mul_nonneg (exp_pos _).le hfpos) hAmp 2
  have hExp : exp (y/3)=exp (y/6)^2 := by rw [pow_two,←exp_add];congr 1;ring
  unfold kernel oldKernel
  rw [hExp]
  calc
    _ = exp (2*y-2*alpha*exp (2*y))*
      (exp (y/6)*(1+y/(if y≤0 then h else h+v)))^2*(exp y+ratioFloor v) := by ring
    _ ≤ _ := by
      have hn:=ratio_nonneg hv
      gcongr

#print axioms oldC4_lower
#print axioms oldRatio_lower
#print axioms oldKernel_lower
end WinnerOldC4Source
