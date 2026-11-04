/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalScalars
namespace WinnerOriginalScalars
open LeanCert.Core LeanCert.Engine Real
set_option maxHeartbeats 0

@[simp] theorem value_lit (q : ℚ) : value (lit q)=(q:ℝ) := rfl
@[simp] theorem value_add (e f : Expr) : value (add e f)=value e+value f := rfl
@[simp] theorem value_mul (e f : Expr) : value (mul e f)=value e*value f := rfl
@[simp] theorem value_div (e f : Expr) : value (dv e f)=value e/value f := by rfl
@[simp] theorem value_sq (e : Expr) : value (sq e)=value e^2 := by simp [sq,pow_two]
@[simp] theorem value_inv (e : Expr) : value (.inv e)=(value e)⁻¹ := rfl
@[simp] theorem value_log (e : Expr) : value (.log e)=log (value e) := rfl
@[simp] theorem value_exp (e : Expr) : value (.exp e)=exp (value e) := rfl
@[simp] theorem value_pi : value pival=Real.pi := rfl

theorem value_rt (e : Expr) (hp : 0<value e) : value (rt e)=sqrt (value e) := by
  simp only [rt,value_exp,value_div,value_log,value_lit]
  rw [sqrt_eq_rpow,rpow_def_of_pos hp]
  congr 1
  ring

noncomputable def height : ℝ := 3000000000000
noncomputable def sourceM0 : ℝ := sqrt (1+(2/3)*sqrt (6/5))
noncomputable def sourceM1 : ℝ := 6/Real.pi^2+(131/125)/log height
noncomputable def sourceM2 : ℝ := Real.pi*sourceM0*(31/50)/log height+
  6*sourceM0/(Real.pi*height)+Real.pi*sourceM0*(131/125)/(height*log height)
noncomputable def sourceR0 : ℝ := (1413/500)/((309/500)*height^((1:ℝ)/6)*log height)
noncomputable def sourceR1 : ℝ := 1/((309/500)*height^((1:ℝ)/6)*log height*sqrt (log height))
noncomputable def sourceOmega : ℝ := exp ((601/5000)/(2*height^2))

theorem height_semantics : value h0=height := by norm_num [h0,height]
theorem log_semantics : value h=log height := by simp [h,height]
theorem mzero_semantics : value mzero=sourceM0 := by
  unfold mzero
  rw [value_rt _ (by simp [rt]; positivity)]
  simp only [value_add,value_lit,value_mul]
  rw [value_rt _ (by norm_num)]
  norm_num [sourceM0]

theorem mone_semantics : value mone=sourceM1 := by
  simp [mone,sourceM1,log_semantics]

theorem mtwo_semantics : value mtwo=sourceM2 := by
  simp [mtwo,sourceM2,log_semantics,height,mzero_semantics]

theorem rootHeight_semantics : value rootHeight=height^((1:ℝ)/6) := by
  simp only [rootHeight,value_exp,value_div,log_semantics,value_lit]
  rw [rpow_def_of_pos (by norm_num [height])]
  congr 1
  ring

theorem rzero_semantics : value rzero=sourceR0 := by
  simp [rzero,sourceR0,rootHeight_semantics,log_semantics]

theorem rone_semantics : value rone=sourceR1 := by
  simp only [rone,value_inv,value_mul,value_lit,rootHeight_semantics,log_semantics]
  rw [value_rt _ (by rw [log_semantics]; have h:=height_log_lower;rw [log_semantics] at h;linarith)]
  rw [log_semantics]
  norm_num [sourceR1,one_div]

theorem omega_semantics : value omega=sourceOmega := by
  simp [omega,sourceOmega,alpha,height]

theorem source_log_lower : (28:ℝ)≤log height := by simpa [log_semantics] using height_log_lower
theorem source_mone_upper : sourceM1≤129/200 := by simpa [mone_semantics] using mean_one_upper
theorem source_mtwo_upper : sourceM2≤23/250 := by simpa [mtwo_semantics] using mean_two_upper
theorem source_rzero_upper : sourceR0≤681/500000 := by simpa [rzero_semantics] using rzero_upper
theorem source_rone_upper : sourceR1≤23/250000 := by simpa [rone_semantics] using rone_upper
theorem source_omega_upper : sourceOmega≤1000000000001/1000000000000 := by simpa [omega_semantics] using omega_upper
#print axioms source_mone_upper
#print axioms source_rone_upper
end WinnerOriginalScalars
