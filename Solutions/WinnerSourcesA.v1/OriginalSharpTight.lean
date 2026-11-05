/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalSharpScalars
namespace WinnerOriginalScalars.Tight
open LeanCert.Core LeanCert.Engine Real
set_option maxHeartbeats 0

def sharpPhi : Expr := add (lit (4/3))
  (mul (dv (lit (263/200)) (lit (17/2)))
    (.exp (sub (.neg (dv (mul (lit 8) delta) (lit 3))) (lit 1))))
def smoothingR : Expr := dv (lit (1/2))
  (sq (sub (lit 1) (.inv (sub h0 (lit 1)))))
def sharpKappa : Expr :=
  let exponent := add (add (mul (lit 2) alpha)
    (add (mul (lit (1/4)) (.log (lit (263/200))))
      (mul (lit (3/4)) (.log (lit (17/2))))))
    (mul (add (mul (lit 2) dd) (mul (mul (lit 2) delta) (lit (3/4)))) sharpPhi)
  dv (mul smoothingR (.exp exponent)) (mul (mul (lit 2) pival) dd)
def sharpSlope : Expr := add
  (mul (lit 2) (.log (dv (lit (17/2)) (lit (263/200)))))
  (mul (mul (lit 4) delta) sharpPhi)

theorem sharp_kappa_upper : value sharpKappa ≤ 151/20 := by
  have hz := closed_upper sharpKappa (151/20) (by native_decide)
  norm_num at hz ⊢
  exact hz

theorem sharp_slope_lower : (271/50:ℝ) ≤ value sharpSlope := by
  have hz := closed_lower sharpSlope (271/50) (by native_decide)
  norm_num at hz ⊢
  exact hz


noncomputable def sourceSharpPhi : ℝ := 4/3+((263/200)/(17/2))*exp (-8*(3119/10000)/3-1)
noncomputable def sourceSmoothingR : ℝ := (1/2)/(1-1/(height-1))^2
noncomputable def sourceSharpKappa : ℝ :=
  (sourceSmoothingR*exp (2*(601/5000))/(2*Real.pi*(851/2500)))*
    (263/200:ℝ)^((1:ℝ)/4)*(17/2:ℝ)^((3:ℝ)/4)*
    exp ((2*(851/2500)+2*(3119/10000)*(3/4))*sourceSharpPhi)
noncomputable def sourceSharpSlope : ℝ := 2*log ((17/2)/(263/200))+4*(3119/10000)*sourceSharpPhi

theorem sharpPhi_semantics : value sharpPhi=sourceSharpPhi := by
  norm_num [sharpPhi,sourceSharpPhi,delta]

theorem smoothingR_semantics : value smoothingR=sourceSmoothingR := by
  norm_num [smoothingR,sourceSmoothingR,height]

theorem sharpKappa_semantics : value sharpKappa=sourceSharpKappa := by
  simp only [sharpKappa,value_div,value_mul,value_add,value_exp,value_lit,value_log,
    value_pi,sharpPhi_semantics,smoothingR_semantics]
  norm_num only [alpha,dd,value_lit]
  unfold sourceSharpKappa
  rw [rpow_def_of_pos (by norm_num : (0:ℝ)<263/200),
    rpow_def_of_pos (by norm_num : (0:ℝ)<17/2)]
  rw [show log (263/200:ℝ)*(1/4)=1/4*log (263/200:ℝ) by ring,
    show log (17/2:ℝ)*(3/4)=3/4*log (17/2:ℝ) by ring]
  simp only [exp_add]
  ring

theorem sharpSlope_semantics : value sharpSlope=sourceSharpSlope := by
  simp [sharpSlope,sourceSharpSlope,sharpPhi_semantics,delta]

theorem source_sharp_kappa_upper : sourceSharpKappa≤151/20 := by
  simpa [sharpKappa_semantics] using sharp_kappa_upper

theorem source_sharp_slope_lower : (271/50:ℝ)≤sourceSharpSlope := by
  simpa [sharpSlope_semantics] using sharp_slope_lower

#print axioms source_sharp_kappa_upper
#print axioms source_sharp_slope_lower
end WinnerOriginalScalars.Tight
