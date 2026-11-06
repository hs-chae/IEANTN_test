/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HeightProfileScalars
namespace PVEvolutionA.Recovery.Profile
open Real LeanCert.Core WinnerOriginalScalars WinnerBetaA.HeightSource WinnerDensitySource
set_option maxHeartbeats 0
noncomputable def anchor (p : WinnerHeightProfiles.Row) : ℝ := height*exp ((p).shift)
def anchorExpr (p : WinnerHeightProfiles.Row) : Expr := mul h0 (.exp (lit (p).shift))
def logExpr (p : WinnerHeightProfiles.Row) : Expr := .log (anchorExpr p)
def rootExpr (p : WinnerHeightProfiles.Row) : Expr := .exp (dv (logExpr p) (lit 6))
def oneExpr (p : WinnerHeightProfiles.Row) : Expr := add (dv (lit 6) (sq pival)) (dv (lit (131/125)) (logExpr p))
def twoExpr (p : WinnerHeightProfiles.Row) : Expr := add (add (dv (mul (mul pival mzero) (lit (31/50))) (logExpr p))
  (dv (mul (lit 6) mzero) (mul pival (anchorExpr p))))
  (dv (mul (mul pival mzero) (lit (131/125))) (mul (anchorExpr p) (logExpr p)))
def zeroExpr (p : WinnerHeightProfiles.Row) : Expr := dv (lit (281/100))
  (mul (mul (lit (611/1000)) (rootExpr p)) (logExpr p))
def residualExpr (p : WinnerHeightProfiles.Row) : Expr := .inv
  (mul (mul (mul (lit (611/1000)) (rootExpr p)) (logExpr p)) (rt (logExpr p)))
def fiveExpr (p : WinnerHeightProfiles.Row) : Expr :=
  mul (mul (dv (mul (mul pival mzero) (lit (529/1000))) (lit (2*(3599/10000))))
    (sq (add (lit 1) (dv (lit (2*(3599/10000))) (logExpr p)))))
    (.exp (dv (lit (2*(3599/10000)*(289/500))) (logExpr p)))
def sixExpr (p : WinnerHeightProfiles.Row) : Expr :=
  add (mul (dv (lit (529/1000)) (mul (lit (5*(3599/10000))) (.exp (lit (3599/10000)))))
    (sq (add (lit 1) (dv (lit (3599/10000)) (logExpr p)))))
    (dv (mul (lit (121/200)) (.exp (lit (-2*(3599/10000))))) (sq (logExpr p)))
def vExpr (p : WinnerHeightProfiles.Row) : Expr :=
  let sig2 := add (lit 1) (dv (lit (3599/10000)) (logExpr p))
  let omega := .exp (mul (lit (2*(601/5000))) (sq (dv sig2 (anchorExpr p))))
  mul (mul (lit (8*(601/5000))) omega)
    (add (dv (add (fiveExpr p) (dv (mul (mul (sixExpr p) pival) mzero) (anchorExpr p))) (lit (4*(601/5000))))
      (dv (mul (sixExpr p) (rt pival)) (mul (lit (8*(601/5000))) (rt (lit (2*(601/5000)))))))
def phiExpr (p : WinnerHeightProfiles.Row) : Expr := add (lit (4/3))
  (mul (lit ((p).U/(p).V)) (.exp (lit (-8*(3599/10000)/3-1))))
def kExpr (p : WinnerHeightProfiles.Row) : Expr :=
  let exponent := add (add (lit (2*(601/5000)))
    (add (mul (lit (1/4)) (.log (lit (p).U))) (mul (lit (3/4)) (.log (lit (p).V)))))
    (mul (lit (2*(3681/10000)+2*(3599/10000)*(3/4))) (phiExpr p))
  dv (mul smoothingR (.exp exponent)) (mul (mul (lit 2) pival) (lit (3681/10000)))
def bExpr (p : WinnerHeightProfiles.Row) : Expr := add (mul (lit 2) (.log (lit ((p).V/(p).U))))
  (mul (lit (4*(3599/10000))) (phiExpr p))

 theorem anchor_pos (p : WinnerHeightProfiles.Row) : 0<anchor p := by
  unfold anchor
  exact mul_pos (by norm_num [height]) (exp_pos _)

 theorem anchor_gt_one (p : WinnerHeightProfiles.Row) (hshift : 0≤(p.shift:ℝ)) : 1<anchor p := by
  have he := one_le_exp hshift
  unfold anchor
  nlinarith [show (1:ℝ)<height by norm_num [height]]

 theorem height_le_anchor (p : WinnerHeightProfiles.Row) (hshift : 0≤(p.shift:ℝ)) : height≤anchor p := by
  have he := one_le_exp hshift
  unfold anchor
  nlinarith [show (0:ℝ)<height by norm_num [height]]

 theorem omega_upper (p : WinnerHeightProfiles.Row) (hshift : 0≤(p.shift:ℝ)) :
    exp ((601/5000:ℝ)/(2*(anchor p)^2))≤1000000000001/1000000000000 := by
  exact (WinnerBetaA.Minkowski.omega_bound (by norm_num [height]) (height_le_anchor p hshift)).trans source_omega_upper

 theorem anchor_semantics (p : WinnerHeightProfiles.Row) : value (anchorExpr p)=anchor p := by simp [anchorExpr,anchor,h0,height]
 theorem log_semantics (p : WinnerHeightProfiles.Row) : value (logExpr p)=log (anchor p) := by simp [logExpr,anchor_semantics]
 theorem root_semantics (p : WinnerHeightProfiles.Row) : value (rootExpr p)=anchor p^((1:ℝ)/6) := by
  simp only [rootExpr,value_exp,value_div,value_lit,log_semantics]
  rw [rpow_def_of_pos (anchor_pos p)]
  congr 1
  ring
 theorem one_semantics (p : WinnerHeightProfiles.Row) : value (oneExpr p)=meanOne (anchor p) := by simp [oneExpr,meanOne,log_semantics]
 theorem two_semantics (p : WinnerHeightProfiles.Row) : value (twoExpr p)=meanTwo (anchor p) := by
  simp [twoExpr,meanTwo,log_semantics,anchor_semantics,mzero_semantics]
 theorem zero_semantics (p : WinnerHeightProfiles.Row) : value (zeroExpr p)=
    (281/100)/((611/1000)*anchor p^((1:ℝ)/6)*log (anchor p)) := by
  simp [zeroExpr,root_semantics,log_semantics]
 theorem residual_semantics (p : WinnerHeightProfiles.Row) (hshift : 0≤(p.shift:ℝ)) : value (residualExpr p)=
    1/((611/1000)*anchor p^((1:ℝ)/6)*log (anchor p)*sqrt (log (anchor p))) := by
  simp only [residualExpr,value_inv,value_mul,value_lit,root_semantics,log_semantics]
  rw [value_rt _ (by rw [log_semantics];exact log_pos (anchor_gt_one p hshift))]
  rw [log_semantics]
  simp [one_div]
 theorem five_semantics (p : WinnerHeightProfiles.Row) : value (fiveExpr p)=rightFive (289/500) (3599/10000) (anchor p) := by
  simp [fiveExpr,rightFive,log_semantics,mzero_semantics]
 theorem six_semantics (p : WinnerHeightProfiles.Row) : value (sixExpr p)=rightSix (3599/10000) (anchor p) := by
  simp [sixExpr,rightSix,log_semantics]
 theorem v_semantics (p : WinnerHeightProfiles.Row) : value (vExpr p)=WinnerBetaA.HeightSource.rightV (289/500) (3599/10000) (anchor p) := by
  simp only [vExpr,value_mul,value_exp,value_sq,value_div,value_add,value_lit,value_pi,
    five_semantics,six_semantics,anchor_semantics,log_semantics,mzero_semantics]
  rw [value_rt _ (by simp;exact Real.pi_pos),value_rt _ (by norm_num)]
  norm_num [WinnerBetaA.HeightSource.rightV,value_pi]

 theorem phi_semantics (p : WinnerHeightProfiles.Row) : value (phiExpr p)=interpolationPhi (3599/10000) (p).U (p).V := by
  simp [phiExpr,interpolationPhi]
 theorem k_semantics (p : WinnerHeightProfiles.Row) (hU : (0:ℝ)<p.U) (hV : (0:ℝ)<p.V) : value (kExpr p)=densityCoefficient (7/8) (3681/10000) (3599/10000)
    (601/5000) (p).U (p).V sourceSmoothingR := by
  simp only [kExpr,value_div,value_mul,value_exp,value_add,value_lit,value_log,value_pi,
    smoothingR_semantics,phi_semantics]
  unfold densityCoefficient interpolationCoefficient
  norm_num only [show (2:ℝ)*(1-7/8)=1/4 by norm_num,show (2:ℝ)*(7/8)-1=3/4 by norm_num]
  rw [rpow_def_of_pos hU,rpow_def_of_pos hV]
  rw [show log ((p).U:ℝ)*(1/4)=1/4*log ((p).U:ℝ) by ring,
    show log ((p).V:ℝ)*(3/4)=3/4*log ((p).V:ℝ) by ring]
  norm_num only
  simp only [exp_add]
  ring
 theorem b_semantics (p : WinnerHeightProfiles.Row) : value (bExpr p)=
    2*log ((p).V/(p).U:ℝ)+4*(3599/10000)*interpolationPhi (3599/10000) (p).U (p).V := by
  simp [bExpr,phi_semantics]


#print axioms one_semantics
#print axioms v_semantics
#print axioms k_semantics
end PVEvolutionA.Recovery.Profile
