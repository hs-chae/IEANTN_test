/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OriginalSharpScalars
import EulerGammaBound
import WinnerBetaA.HeightSource
import SourceDensityPoly
namespace WinnerHeightProfiles
open Real LeanCert.Core WinnerOriginalScalars WinnerBetaA.HeightSource WinnerDensitySource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
structure Row where
  shift : ℚ
  h : ℚ
  m1 : ℚ
  m2 : ℚ
  r0 : ℚ
  r1 : ℚ
  U : ℚ
  V : ℚ
  K : ℚ

def row (j : Fin 4) : Row := match j.val with
  | 0 => ⟨0,28729633/1000000,322203/500000,89181/1000000,8331/6250000,8851/100000000,12747/10000,72369/10000,72931/10000⟩
  | 1 => ⟨1,29729633/1000000,643179/1000000,43091/500000,109037/100000000,7117/100000000,3167/2500,4514/625,36349/5000⟩
  | 2 => ⟨2,30729633/1000000,642031/1000000,83377/1000000,17859/20000000,5733/100000000,2519/2000,72089/10000,72483/10000⟩
  | _ => ⟨4,32729633/1000000,159987/250000,39141/500000,60073/100000000,3737/100000000,12463/10000,71843/10000,72091/10000⟩

noncomputable def anchor (j : Fin 4) : ℝ := height*exp ((row j).shift)
def anchorExpr (j : Fin 4) : Expr := mul h0 (.exp (lit (row j).shift))
def logExpr (j : Fin 4) : Expr := .log (anchorExpr j)
def rootExpr (j : Fin 4) : Expr := .exp (dv (logExpr j) (lit 6))
def oneExpr (j : Fin 4) : Expr := add (dv (lit 6) (sq pival)) (dv (lit (131/125)) (logExpr j))
def twoExpr (j : Fin 4) : Expr := add (add (dv (mul (mul pival mzero) (lit (31/50))) (logExpr j))
  (dv (mul (lit 6) mzero) (mul pival (anchorExpr j))))
  (dv (mul (mul pival mzero) (lit (131/125))) (mul (anchorExpr j) (logExpr j)))
def zeroExpr (j : Fin 4) : Expr := dv (lit (281/100))
  (mul (mul (lit (611/1000)) (rootExpr j)) (logExpr j))
def residualExpr (j : Fin 4) : Expr := .inv
  (mul (mul (mul (lit (611/1000)) (rootExpr j)) (logExpr j)) (rt (logExpr j)))
def fiveExpr (j : Fin 4) : Expr :=
  mul (mul (dv (mul (mul pival mzero) (lit (529/1000))) (lit (2*(3599/10000))))
    (sq (add (lit 1) (dv (lit (2*(3599/10000))) (logExpr j)))))
    (.exp (dv (lit (2*(3599/10000)*(289/500))) (logExpr j)))
def sixExpr (j : Fin 4) : Expr :=
  add (mul (dv (lit (529/1000)) (mul (lit (5*(3599/10000))) (.exp (lit (3599/10000)))))
    (sq (add (lit 1) (dv (lit (3599/10000)) (logExpr j)))))
    (dv (mul (lit (121/200)) (.exp (lit (-2*(3599/10000))))) (sq (logExpr j)))
def vExpr (j : Fin 4) : Expr :=
  let sig2 := add (lit 1) (dv (lit (3599/10000)) (logExpr j))
  let omega := .exp (mul (lit (2*(601/5000))) (sq (dv sig2 (anchorExpr j))))
  mul (mul (lit (8*(601/5000))) omega)
    (add (dv (add (fiveExpr j) (dv (mul (mul (sixExpr j) pival) mzero) (anchorExpr j))) (lit (4*(601/5000))))
      (dv (mul (sixExpr j) (rt pival)) (mul (lit (8*(601/5000))) (rt (lit (2*(601/5000)))))))
def phiExpr (j : Fin 4) : Expr := add (lit (4/3))
  (mul (lit ((row j).U/(row j).V)) (.exp (lit (-8*(3599/10000)/3-1))))
def kExpr (j : Fin 4) : Expr :=
  let exponent := add (add (lit (2*(601/5000)))
    (add (mul (lit (1/4)) (.log (lit (row j).U))) (mul (lit (3/4)) (.log (lit (row j).V)))))
    (mul (lit (2*(3681/10000)+2*(3599/10000)*(3/4))) (phiExpr j))
  dv (mul smoothingR (.exp exponent)) (mul (mul (lit 2) pival) (lit (3681/10000)))
def bExpr (j : Fin 4) : Expr := add (mul (lit 2) (.log (lit ((row j).V/(row j).U))))
  (mul (lit (4*(3599/10000))) (phiExpr j))

 theorem anchor_gt_one (j : Fin 4) : 1<anchor j := by
  have hp : 0≤((row j).shift:ℝ) := by fin_cases j <;> norm_num [row]
  have he := one_le_exp hp
  unfold anchor
  have hH : (1:ℝ)<height := by norm_num [height]
  nlinarith

 theorem height_le_anchor (j : Fin 4) : height ≤ anchor j := by
  have hp : 0 ≤ ((row j).shift:ℝ) := by fin_cases j <;> norm_num [row]
  have he := one_le_exp hp
  unfold anchor
  nlinarith [show (0:ℝ)<height by norm_num [height]]

 theorem omega_upper (j : Fin 4) : exp ((601/5000:ℝ)/(2*(anchor j)^2)) ≤
    1000000000001/1000000000000 := by
  have he := WinnerBetaA.Minkowski.omega_bound (by norm_num [height] : (1:ℝ)<height) (height_le_anchor j)
  exact he.trans source_omega_upper

 theorem anchor_semantics (j : Fin 4) : value (anchorExpr j)=anchor j := by simp [anchorExpr,anchor,h0,height]
 theorem log_semantics (j : Fin 4) : value (logExpr j)=log (anchor j) := by simp [logExpr,anchor_semantics]
 theorem root_semantics (j : Fin 4) : value (rootExpr j)=anchor j^((1:ℝ)/6) := by
  simp only [rootExpr,value_exp,value_div,value_lit,log_semantics]
  rw [rpow_def_of_pos (by linarith [anchor_gt_one j])]
  congr 1
  ring
 theorem one_semantics (j : Fin 4) : value (oneExpr j)=meanOne (anchor j) := by simp [oneExpr,meanOne,log_semantics]
 theorem two_semantics (j : Fin 4) : value (twoExpr j)=meanTwo (anchor j) := by
  simp [twoExpr,meanTwo,log_semantics,anchor_semantics,mzero_semantics]
 theorem zero_semantics (j : Fin 4) : value (zeroExpr j)=
    (281/100)/((611/1000)*anchor j^((1:ℝ)/6)*log (anchor j)) := by
  simp [zeroExpr,root_semantics,log_semantics]
 theorem residual_semantics (j : Fin 4) : value (residualExpr j)=
    1/((611/1000)*anchor j^((1:ℝ)/6)*log (anchor j)*sqrt (log (anchor j))) := by
  simp only [residualExpr,value_inv,value_mul,value_lit,root_semantics,log_semantics]
  rw [value_rt _ (by rw [log_semantics];exact log_pos (anchor_gt_one j))]
  rw [log_semantics]
  simp [one_div]
 theorem five_semantics (j : Fin 4) : value (fiveExpr j)=rightFive (289/500) (3599/10000) (anchor j) := by
  simp [fiveExpr,rightFive,log_semantics,mzero_semantics]
 theorem six_semantics (j : Fin 4) : value (sixExpr j)=rightSix (3599/10000) (anchor j) := by
  simp [sixExpr,rightSix,log_semantics]
 theorem v_semantics (j : Fin 4) : value (vExpr j)=WinnerBetaA.HeightSource.rightV (289/500) (3599/10000) (anchor j) := by
  simp only [vExpr,value_mul,value_exp,value_sq,value_div,value_add,value_lit,value_pi,
    five_semantics,six_semantics,anchor_semantics,log_semantics,mzero_semantics]
  rw [value_rt _ (by simp;exact Real.pi_pos),value_rt _ (by norm_num)]
  norm_num [WinnerBetaA.HeightSource.rightV,value_pi]

 theorem phi_semantics (j : Fin 4) : value (phiExpr j)=interpolationPhi (3599/10000) (row j).U (row j).V := by
  simp [phiExpr,interpolationPhi]
 theorem row_U_pos (j : Fin 4) : (0:ℝ)<(row j).U := by fin_cases j <;> norm_num [row]
 theorem row_V_pos (j : Fin 4) : (0:ℝ)<(row j).V := by fin_cases j <;> norm_num [row]
 theorem k_semantics (j : Fin 4) : value (kExpr j)=densityCoefficient (7/8) (3681/10000) (3599/10000)
    (601/5000) (row j).U (row j).V sourceSmoothingR := by
  simp only [kExpr,value_div,value_mul,value_exp,value_add,value_lit,value_log,value_pi,
    smoothingR_semantics,phi_semantics]
  unfold densityCoefficient interpolationCoefficient
  norm_num only [show (2:ℝ)*(1-7/8)=1/4 by norm_num,show (2:ℝ)*(7/8)-1=3/4 by norm_num]
  rw [rpow_def_of_pos (row_U_pos j),rpow_def_of_pos (row_V_pos j)]
  rw [show log ((row j).U:ℝ)*(1/4)=1/4*log ((row j).U:ℝ) by ring,
    show log ((row j).V:ℝ)*(3/4)=3/4*log ((row j).V:ℝ) by ring]
  norm_num only
  simp only [exp_add]
  ring
 theorem b_semantics (j : Fin 4) : value (bExpr j)=
    2*log ((row j).V/(row j).U:ℝ)+4*(3599/10000)*interpolationPhi (3599/10000) (row j).U (row j).V := by
  simp [bExpr,phi_semantics]

 theorem log_lower (j : Fin 4) : ((row j).h:ℝ)≤log (anchor j) := by
  rw [←log_semantics]
  fin_cases j <;> exact closed_lower _ _ (by native_decide)
 theorem mean_one_upper (j : Fin 4) : meanOne (anchor j)≤(row j).m1 := by
  rw [←one_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem mean_two_upper (j : Fin 4) : meanTwo (anchor j)≤(row j).m2 := by
  rw [←two_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem ratio_zero_upper (j : Fin 4) :
    (281/100)/((611/1000)*anchor j^((1:ℝ)/6)*log (anchor j))≤(row j).r0 := by
  rw [←zero_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem ratio_one_upper (j : Fin 4) :
    1/((611/1000)*anchor j^((1:ℝ)/6)*log (anchor j)*sqrt (log (anchor j)))≤(row j).r1 := by
  rw [←residual_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem right_v_upper (j : Fin 4) : WinnerBetaA.HeightSource.rightV (289/500) (3599/10000) (anchor j)≤(row j).V := by
  rw [←v_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem coefficient_upper (j : Fin 4) : densityCoefficient (7/8) (3681/10000) (3599/10000)
    (601/5000) (row j).U (row j).V sourceSmoothingR≤(row j).K := by
  rw [←k_semantics]
  fin_cases j <;> exact closed_upper _ _ (by native_decide)
 theorem slope_lower (j : Fin 4) : (54281/10000:ℝ)≤
    2*log ((row j).V/(row j).U:ℝ)+4*(3599/10000)*interpolationPhi (3599/10000) (row j).U (row j).V := by
  rw [←b_semantics]
  have hn : ((54281/10000:ℚ):ℝ) ≤ value (bExpr j) := by
    fin_cases j <;> exact closed_lower _ _ (by native_decide)
  norm_num at hn ⊢
  exact hn
#print axioms coefficient_upper
#print axioms slope_lower
end WinnerHeightProfiles
