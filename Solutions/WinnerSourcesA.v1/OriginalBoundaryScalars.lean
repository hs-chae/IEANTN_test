/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalZeta
namespace WinnerOriginalScalars
open Real LeanCert.Core
set_option maxHeartbeats 0

noncomputable def sourceBSix (X q gamma : ℝ) : ℝ :=
  (1+q)*log X/(q*exp (q*log X))*
    (1+1/(q*log X)+gamma/log X+7*q/(12*(1+q)*X*log X))

 theorem bSix_semantics (x q : Expr) : value (bSix x q)=sourceBSix (value x) (value q) 1 := by
  simp [bSix,sourceBSix]

def etaB6 : Expr := bSix (lit 1000000000) eta
def muB6 : Expr := bSix h0 (sub mu (lit 1))

theorem eta_bsix_upper : sourceBSix 1000000000 (507/2000) 1≤3/4 := by
  have h := closed_upper etaB6 (3/4) (by native_decide)
  simpa [etaB6,bSix_semantics,eta] using h

theorem mu_bsix_upper : sourceBSix height (237/1000) 1≤1/4 := by
  have h := closed_upper muB6 (1/4) (by native_decide)
  norm_num [muB6,bSix_semantics,mu,height] at h ⊢
  exact h

def cEightSimple : Expr :=
  mul (dv (mul (lit 2) (sq h)) (.exp (mul (sub (mul (lit 2) mu) (lit 2)) h)))
    (add (dv (mul (mul (lit 4) mu) (bEleven (mul (lit 2) mu))) (sub (mul (lit 2) mu) (lit 1)))
      (dv (mul (mul (mul (lit 2) pival) mzero)
        (mul (sub (mul (lit 2) mu) (lit 1)) (bEleven (sub (mul (lit 2) mu) (lit 1)))))
        (sub mu (lit 1))))

theorem ceight_simple_upper : value cEightSimple≤1 := by
  have h := closed_upper cEightSimple 1 (by native_decide)
  norm_num at h ⊢
  exact h

noncomputable def boundaryEta : ℝ := 507/2000
noncomputable def boundaryMu : ℝ := 1237/1000
noncomputable def sourceBFive : ℝ :=
  positiveZeta (1+boundaryEta)^4/positiveZeta (2+2*boundaryEta)^2+
  2*positiveZeta (1+boundaryEta)^2/positiveZeta (2+2*boundaryEta)
noncomputable def sourceBSeven : ℝ :=
  (1+2/((1503/500)*positiveZeta (1+boundaryEta)*height^(1+boundaryEta)))*
    ((1503/500)*positiveZeta (1+boundaryEta))^2
noncomputable def sourceBEight : ℝ :=
  sqrt ((2+boundaryEta)^2/(height-1)^2+((1+2*boundaryEta)/(height-1)+1)^2)
noncomputable def sourceBNine (gamma : ℝ) : ℝ :=
  Real.pi/log 2*(log sourceBSeven+log sourceBFive-
    2*log (1-sourceBSix 1000000000 boundaryEta gamma^2))+Real.pi+
    2*(1+2*boundaryEta)/log 2*log (sourceBEight/(2*Real.pi))
noncomputable def sourceCSeven (gamma : ℝ) : ℝ :=
  (2*(1+2*boundaryEta)+2*Real.pi*(1+boundaryEta))/log 2+sourceBNine gamma/log height
noncomputable def coarseCSeven : ℝ :=
  (2*(1+2*boundaryEta)+2*Real.pi*(1+boundaryEta))/log 2+
  (Real.pi/log 2*(log 227+log 675-2*log (1-sourceBSix 1000000000 boundaryEta 1^2))+Real.pi)/log height

 theorem coarse_cseven_semantics : value cSeven=coarseCSeven := by
  simp [cSeven,coarseCSeven,bSix_semantics,boundaryEta,eta,log_semantics]

 theorem coarse_cseven_upper : coarseCSeven≤20 := by
  rw [←coarse_cseven_semantics]
  exact cSeven_upper

 theorem bsix_gamma_le {X q gamma : ℝ} (hX : 1<X) (hq : 0<q) (hg : gamma≤1) :
    sourceBSix X q gamma≤sourceBSix X q 1 := by
  have hlog := log_pos hX
  unfold sourceBSix
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  gcongr

 theorem bsix_pos {X q gamma : ℝ} (hX : 1<X) (hq : 0<q) (hg : 0≤gamma) :
    0<sourceBSix X q gamma := by
  have hlog := log_pos hX
  unfold sourceBSix
  positivity

 theorem bfive_upper : sourceBFive≤675 := by
  have hz0 : 0≤positiveZeta (1+boundaryEta) := by
    have h:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta]);linarith
  have hz : positiveZeta (1+boundaryEta)≤5 := by simpa [boundaryEta] using zeta_eta_upper
  have hz2 : 1≤positiveZeta (2+2*boundaryEta) := by simpa [boundaryEta] using zeta_two_eta_lower
  have h1 : positiveZeta (1+boundaryEta)^4/positiveZeta (2+2*boundaryEta)^2≤(5:ℝ)^4/1^2 := by
    gcongr
  have h2 : 2*positiveZeta (1+boundaryEta)^2/positiveZeta (2+2*boundaryEta)≤(2:ℝ)*5^2/1 := by
    gcongr
  unfold sourceBFive
  norm_num at h1 h2
  linarith

 theorem bfive_pos : 0<sourceBFive := by
  have h1:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta])
  have h2:=positiveZeta_lower (s:=2+2*boundaryEta) (by norm_num [boundaryEta])
  unfold sourceBFive
  positivity

 theorem bseven_upper : sourceBSeven≤227 := by
  have hz : positiveZeta (1+boundaryEta)≤5 := by simpa [boundaryEta] using zeta_eta_upper
  have hzp:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta])
  have hHp : 0<height := by norm_num [height]
  have hpow : height≤height^(1+boundaryEta) := by
    nth_rw 1 [←rpow_one height]
    apply rpow_le_rpow_of_exponent_le (by norm_num [height])
    norm_num [boundaryEta]
  have hpp : 0<height^(1+boundaryEta) := by positivity [show (0:ℝ)<height by norm_num [height]]
  have he : sourceBSeven=((1503/500)*positiveZeta (1+boundaryEta))^2+
      2*((1503/500)*positiveZeta (1+boundaryEta))/height^(1+boundaryEta) := by
    unfold sourceBSeven
    field_simp
    <;> ring
  rw [he]
  have hm : 2*((1503/500)*positiveZeta (1+boundaryEta))/height^(1+boundaryEta)≤
      2*((1503/500:ℝ)*5)/height := by gcongr
  have hs : ((1503/500)*positiveZeta (1+boundaryEta))^2≤((1503/500:ℝ)*5)^2 := by gcongr
  norm_num [height] at hm
  norm_num at hs
  norm_num [height]
  linarith

 theorem bseven_pos : 0<sourceBSeven := by
  have hz:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta])
  have hp : 0<height := by norm_num [height]
  unfold sourceBSeven
  positivity

 theorem beight_upper : sourceBEight≤2 := by
  unfold sourceBEight
  apply (sqrt_le_iff).mpr
  norm_num [boundaryEta,height]

 theorem cseven_source_le_coarse {gamma : ℝ} (hg0 : 0≤gamma) (hg1 : gamma≤1) :
    sourceCSeven gamma≤coarseCSeven := by
  have hH : 0<log height := by linarith [source_log_lower]
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have he0 : 0<boundaryEta := by norm_num [boundaryEta]
  have hb0 := bsix_pos (X:=1000000000) (q:=boundaryEta) (by norm_num) he0 hg0
  have hbc0 := bsix_pos (X:=1000000000) (q:=boundaryEta) (gamma:=1) (by norm_num) he0 (by norm_num)
  have hbg := bsix_gamma_le (X:=1000000000) (q:=boundaryEta) (by norm_num) he0 hg1
  have hbc : sourceBSix 1000000000 boundaryEta 1≤3/4 := by simpa [boundaryEta] using eta_bsix_upper
  have hr : (sourceBSix 1000000000 boundaryEta gamma)^2≤(sourceBSix 1000000000 boundaryEta 1)^2 := by nlinarith
  have hp : 0<1-(sourceBSix 1000000000 boundaryEta 1)^2 := by nlinarith
  have hlog := log_le_log hp (by linarith :
    1-(sourceBSix 1000000000 boundaryEta 1)^2≤1-(sourceBSix 1000000000 boundaryEta gamma)^2)
  have h5 : log sourceBFive≤log 675 := log_le_log bfive_pos bfive_upper
  have h7 : log sourceBSeven≤log 227 := log_le_log bseven_pos bseven_upper
  have h8pos : 0<sourceBEight := by
    unfold sourceBEight
    apply sqrt_pos.mpr
    norm_num [height,boundaryEta]
  have h8ratio : sourceBEight/(2*Real.pi)≤1 := by
    apply (div_le_iff₀ (by positivity : 0<2*Real.pi)).mpr
    nlinarith [beight_upper,Real.pi_gt_three]
  have h8log : log (sourceBEight/(2*Real.pi))≤0 :=
    log_nonpos (by positivity) h8ratio
  have hneg : 2*(1+2*boundaryEta)/log 2*log (sourceBEight/(2*Real.pi))≤0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h8log
  have h9 : sourceBNine gamma≤
      Real.pi/log 2*(log 227+log 675-2*log (1-sourceBSix 1000000000 boundaryEta 1^2))+Real.pi := by
    unfold sourceBNine
    have hinner : log sourceBSeven+log sourceBFive-2*log (1-sourceBSix 1000000000 boundaryEta gamma^2)≤
        log 227+log 675-2*log (1-sourceBSix 1000000000 boundaryEta 1^2) := by linarith
    have hh := mul_le_mul_of_nonneg_left hinner (by positivity : 0≤Real.pi/log 2)
    linarith
  unfold sourceCSeven coarseCSeven
  gcongr

 theorem source_cseven_upper : sourceCSeven eulerMascheroniConstant≤20 := by
  have hg0 : 0≤eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  exact (cseven_source_le_coarse hg0 euler_gamma_le_one).trans coarse_cseven_upper

noncomputable def sourceBEleven (tau : ℝ) : ℝ :=
  1+3/((tau-1)*log height)+6/((tau-1)*log height)^2+6/((tau-1)*log height)^3
noncomputable def sourceCEightBase : ℝ :=
  (log height)^2/exp ((2*boundaryMu-2)*log height)*
    (4*boundaryMu*sourceBEleven (2*boundaryMu)/(2*boundaryMu-1)+
     2*Real.pi*sourceM0*(2*boundaryMu-1)*sourceBEleven (2*boundaryMu-1)/(boundaryMu-1))
noncomputable def sourceBTen (gamma : ℝ) : ℝ :=
  -log (1-(sourceBSix height (boundaryMu-1) gamma)^2)/(sourceBSix height (boundaryMu-1) gamma)^2
noncomputable def sourceCEight (gamma : ℝ) : ℝ := sourceBTen gamma*sourceCEightBase

 theorem bEleven_semantics (tau : Expr) : value (bEleven tau)=sourceBEleven (value tau) := by
  simp [bEleven,sourceBEleven,log_semantics]
  ring

 theorem ceight_simple_semantics : value cEightSimple=2*sourceCEightBase := by
  simp [cEightSimple,sourceCEightBase,bEleven_semantics,boundaryMu,mu,
    mzero_semantics,log_semantics]
  ring

 theorem ceight_base_nonneg : 0≤sourceCEightBase := by
  have hh : 0<log height := by linarith [source_log_lower]
  have hm:=source_mzero_pos
  unfold sourceCEightBase sourceBEleven boundaryMu
  positivity

 theorem bten_le_two {gamma : ℝ} (hg0 : 0≤gamma) (hg1 : gamma≤1) : sourceBTen gamma≤2 := by
  have hH : 1<height := by norm_num [height]
  have hq : 0<boundaryMu-1 := by norm_num [boundaryMu]
  have hb0 := bsix_pos hH hq hg0
  have hbc := bsix_gamma_le hH hq hg1
  have hupper : sourceBSix height (boundaryMu-1) 1≤1/4 := by
    norm_num [boundaryMu] at hbc ⊢
    exact mu_bsix_upper
  have hb : sourceBSix height (boundaryMu-1) gamma≤1/4 := hbc.trans hupper
  let r := (sourceBSix height (boundaryMu-1) gamma)^2
  have hr : 0<r := sq_pos_of_pos hb0
  have hr' : r≤1/16 := by dsimp [r];nlinarith
  have hu : 0<1-r := by linarith
  have hl : -log (1-r)≤1/(1-r)-1 := by
    have h := log_le_sub_one_of_pos (inv_pos.mpr hu)
    simpa only [log_inv,one_div] using h
  have hf : 1/(1-r)-1≤2*r := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hu).mpr
    nlinarith
  unfold sourceBTen
  change -log (1-r)/r≤2
  apply (div_le_iff₀ hr).mpr
  linarith

 theorem source_ceight_upper : sourceCEight eulerMascheroniConstant≤1 := by
  have hg0 : 0≤eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  have h := mul_le_mul_of_nonneg_right (bten_le_two hg0 euler_gamma_le_one) ceight_base_nonneg
  have hfinite : 2*sourceCEightBase≤1 := by rw [←ceight_simple_semantics];exact ceight_simple_upper
  exact h.trans hfinite

 theorem source_log_height_uniform {T : ℝ} (hT : height≤T) : 28≤log T := by
  exact source_log_lower.trans (log_le_log (by norm_num [height]) hT)

#print axioms source_cseven_upper
#print axioms source_ceight_upper

#print axioms bfive_upper
#print axioms bseven_upper
#print axioms coarse_cseven_upper
end WinnerOriginalScalars
