/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.BaselineTransfer
import IEANTN.Vocabulary.ErrorTerms
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace FKSComputationLed.StrongBaseline
open Real Finset MeasureTheory intervalIntegral LeanCert.Core CellProgram PointProgram RealBounds

lemma log_hundred : (4:ℝ)≤log 100 := by
  have h3 : (1:ℝ)<log 3 := (lt_log_iff_exp_lt (by norm_num)).mpr exp_one_lt_three
  have hh := log_le_log (by norm_num : (0:ℝ)<81) (by norm_num : (81:ℝ)≤100)
  rw [show (81:ℝ)=3^4 by norm_num,log_pow] at hh
  norm_num at hh
  linarith
lemma log_billion {x : ℝ} (hx : 0<x) (hxU : x≤1000000000) : log x≤21 := by
  have h27 : (27/10:ℝ)<exp 1 := by linarith [exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ h27 (by norm_num : (0:ℝ)≤27/10) (by norm_num : (21:Nat)≠0)
  have he : (1000000000:ℝ)<exp 21 := by
    have heq : exp (21:ℝ)=(exp 1)^21 := by rw [show (21:ℝ)=(21:Nat)*(1:ℝ) by norm_num,exp_nat_mul]
    rw [heq]
    exact (show (1000000000:ℝ)<(27/10:ℝ)^21 by norm_num).trans hp
  exact (log_le_iff_le_exp hx).mpr (hxU.trans he.le)

theorem hundred_checked : (pointInfo 100).valid=true ∧
    (pointInfo 100).liI.lowerBoundedBy 28=true := by native_decide
lemma Li_hundred : (28:ℝ)≤LiTaylor.Li2 100 := by
  have hm := (PointSound.pointInfo_sound 100 hundred_checked.1).2.2.2.1
  exact_mod_cast (IntervalDyadic.lowerBoundedBy_spec hundred_checked.2).trans
    (IntervalDyadic.lo_le_of_mem hm)
lemma psi_hundred : (92:ℝ)≤Chebyshev.psi 100 := by
  have hn : Nat.lcmUpto 100=69720375229712477164533808935312303556800 := by decide +kernel
  rw [show (100:ℝ)=(100:Nat) by norm_num,Chebyshev.psi_eq_log_lcmUpto,hn]
  have he : exp (92:ℝ) < (69720375229712477164533808935312303556800:ℝ) := by
    have h11 : exp 1<(11/4:ℝ) := by linarith [exp_one_lt_d9]
    calc
      _ = (exp 1)^92 := by rw [show (92:ℝ)=(92:Nat)*(1:ℝ) by norm_num,exp_nat_mul]
      _ < (11/4:ℝ)^92 := pow_lt_pow_left₀ h11 (exp_pos _).le (by norm_num)
      _ < _ := by norm_num
  exact (le_log_iff_exp_le (by norm_num)).mpr he.le

lemma high_hundred (k : Nat) (hk : 6≤k) :
    IEANTN.primeCounting ((100:ℝ)^((1:ℝ)/(k+1:Nat)))/(k+1:Nat)=0 := by
  have hlog : log (100:ℝ)<7*log 2 := by
    have hh := log_lt_log (by norm_num : (0:ℝ)<100) (by norm_num : (100:ℝ)<2^7)
    simpa only [log_pow,Nat.cast_ofNat] using hh
  have hk1 : (7:ℝ)≤((k+1:Nat):ℝ) := by exact_mod_cast (by omega : 7≤k+1)
  have hk0 : (0:ℝ)<((k+1:Nat):ℝ) := by positivity
  have hl2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hr : (100:ℝ)^((1:ℝ)/(k+1:Nat))<2 := by
    rw [rpow_def_of_pos (by norm_num : (0:ℝ)<100),←exp_log (by norm_num : (0:ℝ)<2)]
    apply exp_lt_exp.mpr
    have hd : log (100:ℝ)/((k+1:Nat):ℝ)<log 2 := (div_lt_iff₀ hk0).mpr (by nlinarith)
    simpa only [div_eq_mul_inv,one_mul] using hd
  rw [BaselineTransfer.primeCounting_zero_lt_two (rpow_nonneg (by norm_num) _) hr]
  simp

lemma pi_star_hundred : IEANTN.riemannPrimeCounting 100≤(31:ℝ) := by
  unfold IEANTN.riemannPrimeCounting
  rw [tsum_eq_sum (s:=range 6) (fun k hk=>by
    simpa only [Nat.cast_add,Nat.cast_one] using high_hundred k (by simpa using hk))]
  rw [sum_range_succ']
  have hfirst : IEANTN.primeCounting (100:ℝ)=25 := by
    have h : Nat.primeCounting 100=25 := by decide +kernel
    simpa [IEANTN.primeCounting] using congrArg (fun n:Nat=>(n:ℝ)) h
  simp only [Nat.cast_zero,zero_add,div_one,rpow_one,hfirst]
  have hbound : ∀ k:Nat, IEANTN.primeCounting ((100:ℝ)^(1/(k+1+1:ℝ)))≤4 := by
    intro k
    have he : (1:ℝ)/(k+1+1:ℝ)≤1/2 := by
      apply div_le_div_of_nonneg_left zero_le_one (by norm_num)
      have hk0 : (0:ℝ)≤(k:ℝ) := Nat.cast_nonneg _
      linarith
    have hr := rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤100) he
    have hroot : (100:ℝ)^(1/(k+1+1:ℝ))≤10 := by
      simpa only [←sqrt_eq_rpow,show sqrt (100:ℝ)=10 by norm_num] using hr
    have hp := pi_mono hroot
    have hp10 : IEANTN.primeCounting (10:ℝ)=4 := by
      have h : Nat.primeCounting 10=4 := by decide +kernel
      simpa [IEANTN.primeCounting] using congrArg (fun n:Nat=>(n:ℝ)) h
    rwa [hp10] at hp
  have hh := sum_le_sum (s:=range 5) (fun k hk=>
    div_le_div_of_nonneg_right (hbound k) (by positivity : (0:ℝ)≤(k+1:ℝ)+1))
  norm_num [Finset.sum_range_succ] at hh ⊢
  linarith

noncomputable def anchor : ℝ := LiTaylor.Li2 100-IEANTN.riemannPrimeCounting 100-
  (100-Chebyshev.psi 100)/log 100
theorem anchor_lower : (-5:ℝ)≤anchor := by
  have hl := log_hundred
  have hdiv : (100-Chebyshev.psi (100:ℝ))/log 100≤2 := by
    apply (div_le_iff₀ (by linarith : 0<log (100:ℝ))).mpr
    linarith [psi_hundred]
  unfold anchor
  linarith [Li_hundred,pi_star_hundred]
#print axioms anchor_lower
end FKSComputationLed.StrongBaseline
