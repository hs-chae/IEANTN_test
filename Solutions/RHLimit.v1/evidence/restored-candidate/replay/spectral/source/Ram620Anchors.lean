import Ram620Low
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier Ramanujan640.MainTerm
open RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma anchor_p8_13 :
    0 ≤ A IEANTN.li 13-pDiv 8 13 ∧
    A IEANTN.li 13-pDiv 8 13 ≤ 5*(Nat.factorial (8+1):ℝ)/(13:ℝ)^(8+2) := by
  have he := exp13_source_bounds
  have hb := actual_li_exp_bounds155 (z:=(13:ℝ)) (by norm_num) (by norm_num) log13_bounds
  have hL0 : 0 ≤ wideEiLo 13 logLow13 := by
    norm_num [wideEiLo,eiPartial155,eiTerm,logLow13,logAtanhPoly,Finset.sum_range_succ,Nat.factorial]
  have hE0 : 0 < ELo13 := by norm_num [ELo13]
  have hAl : wideEiLo 13 logLow13/EHi13 ≤ A IEANTN.li 13 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans hb.1) hb.1 (Real.exp_pos _) he.2
  have hAu : A IEANTN.li 13 ≤ wideEiHi 13 (logLow13+4*logErr35)/ELo13 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans (hb.1.trans hb.2)) hb.2 hE0 he.1
  have hnumL : pDiv 8 (13:ℝ) ≤ wideEiLo 13 logLow13/EHi13 := by
    norm_num [pDiv,wideEiLo,eiPartial155,eiTerm,logLow13,logAtanhPoly,EHi13,Finset.sum_range_succ,Nat.factorial]
  have hnumU : wideEiHi 13 (logLow13+4*logErr35)/ELo13 ≤
      pDiv 8 13+5*(Nat.factorial (8+1):ℝ)/(13:ℝ)^(8+2) := by
    norm_num [pDiv,wideEiHi,eiPartial155,eiTerm,logLow13,logAtanhPoly,logErr35,ELo13,Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith

lemma anchor_p1_5 :
    0 ≤ A IEANTN.li 5-pDiv 1 5 ∧
    A IEANTN.li 5-pDiv 1 5 ≤ 3*(Nat.factorial (1+1):ℝ)/(5:ℝ)^(1+2) := by
  have he := exp_bounds155 (z:=(5:ℝ)) (by norm_num) (by norm_num)
  have hb := actual_li_exp_bounds155 (z:=(5:ℝ)) (by norm_num) (by norm_num) log5_source_bounds
  have hL0 : 0 ≤ wideEiLo 5 (1609/1000) := by
    norm_num [wideEiLo,eiPartial155,eiTerm,Finset.sum_range_succ,Nat.factorial]
  have hE0 : 0 < expPartial155 (5:ℝ) := by
    norm_num [expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  have hAl : wideEiLo 5 (1609/1000)/expUpper155 5 ≤ A IEANTN.li 5 := by
    rw [A,Real.exp_neg,mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans hb.1) hb.1 (Real.exp_pos _) he.2
  have hAu : A IEANTN.li 5 ≤ wideEiHi 5 (161/100)/expPartial155 5 := by
    rw [A,Real.exp_neg,mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans (hb.1.trans hb.2)) hb.2 hE0 he.1
  have hnumL : pDiv 1 (5:ℝ) ≤ wideEiLo 5 (1609/1000)/expUpper155 5 := by
    norm_num [pDiv,wideEiLo,eiPartial155,eiTerm,expUpper155,expPartial155,expTerm,
      Finset.sum_range_succ,Nat.factorial]
  have hnumU : wideEiHi 5 (161/100)/expPartial155 5 ≤
      pDiv 1 5+3*(Nat.factorial (1+1):ℝ)/(5:ℝ)^(1+2) := by
    norm_num [pDiv,wideEiHi,eiPartial155,eiTerm,expPartial155,expTerm,
      Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith

lemma actual_p8 {z : ℝ} (hz : 13 ≤ z) :
    pN 8 z ≤ RamStudy.w z ∧ RamStudy.w z ≤ pN 8 z+5*362880/z^9 := by
  have hd : LogIntegralDerivative IEANTN.li := fun x hx => actual_li_hasDerivAt (by linarith)
  have h := actual_w_barriers hd (by norm_num : (1:ℝ)<13) hz (by norm_num : (0:ℝ)≤5)
    anchor_p8_13 (by norm_num)
  norm_num only [actual_w_eq,Nat.factorial,Nat.reduceAdd,Nat.reduceMul,Nat.cast_ofNat] at h
  simpa only [show (5*362880:ℝ)=1814400 by norm_num] using h
lemma actual_p1 {z : ℝ} (hz : 5 ≤ z) :
    pN 1 z ≤ RamStudy.w z ∧ RamStudy.w z ≤ pN 1 z+6/z^2 := by
  have hd : LogIntegralDerivative IEANTN.li := fun x hx => actual_li_hasDerivAt (by linarith)
  have h := actual_w_barriers hd (by norm_num : (1:ℝ)<5) hz (by norm_num : (0:ℝ)≤3)
    anchor_p1_5 (by norm_num)
  simpa only [actual_w_eq,show (3*(Nat.factorial (1+1):ℝ))=6 by norm_num] using h
#print axioms actual_p8
#print axioms actual_p1
end RHLimit.Ram620
