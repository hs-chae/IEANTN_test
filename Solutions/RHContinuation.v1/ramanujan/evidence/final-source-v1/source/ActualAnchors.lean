import LiRelativeSeries
import MainTerm640
namespace RHContinuation.Ramanujan
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier Ramanujan640.MainTerm
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable def wideEiLo (z L : ℝ) : ℝ := eiPartial155 z+L-1
noncomputable def wideEiHi (z H : ℝ) : ℝ := eiPartial155 z+H+6/5+
  (z^155/(Nat.factorial 155:ℝ))*z/(156*(156-z))

theorem actual_li_exp_bounds155 {z L H : ℝ} (hz : 0 < z) (hz44 : z ≤ 44)
    (hlog : L ≤ log z ∧ log z ≤ H) :
    wideEiLo z L ≤ IEANTN.li (exp z) ∧ IEANTN.li (exp z) ≤ wideEiHi z H := by
  have hid := actual_li_relative_series (x:=exp z) (by simpa using Real.one_lt_exp_iff.mpr hz)
  have hC := liSeriesConstant_bounds.1
  have hCU := liSeriesConstant_upper_six_fifths
  have htail := ei_series_remainder155 hz.le hz44
  dsimp [wideEiLo,wideEiHi,liSeriesCore] at *
  rw [Real.log_exp] at hid
  constructor <;> linarith

theorem actual_anchor13 :
    0 ≤ A IEANTN.li 13-pDiv 3 13 ∧
    A IEANTN.li 13-pDiv 3 13 ≤ 3*(Nat.factorial (3+1):ℝ)/(13:ℝ)^(3+2) := by
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
  have hnumL : pDiv 3 (13:ℝ) ≤ wideEiLo 13 logLow13/EHi13 := by
    norm_num [pDiv,wideEiLo,eiPartial155,eiTerm,logLow13,logAtanhPoly,EHi13,Finset.sum_range_succ,Nat.factorial]
  have hnumU : wideEiHi 13 (logLow13+4*logErr35)/ELo13 ≤
      pDiv 3 13+3*(Nat.factorial (3+1):ℝ)/(13:ℝ)^(3+2) := by
    norm_num [pDiv,wideEiHi,eiPartial155,eiTerm,logLow13,logAtanhPoly,logErr35,ELo13,Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith


theorem actual_anchor26 :
    0 ≤ A IEANTN.li 26-pDiv 20 26 ∧
    A IEANTN.li 26-pDiv 20 26 ≤ 7*(Nat.factorial (20+1):ℝ)/(26:ℝ)^(20+2) := by
  have he := exp26_source_bounds
  have hb := actual_li_exp_bounds155 (z:=(26:ℝ)) (by norm_num) (by norm_num) log26_bounds
  have hL0 : 0 ≤ wideEiLo 26 logLow26 := by
    norm_num [wideEiLo,eiPartial155,eiTerm,logLow26,logAtanhPoly,Finset.sum_range_succ,Nat.factorial]
  have hE0 : 0 < ELo26 := by norm_num [ELo26]
  have hAl : wideEiLo 26 logLow26/EHi26 ≤ A IEANTN.li 26 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans hb.1) hb.1 (Real.exp_pos _) he.2
  have hAu : A IEANTN.li 26 ≤ wideEiHi 26 (logLow26+5*logErr35)/ELo26 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans (hb.1.trans hb.2)) hb.2 hE0 he.1
  have hnumL : pDiv 20 (26:ℝ) ≤ wideEiLo 26 logLow26/EHi26 := by
    norm_num [pDiv,wideEiLo,eiPartial155,eiTerm,logLow26,logAtanhPoly,EHi26,Finset.sum_range_succ,Nat.factorial]
  have hnumU : wideEiHi 26 (logLow26+5*logErr35)/ELo26 ≤
      pDiv 20 26+7*(Nat.factorial (20+1):ℝ)/(26:ℝ)^(20+2) := by
    norm_num [pDiv,wideEiHi,eiPartial155,eiTerm,logLow26,logAtanhPoly,logErr35,ELo26,Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith


theorem actual_factorial_barrier13 {z : ℝ} (hz : 13 ≤ z) :
    pN 3 z ≤ w IEANTN.li z ∧ w IEANTN.li z ≤ pN 3 z+72/z^4 := by
  have hd : LogIntegralDerivative IEANTN.li := fun x hx => actual_li_hasDerivAt (by linarith)
  have h := actual_w_barriers hd (by norm_num : (1:ℝ)<13) hz (by norm_num : (0:ℝ)≤3)
    actual_anchor13 (by norm_num)
  norm_num [Nat.factorial] at h
  exact h

theorem actual_factorial_barrier26 {z : ℝ} (hz : 26 ≤ z) :
    pN 20 z ≤ w IEANTN.li z ∧
      w IEANTN.li z ≤ pN 20 z+7*(Nat.factorial 21:ℝ)/z^21 := by
  have hd : LogIntegralDerivative IEANTN.li := fun x hx => actual_li_hasDerivAt (by linarith)
  exact actual_w_barriers hd (by norm_num : (1:ℝ)<26) hz (by norm_num : (0:ℝ)≤7)
    actual_anchor26 (by norm_num)

#print axioms actual_anchor13
#print axioms actual_anchor26
#print axioms actual_factorial_barrier26
end RHContinuation.Ramanujan
