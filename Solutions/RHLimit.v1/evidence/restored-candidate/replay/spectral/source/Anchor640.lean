import ActualLiBarrier640
import Gamma640
import Exp155Barrier640

namespace Ramanujan640.AnalyticBarrier
open Real Set Finset RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def logErr35 : ℝ := 2*(1/3:ℝ)^71/(71*(1-(1/3:ℝ)^2))
noncomputable def logLow3 : ℝ := logAtanhPoly 35 (1/5)+logAtanhPoly 35 (1/3)
noncomputable def logLow13 : ℝ := logAtanhPoly 35 (5/21)+3*logAtanhPoly 35 (1/3)
noncomputable def logLow26 : ℝ := logAtanhPoly 35 (5/21)+4*logAtanhPoly 35 (1/3)

lemma log3_bounds : logLow3 ≤ log (3:ℝ) ∧ log (3:ℝ) ≤ logLow3+2*logErr35 := by
  have h := log35_bounds (r:=(1/5:ℝ)) (by norm_num) (by norm_num)
  have h2 := log35_bounds (r:=(1/3:ℝ)) (by norm_num) (by norm_num)
  norm_num at h h2
  have hid : log (3:ℝ) = log (3/2:ℝ)+log 2 := by
    rw [← Real.log_mul (by norm_num : (3/2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  dsimp [logLow3,logErr35]
  rw [hid]
  constructor <;> linarith

lemma log13_bounds : logLow13 ≤ log (13:ℝ) ∧ log (13:ℝ) ≤ logLow13+4*logErr35 := by
  have h := log35_bounds (r:=(5/21:ℝ)) (by norm_num) (by norm_num)
  have h2 := log35_bounds (r:=(1/3:ℝ)) (by norm_num) (by norm_num)
  norm_num at h h2
  have hid : log (13:ℝ) = log (13/8:ℝ)+3*log 2 := by
    rw [show (13:ℝ)=(13/8)*2^3 by norm_num,
      Real.log_mul (by norm_num : (13/8:ℝ) ≠ 0) (by norm_num : (2:ℝ)^3 ≠ 0),Real.log_pow]
    norm_num
  dsimp [logLow13,logErr35]
  rw [hid]
  constructor <;> linarith

lemma log26_bounds : logLow26 ≤ log (26:ℝ) ∧ log (26:ℝ) ≤ logLow26+5*logErr35 := by
  have h := log13_bounds
  have h2 := log35_bounds (r:=(1/3:ℝ)) (by norm_num) (by norm_num)
  norm_num at h2
  have hid : log (26:ℝ) = log (13:ℝ)+log 2 := by
    rw [← Real.log_mul (by norm_num : (13:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  dsimp [logLow26,logErr35]
  dsimp [logLow13,logErr35] at h
  rw [hid]
  constructor <;> linarith

noncomputable def eiLo (z L : ℝ) : ℝ := eiPartial155 z+L+577/1000
noncomputable def eiHi (z H : ℝ) : ℝ := eiPartial155 z+H+578/1000+
  (z^155/(Nat.factorial 155:ℝ))*z/(156*(156-z))

theorem li_exp_bounds155 {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li)
    {z L H : ℝ} (hz : 0 < z) (hz44 : z ≤ 44)
    (hlog : L ≤ log z ∧ log z ≤ H) :
    eiLo z L ≤ li (exp z) ∧ li (exp z) ≤ eiHi z H := by
  have hid := hseries (exp z) (by simpa using Real.one_lt_exp_iff.mpr hz)
  rw [Real.log_exp] at hid
  have hgamma := gamma_source_bracket
  have htail := ei_series_remainder155 hz.le hz44
  dsimp [eiLo,eiHi]
  constructor <;> linarith

noncomputable def ELo3 : ℝ := (2008553692318766774092852965458171789698790783/100000000000000000000000000000000000000000000:ℝ)
noncomputable def EHi3 : ℝ := (15691825721240365422600413792641967107021803/781250000000000000000000000000000000000000:ℝ)
lemma exp3_source_bounds : ELo3 ≤ exp (3:ℝ) ∧ exp (3:ℝ) ≤ EHi3 := by
  have h := exp_bounds155 (z:=(3:ℝ)) (by norm_num) (by norm_num)
  have hlo : ELo3 ≤ expPartial155 (3:ℝ) := by
    norm_num [ELo3,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  have hup : expPartial155 (3:ℝ)+((3:ℝ)^155/(Nat.factorial 155:ℝ))*3/(156-3) ≤ EHi3 := by
    norm_num [EHi3,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  exact ⟨hlo.trans h.1,h.2.trans hup⟩

noncomputable def ELo13 : ℝ := (22120669600446025166305138797454414089219565303029/50000000000000000000000000000000000000000000:ℝ)
noncomputable def EHi13 : ℝ := (44241339200892050332610277594908828178439130606059/100000000000000000000000000000000000000000000:ℝ)
lemma exp13_source_bounds : ELo13 ≤ exp (13:ℝ) ∧ exp (13:ℝ) ≤ EHi13 := by
  have h := exp_bounds155 (z:=(13:ℝ)) (by norm_num) (by norm_num)
  have hlo : ELo13 ≤ expPartial155 (13:ℝ) := by
    norm_num [ELo13,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  have hup : expPartial155 (13:ℝ)+((13:ℝ)^155/(Nat.factorial 155:ℝ))*13/(156-13) ≤ EHi13 := by
    norm_num [EHi13,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  exact ⟨hlo.trans h.1,h.2.trans hup⟩

noncomputable def ELo26 : ℝ := (19572960942883876426977639787609534279203610095069759389/100000000000000000000000000000000000000000000:ℝ)
noncomputable def EHi26 : ℝ := (1957296094288387642697763978760953427920361009506975939/10000000000000000000000000000000000000000000:ℝ)
lemma exp26_source_bounds : ELo26 ≤ exp (26:ℝ) ∧ exp (26:ℝ) ≤ EHi26 := by
  have h := exp_bounds155 (z:=(26:ℝ)) (by norm_num) (by norm_num)
  have hlo : ELo26 ≤ expPartial155 (26:ℝ) := by
    norm_num [ELo26,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  have hup : expPartial155 (26:ℝ)+((26:ℝ)^155/(Nat.factorial 155:ℝ))*26/(156-26) ≤ EHi26 := by
    norm_num [EHi26,expPartial155,expTerm,Finset.sum_range_succ,Nat.factorial]
  exact ⟨hlo.trans h.1,h.2.trans hup⟩

theorem anchor13 {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    0 ≤ A li 13-pDiv 3 13 ∧
    A li 13-pDiv 3 13 ≤ 3*(Nat.factorial (3+1):ℝ)/(13:ℝ)^(3+2) := by
  have he := exp13_source_bounds
  have hb := li_exp_bounds155 hseries (z:=(13:ℝ)) (by norm_num) (by norm_num) log13_bounds
  have hL0 : 0 ≤ eiLo 13 logLow13 := by
    norm_num [eiLo,eiPartial155,eiTerm,logLow13,logAtanhPoly,Finset.sum_range_succ,Nat.factorial]
  have hE0 : 0 < ELo13 := by norm_num [ELo13]
  have hAl : eiLo 13 logLow13/EHi13 ≤ A li 13 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans hb.1) hb.1 (Real.exp_pos _) he.2
  have hAu : A li 13 ≤ eiHi 13 (logLow13+4*logErr35)/ELo13 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans (hb.1.trans hb.2)) hb.2 hE0 he.1
  have hnumL : pDiv 3 (13:ℝ) ≤ eiLo 13 logLow13/EHi13 := by
    norm_num [pDiv,eiLo,eiPartial155,eiTerm,logLow13,logAtanhPoly,EHi13,Finset.sum_range_succ,Nat.factorial]
  have hnumU : eiHi 13 (logLow13+4*logErr35)/ELo13 ≤
      pDiv 3 13+3*(Nat.factorial (3+1):ℝ)/(13:ℝ)^(3+2) := by
    norm_num [pDiv,eiHi,eiPartial155,eiTerm,logLow13,logAtanhPoly,logErr35,ELo13,Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith

 theorem factorial_barrier13 {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    {z : ℝ} (hz : 13 ≤ z) :
    pN 3 z ≤ w li z ∧
    w li z ≤ pN 3 z+3*(Nat.factorial (3+1):ℝ)/z^(3+1) := by
  exact actual_w_barriers hderiv (by norm_num : (1:ℝ)<13) hz (by norm_num : (0:ℝ)≤3)
    (anchor13 hseries) (by norm_num)

theorem anchor26 {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    0 ≤ A li 26-pDiv 20 26 ∧
    A li 26-pDiv 20 26 ≤ 7*(Nat.factorial (20+1):ℝ)/(26:ℝ)^(20+2) := by
  have he := exp26_source_bounds
  have hb := li_exp_bounds155 hseries (z:=(26:ℝ)) (by norm_num) (by norm_num) log26_bounds
  have hL0 : 0 ≤ eiLo 26 logLow26 := by
    norm_num [eiLo,eiPartial155,eiTerm,logLow26,logAtanhPoly,Finset.sum_range_succ,Nat.factorial]
  have hE0 : 0 < ELo26 := by norm_num [ELo26]
  have hAl : eiLo 26 logLow26/EHi26 ≤ A li 26 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans hb.1) hb.1 (Real.exp_pos _) he.2
  have hAu : A li 26 ≤ eiHi 26 (logLow26+5*logErr35)/ELo26 := by
    rw [A,Real.exp_neg]
    rw [mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hL0.trans (hb.1.trans hb.2)) hb.2 hE0 he.1
  have hnumL : pDiv 20 (26:ℝ) ≤ eiLo 26 logLow26/EHi26 := by
    norm_num [pDiv,eiLo,eiPartial155,eiTerm,logLow26,logAtanhPoly,EHi26,Finset.sum_range_succ,Nat.factorial]
  have hnumU : eiHi 26 (logLow26+5*logErr35)/ELo26 ≤
      pDiv 20 26+7*(Nat.factorial (20+1):ℝ)/(26:ℝ)^(20+2) := by
    norm_num [pDiv,eiHi,eiPartial155,eiTerm,logLow26,logAtanhPoly,logErr35,ELo26,Finset.sum_range_succ,Nat.factorial]
  constructor <;> linarith

 theorem factorial_barrier26 {li : ℝ → ℝ}
    (hseries : LogIntegralSeriesIdentity li) (hderiv : LogIntegralDerivative li)
    {z : ℝ} (hz : 26 ≤ z) :
    pN 20 z ≤ w li z ∧
    w li z ≤ pN 20 z+7*(Nat.factorial (20+1):ℝ)/z^(20+1) := by
  exact actual_w_barriers hderiv (by norm_num : (1:ℝ)<26) hz (by norm_num : (0:ℝ)≤7)
    (anchor26 hseries) (by norm_num)

theorem anchor3_upper {li : ℝ → ℝ} (hseries : LogIntegralSeriesIdentity li) :
    li (exp 3)*3 ≤ (3/2:ℝ)*exp 3 := by
  have he := exp3_source_bounds
  have hb := li_exp_bounds155 hseries (z:=(3:ℝ)) (by norm_num) (by norm_num) log3_bounds
  have hnum : eiHi 3 (logLow3+2*logErr35)*3 ≤ (3/2:ℝ)*ELo3 := by
    norm_num [eiHi,eiPartial155,eiTerm,logLow3,logAtanhPoly,logErr35,ELo3,Finset.sum_range_succ,Nat.factorial]
  linarith

#print axioms li_exp_bounds155
#print axioms exp13_source_bounds
#print axioms exp26_source_bounds
#print axioms anchor13
#print axioms anchor26
#print axioms factorial_barrier13
#print axioms factorial_barrier26
#print axioms anchor3_upper
end Ramanujan640.AnalyticBarrier
