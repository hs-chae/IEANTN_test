import ActualAnalytic
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier
open RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def eiLowerTight (z L : ℝ) := eiPartial155 z+L-1/6
noncomputable def expLower155 (z : ℝ) := expPartial155 z
noncomputable def expUpper155 (z : ℝ) :=
  expPartial155 z+((z^155/(Nat.factorial 155:ℝ))*z/(156-z))

lemma actual_li_exp_lower_tight {z L : ℝ} (hz : 0 < z) (hz44 : z ≤ 44)
    (hlog : L ≤ log z) : eiLowerTight z L ≤ IEANTN.li (exp z) := by
  have hid := actual_li_relative_series (x:=exp z) (one_lt_exp_iff.mpr hz)
  have hC := liSeriesConstant_lower_sixth
  have htail := ei_series_remainder155 hz.le hz44
  dsimp [eiLowerTight,liSeriesCore] at *
  rw [Real.log_exp] at hid
  linarith

lemma log5_source_bounds : (1609/1000:ℝ) ≤ log 5 ∧ log 5 ≤ 161/100 := by
  constructor <;> interval_decide 80 (trust := kernel)

lemma actual_anchor5_lower : 0 ≤ A IEANTN.li 5-pDiv 3 5 := by
  have hb := actual_li_exp_lower_tight (z:=(5:ℝ)) (by norm_num) (by norm_num)
    log5_source_bounds.1
  have he := exp_bounds155 (z:=(5:ℝ)) (by norm_num) (by norm_num)
  have hn0 : 0 ≤ eiLowerTight 5 (1609/1000) := by
    norm_num [eiLowerTight,eiPartial155,eiTerm,Finset.sum_range_succ,Nat.factorial]
  have hn : pDiv 3 (5:ℝ) ≤ eiLowerTight 5 (1609/1000)/expUpper155 5 := by
    norm_num [pDiv,eiLowerTight,eiPartial155,eiTerm,expUpper155,expPartial155,expTerm,
      Finset.sum_range_succ,Nat.factorial]
  have hA : eiLowerTight 5 (1609/1000)/expUpper155 5 ≤ A IEANTN.li 5 := by
    rw [A,exp_neg,mul_comm,← div_eq_mul_inv]
    exact div_le_div₀ (hn0.trans hb) hb (exp_pos _) he.2
  linarith

lemma actual_lower_barrier {N : ℕ} {a z : ℝ} (ha : 1 < a) (haz : a ≤ z)
    (hanchor : 0 ≤ A IEANTN.li a-pDiv N a) : pN N z ≤ w IEANTN.li z := by
  have ha0 : 0 < a := by linarith
  have hz0 : 0 < z := ha0.trans_le haz
  have hd : ∀ t ∈ Ici a, HasDerivAt (fun t => A IEANTN.li t-pDiv N t)
      ((Nat.factorial (N+1):ℝ)/t^(N+2)-(A IEANTN.li t-pDiv N t)) t := by
    intro t ht
    exact actual_residual_hasDerivAt (fun x hx => actual_li_hasDerivAt (by linarith))
      (ha.trans_le ht)
  have h := mul_nonneg hz0.le (residual_lower ha0 haz hd hanchor)
  rw [mul_sub,mul_pDiv hz0.ne'] at h
  dsimp [w]
  linarith

lemma actual_p3_lower5 {z : ℝ} (hz : 5 ≤ z) : pN 3 z ≤ w IEANTN.li z :=
  actual_lower_barrier (by norm_num : (1:ℝ)<5) hz actual_anchor5_lower

#print axioms actual_anchor5_lower
#print axioms actual_p3_lower5
end RHLimit.Ram620
