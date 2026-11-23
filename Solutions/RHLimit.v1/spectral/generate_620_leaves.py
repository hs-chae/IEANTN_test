#!/usr/bin/env python3
"""Generate readable exact scalar goals; acceptance is Lean kernel compilation."""
from pathlib import Path
from scout_620_bridge import run
B=Path(__file__).resolve().parent
rows=run()['rows']
s='''import Ram620Finite
import ActualSourceResult
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
'''
for i,r in enumerate(rows):
 l,u,c,d=[f"({r[k]}:ℝ)"for k in ['l','u','c','d']]
 s+=f'''
lemma c_number_{i} : {c} ≤ -88/100-shift {l} {u}+lowerNoMax {l} {u} := by
  unfold shift lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma d_number_{i} : 68/100+shift ({l}-1) ({u}-1)+upperPowers ({l}-1) ≤ {d} := by
  unfold shift upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
lemma margin_{i} : (1/1000:ℝ) ≤ enhancedMargin {l} {u} {c} {d} := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)
theorem gap_{i} (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hl : {l} ≤ z) (hu : z ≤ {u})
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hc := c_number_{i}.trans (by
    linarith [lowerNoMax_le {l} {u}] :
      -88/100-shift {l} {u}+lowerNoMax {l} {u} ≤ -88/100-shift {l} {u}+lowerPowers {l} {u})
  have hb := actual_deficits hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ {l}) (by norm_num : {u} ≤ 42) hl hu hcut hcap hc d_number_{i}
  exact margin_{i}.trans (enhanced_slab (by norm_num : 27 ≤ {l}) hl hu
    (by norm_num : 0 ≤ {c}) (by norm_num : 0 ≤ {d}) hb.1 hb.2)
'''
s+='''
theorem finite_bridge (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp (444873/16384:ℝ) ≤ (620000000000:ℝ) := by interval_decide 80 (trust := kernel)
  have hhi : (640000000000:ℝ) ≤ exp (1743/64:ℝ) := by interval_decide 80 (trust := kernel)
  have hl : (444873/16384:ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ (1743/64:ℝ) := exp_le_exp.mp (hcap.trans hhi)
'''
for i,r in enumerate(rows[:-1]):
 u=f"({r['u']}:ℝ)";s+=f'''  by_cases h{i} : z ≤ {u}
  · exact gap_{i} hRH hGM hP hJ hT hL hU (by linarith) h{i} hcut hcap
'''
s+='''  exact gap_4 hRH hGM hP hJ hT hL hU (by linarith) hu hcut hcap

theorem actual_ramanujan_620b (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT1 : Buthe.v1.table_1_interval_bounds) (hT2 : Buthe.v1.table_2_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    (hS : Buthe2016.v1.theorem_2_li_minus_pi)
    {x : ℝ} (hx : (620000000000:ℝ) ≤ x) : (1/1000:ℝ) ≤ RamStudy.RG x := by
  have hx0 : 0 < x := by linarith
  by_cases h640 : (640000000000:ℝ) ≤ x
  · have h := source_ramanujan_640b hRH hT2 hJ hL hU hS h640
    linarith
  · have h := finite_bridge hRH hGM hP hJ hT1 hL hU (z:=log x)
      (by simpa only [exp_log hx0] using hx)
      (by rw [exp_log hx0]; linarith)
    simpa only [exp_log hx0] using h
#print axioms finite_bridge
#print axioms actual_ramanujan_620b
#check @actual_ramanujan_620b
end RHLimit.Ram620
'''
(B/'Ram620Leaves.lean').write_text(s)
