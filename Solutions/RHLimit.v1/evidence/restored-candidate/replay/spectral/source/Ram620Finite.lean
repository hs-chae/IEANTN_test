import Ram620Bands
import Ram620Powers
namespace RHLimit.Ram620
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

lemma table1_bridge (hT : Buthe.v1.table_1_interval_bounds)
    {z : ℝ} (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (-88/100:ℝ) ≤ psiDeficit z ∧ psiDeficit (z-1) ≤ (68/100:ℝ) := by
  have hL := (hT ((320000000000:ℝ),(-88/100:ℝ),(78/100:ℝ))
    (by norm_num [Buthe.v1.table_1]) (exp z) (by linarith) (by norm_num; linarith)).1
  have he : exp (z-1)*exp 1 = exp z := by rw [←exp_add]; congr 1; ring
  have he1 : (2:ℝ) < exp 1 ∧ exp 1 < 3 := by constructor <;> interval_decide 80 (trust := kernel)
  have hx1 : (160000000000:ℝ) ≤ exp (z-1) := by nlinarith [exp_pos (z-1)]
  have hx2 : exp (z-1) ≤ (320000000000:ℝ) := by nlinarith [exp_pos (z-1)]
  have hU := (hT ((160000000000:ℝ),(-88/100:ℝ),(68/100:ℝ))
    (by norm_num [Buthe.v1.table_1]) (exp (z-1)) hx1 (by norm_num; linarith)).2
  constructor
  · simpa only [psiDeficit,←Real.exp_half] using hL
  · simpa only [psiDeficit,←Real.exp_half] using hU

lemma actual_deficits (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {l u z c d : ℝ} (hl : 27 ≤ l) (hu : u ≤ 42) (hlz : l ≤ z) (hzu : z ≤ u)
    (hcut : (620000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000)
    (hc : c ≤ -88/100-shift l u+lowerPowers l u)
    (hd : 68/100+shift (l-1) (u-1)+upperPowers (l-1) ≤ d) :
    c ≤ deficit z ∧ deficit (z-1) ≤ d := by
  have ht := table1_bridge hT hcut hcap
  have hb := abs_le.mp (refined_deficit_band hRH hGM hP hJ (by linarith : 12 ≤ l) hlz hzu)
  have hb' := abs_le.mp (refined_deficit_band hRH hGM hP hJ
    (by linarith : 12 ≤ l-1) (by linarith : l-1 ≤ z-1) (by linarith : z-1 ≤ u-1))
  have hp := powers_lower hL (by linarith : 26 ≤ l) hlz hzu hu
  have hp' := powers_upper hU (by linarith : 26 ≤ l-1)
    (by linarith : l-1 ≤ z-1) (by linarith : z-1 ≤ 42)
  have he := deficit_split z
  have he' := deficit_split (z-1)
  constructor <;> linarith

noncomputable def enhancedMargin (l u c d : ℝ) : ℝ :=
  fullBase u-d*l^5/(l-1)*exp ((1-l)/2)+
    2*pN 20 u*c*u^4*exp (-u/2)-c^2*l^4*exp (-l)

lemma enhanced_slab {l u z c d : ℝ} (hl : 27 ≤ l)
    (hlz : l ≤ z) (hzu : z ≤ u) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hc : c ≤ deficit z) (hd : deficit (z-1) ≤ d) :
    enhancedMargin l u c d ≤ RamStudy.RG (exp z) := by
  have hz27 : (27:ℝ) ≤ z := hl.trans hlz
  have hbase := actual_source_base hz27
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hbase
  have h := actual_signed_gap (show 1 < z by linarith) hbase hc hd
  have hB := fullBase_antitone (show 0 < z by linarith) hzu
  have hwF := weight_antitone (a:=l) (b:=(1/2:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hF1 := hwF hlz (hlz.trans hzu) hzu
  have hF := mul_le_mul_of_nonneg_left hF1 hc0
  have hwQ := weight_antitone (a:=l) (b:=(1:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hQ1 := hwQ (show l ∈ Ici l by simp) hlz hlz
  have hQ := mul_le_mul_of_nonneg_left hQ1 (sq_nonneg c)
  have hH := mul_le_mul_of_nonneg_left (shift_antitone hl hz27 hlz) hd0
  have hw : pN 20 u ≤ RamStudy.w z :=
    (pN_antitone (by linarith : 0 < z) hzu 20).trans (by
      simpa only [actual_w_eq] using (actual_factorial_barrier26 (by linarith : 26 ≤ z)).1)
  have hF0 : 0 ≤ c*weight (1/2) u := by unfold weight; positivity
  have hw0 : 0 ≤ RamStudy.w z := by
    have hu0 : 0 < u := by linarith
    have hn : 0 ≤ pN 20 u := by unfold pN; positivity
    exact hn.trans hw
  have hprod := mul_le_mul hw hF hF0 hw0
  unfold enhancedMargin weight shiftWeight at *
  norm_num only [one_mul,neg_one_mul] at *
  have hnz : -(1/2:ℝ)*z = -z/2 := by ring
  have hnu : -(1/2:ℝ)*u = -u/2 := by ring
  simp only [hnz,hnu] at *
  simp only [div_eq_mul_inv] at h hB hH hQ hprod ⊢
  nlinarith only [h,hB,hH,hQ,hprod]

noncomputable def lowerNoMax (l u : ℝ) : ℝ := pN 8 (u/2)-q (l/2)*exp (-l/4)+
  ∑ k ∈ range 3, exp (-u*(1/2-1/(k+3:ℝ)))*(p3 (u/(k+3))-q (l/(k+3))*exp (-l/(2*(k+3))))
lemma lowerNoMax_le (l u : ℝ) : lowerNoMax l u ≤ lowerPowers l u := by
  unfold lowerNoMax lowerPowers
  apply add_le_add le_rfl
  apply sum_le_sum
  intro k hk
  unfold lowRoot
  push_cast
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) (exp_pos _).le
#print axioms actual_deficits
#print axioms enhanced_slab
end RHLimit.Ram620
