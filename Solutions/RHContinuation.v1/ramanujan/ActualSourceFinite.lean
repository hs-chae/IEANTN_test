import ActualSourcePolynomial
import ActualFinite
namespace RHContinuation.Ramanujan
open Real Set Finset IEANTN Ramanujan640 Ramanujan640.Polynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def fullEndpointMargin (l u c d : ℝ) : ℝ :=
  fullBase u-d*l^5/(l-1)*exp ((1-l)/2)+
    2*(1+1/u)*c*u^4*exp (-u/2)-c^2*l^4*exp (-l)

lemma fullBase_explicit (z : ℝ) : fullBase z =
    1+
    14/z+
    145/z^2+
    1412/z^3+
    13985/z^4+
    145450/z^5+
    1610021/z^6+
    19063832/z^7+
    241691425/z^8+
    3277187246/z^9+
    47424796805/z^10+
    730550160076/z^11+
    11946592513217/z^12+
    206824220948690/z^13+
    3780755108724421/z^14+
    72793555607972000/z^15+
    1472754152349904001/z^16-1/1000 := by
  norm_num [fullBase,coeff,lhs,rhs,Finset.sum_range_succ,Nat.factorial,Nat.choose]

theorem full_slab_consumer {l u z c d : ℝ} (hl : 27 ≤ l)
    (hlz : l ≤ z) (hzu : z ≤ u) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (hbase : fullBase z ≤ z^4*(z/(z-1)*RamStudy.w (z-1)-(RamStudy.w z)^2))
    (hwl : 1+1/z ≤ RamStudy.w z)
    (hc : c ≤ deficit z) (hd : deficit (z-1) ≤ d) :
    fullEndpointMargin l u c d ≤ RamStudy.RG (exp z) := by
  have hz27 : (27:ℝ) ≤ z := hl.trans hlz
  have hu27 : (27:ℝ) ≤ u := hz27.trans hzu
  have h := actual_signed_gap (show 1 < z by linarith) hbase hc hd
  have hB := fullBase_antitone (show 0 < z by linarith) hzu
  have hwF := weight_antitone (a:=l) (b:=(1/2:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hF1 := hwF hlz (hlz.trans hzu) hzu
  have hF := mul_le_mul_of_nonneg_left hF1 hc0
  have hwQ := weight_antitone (a:=l) (b:=(1:ℝ)) (by linarith) (by norm_num) (by linarith)
  have hQ1 := hwQ (show l ∈ Ici l by simp) hlz hlz
  have hQ := mul_le_mul_of_nonneg_left hQ1 (sq_nonneg c)
  have hH := mul_le_mul_of_nonneg_left (shift_antitone hl hz27 hlz) hd0
  have hwi : 1/u ≤ 1/z := one_div_le_one_div_of_le (by linarith) hzu
  have hw : 1+1/u ≤ RamStudy.w z := by linarith
  have hF0 : 0 ≤ c*weight (1/2) u := by unfold weight;positivity
  have hw0 : 0 ≤ RamStudy.w z := by
    have hzp : 0 < z := by linarith
    have hrec : 0 < 1/z := by positivity
    linarith
  have hprod := mul_le_mul hw hF hF0 hw0
  unfold fullEndpointMargin weight shiftWeight at *
  norm_num only [one_mul, neg_one_mul] at *
  have hnz : -(1/2:ℝ)*z = -z/2 := by ring
  have hnu : -(1/2:ℝ)*u = -u/2 := by ring
  simp only [hnz,hnu] at *
  simp only [div_eq_mul_inv] at h hB hH hQ hprod ⊢
  nlinarith only [h,hB,hH,hQ,hprod]


theorem source_margin_0 : (1/12:ℝ) ≤ fullEndpointMargin (6957/256:ℝ) (1743/64:ℝ) c0 nd0 := by
  unfold fullEndpointMargin c0 nd0
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_0 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (6957/256:ℝ) ≤ z) (hu : z ≤ (1743/64:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_0 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_0.trans (full_slab_consumer
    (l:=(6957/256:ℝ)) (u:=(1743/64:ℝ)) (by norm_num) hl hu
    (proof_representation_0).1 nd0_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_1 : (1/12:ℝ) ≤ fullEndpointMargin (1743/64:ℝ) (879/32:ℝ) c1 nd1 := by
  unfold fullEndpointMargin c1 nd1
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_1 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1743/64:ℝ) ≤ z) (hu : z ≤ (879/32:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_1 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_1.trans (full_slab_consumer
    (l:=(1743/64:ℝ)) (u:=(879/32:ℝ)) (by norm_num) hl hu
    (proof_representation_1).1 nd1_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_2 : (1/12:ℝ) ≤ fullEndpointMargin (879/32:ℝ) (1773/64:ℝ) c2 nd2 := by
  unfold fullEndpointMargin c2 nd2
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_2 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (879/32:ℝ) ≤ z) (hu : z ≤ (1773/64:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_2 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_2.trans (full_slab_consumer
    (l:=(879/32:ℝ)) (u:=(1773/64:ℝ)) (by norm_num) hl hu
    (proof_representation_2).1 nd2_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_3 : (1/12:ℝ) ≤ fullEndpointMargin (1773/64:ℝ) (447/16:ℝ) c3 nd3 := by
  unfold fullEndpointMargin c3 nd3
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_3 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (1773/64:ℝ) ≤ z) (hu : z ≤ (447/16:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_3 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_3.trans (full_slab_consumer
    (l:=(1773/64:ℝ)) (u:=(447/16:ℝ)) (by norm_num) hl hu
    (proof_representation_3).1 nd3_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_4 : (1/12:ℝ) ≤ fullEndpointMargin (447/16:ℝ) (231/8:ℝ) c4 nd4 := by
  unfold fullEndpointMargin c4 nd4
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_4 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (447/16:ℝ) ≤ z) (hu : z ≤ (231/8:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_4 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_4.trans (full_slab_consumer
    (l:=(447/16:ℝ)) (u:=(231/8:ℝ)) (by norm_num) hl hu
    (proof_representation_4).1 nd4_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_5 : (1/12:ℝ) ≤ fullEndpointMargin (231/8:ℝ) (123/4:ℝ) c5 nd5 := by
  unfold fullEndpointMargin c5 nd5
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_5 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (231/8:ℝ) ≤ z) (hu : z ≤ (123/4:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_5 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_5.trans (full_slab_consumer
    (l:=(231/8:ℝ)) (u:=(123/4:ℝ)) (by norm_num) hl hu
    (proof_representation_5).1 nd5_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_6 : (1/12:ℝ) ≤ fullEndpointMargin (123/4:ℝ) (69/2:ℝ) c6 nd6 := by
  unfold fullEndpointMargin c6 nd6
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_6 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (123/4:ℝ) ≤ z) (hu : z ≤ (69/2:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_6 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_6.trans (full_slab_consumer
    (l:=(123/4:ℝ)) (u:=(69/2:ℝ)) (by norm_num) hl hu
    (proof_representation_6).1 nd6_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_margin_7 : (1/12:ℝ) ≤ fullEndpointMargin (69/2:ℝ) (42:ℝ) c7 nd7 := by
  unfold fullEndpointMargin c7 nd7
  rw [fullBase_explicit]
  interval_decide 80 (trust := kernel)

theorem source_gap_7 (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hl : (69/2:ℝ) ≤ z) (hu : z ≤ (42:ℝ))
    (hcut : (640000000000:ℝ) ≤ exp z) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hdef := actual_deficits_7 hT hJ hL hU hl hu hcut
  have hsource := actual_source_base (by linarith : (27:ℝ) ≤ z)
  rw [sourceBase_eq (by linarith : z ≠ 0)] at hsource
  exact source_margin_7.trans (full_slab_consumer
    (l:=(69/2:ℝ)) (u:=(42:ℝ)) (by norm_num) hl hu
    (proof_representation_7).1 nd7_nonneg hsource
    (actual_linear_no_series (by linarith)) hdef.1 hdef.2)

theorem source_finite_log_ray (hT : Buthe.v1.table_2_interval_bounds)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hL : Buthe.v1.theorem_2_li_minus_pi)
    (hU : Buthe.v1.theorem_2_li_gt_pi)
    {z : ℝ} (hcut : (640000000000:ℝ) ≤ exp z) (hz42 : z ≤ 42) :
    (1/12:ℝ) ≤ RamStudy.RG (exp z) := by
  have hfirst : (6957/256:ℝ) ≤ z := by
    have h := first_log_below_cut.trans_le hcut
    exact (exp_lt_exp.mp h).le
  by_cases h0 : z ≤ (1743/64:ℝ)
  · exact source_gap_0 hT hJ hL hU (by linarith) h0 hcut
  by_cases h1 : z ≤ (879/32:ℝ)
  · exact source_gap_1 hT hJ hL hU (by linarith) h1 hcut
  by_cases h2 : z ≤ (1773/64:ℝ)
  · exact source_gap_2 hT hJ hL hU (by linarith) h2 hcut
  by_cases h3 : z ≤ (447/16:ℝ)
  · exact source_gap_3 hT hJ hL hU (by linarith) h3 hcut
  by_cases h4 : z ≤ (231/8:ℝ)
  · exact source_gap_4 hT hJ hL hU (by linarith) h4 hcut
  by_cases h5 : z ≤ (123/4:ℝ)
  · exact source_gap_5 hT hJ hL hU (by linarith) h5 hcut
  by_cases h6 : z ≤ (69/2:ℝ)
  · exact source_gap_6 hT hJ hL hU (by linarith) h6 hcut
  exact source_gap_7 hT hJ hL hU (by linarith) hz42 hcut


#print axioms source_finite_log_ray
end RHContinuation.Ramanujan
