import ActualGMPrimitive
namespace RHContinuation.Ramanujan
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable def gmWeight (t : ℝ) : ℝ := 1/(t*(log t)^2)
noncomputable def gmKernel (t : ℝ) : ℝ := 1/(t^2*(log t)^2)+2/(t^2*(log t)^3)
/-- GM1312.4465v4 Theorem1.1, rational field case, all four source terms. -/
noncomputable def gmEnvelope (t : ℝ) : ℝ :=
  (231/5000:ℝ)*t*sqrt t+(919/500:ℝ)*t+19851/10000+(5097/10000:ℝ)/t
/-- Exact published source bound on the actual primitive, not on desired J error. -/
def GM_Q_Theorem1_1 : Prop := SharedRH.hypothesis →
  ∀ t : ℝ, 3 ≤ t → |gmPrimitive t| ≤ gmEnvelope t

lemma gmWeight_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt gmWeight (-gmKernel t) t := by
  have ht0 : t ≠ 0 := by linarith
  have hl0 : log t ≠ 0 := (log_pos ht).ne'
  have hd := ((hasDerivAt_id t).mul ((hasDerivAt_log ht0).pow 2)).inv
    (mul_ne_zero ht0 (pow_ne_zero 2 hl0))
  convert! hd using 1
  · funext x
    simp [gmWeight]
  · simp only [gmKernel,Pi.mul_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat,
      Nat.reduceSub,pow_one,mul_one]
    field_simp [ht0,hl0]
    <;> ring

lemma gmKernel_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn gmKernel (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl0 : log t ≠ 0 := (log_pos (ha.trans_le ht.1)).ne'
  have hl := Real.continuousAt_log ht0
  exact ((continuousAt_const.div ((continuousAt_id.pow 2).mul (hl.pow 2))
    (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hl0))).add
    (continuousAt_const.div ((continuousAt_id.pow 2).mul (hl.pow 3))
      (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 3 hl0)))).continuousWithinAt

/-- Actual ordinary-endpoint primitive integration by parts; all jump terms
are covered by the proved right derivatives of the finite Mangoldt primitive. -/
theorem actual_gm_integral_parts {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, (Chebyshev.psi t-t)*gmWeight t) =
      gmPrimitive b*gmWeight b-gmPrimitive a*gmWeight a+
        ∫ t in Set.Ioc a b, gmPrimitive t*gmKernel t := by
  have hF : ContinuousOn gmPrimitive (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact gmPrimitive_continuousOn (by linarith)
  have hw : ContinuousOn gmWeight (Set.uIcc a b) := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact (gmWeight_derivative (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hdF : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt gmPrimitive (Chebyshev.psi t-t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hab,max_eq_right hab] at ht
    exact gmPrimitive_right_derivative (by linarith [ht.1])
  have hdw : ∀ t ∈ Set.Ioo (min a b) (max a b),
      HasDerivWithinAt gmWeight (-gmKernel t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hab,max_eq_right hab] at ht
    exact (gmWeight_derivative (ha.trans ht.1)).hasDerivWithinAt
  have hE : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t-t) volume a b :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable a b)
  have hk : IntervalIntegrable gmKernel volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact gmKernel_continuousOn ha
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    hF hw hdF hdw hE hk.neg
  have he : (∫ t in a..b, gmPrimitive t*(-gmKernel t)) =
      -(∫ t in a..b, gmPrimitive t*gmKernel t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [he] at h
  simp only [intervalIntegral.integral_of_le hab] at h
  linarith

lemma gmEnvelope_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn gmEnvelope (Set.Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  unfold gmEnvelope
  fun_prop (disch := assumption)

noncomputable def gmTransport (a b : ℝ) : ℝ :=
  gmEnvelope b*gmWeight b+gmEnvelope a*gmWeight a+
    ∫ t in Set.Ioc a b, gmEnvelope t*gmKernel t

theorem actual_gm_weighted_error (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    |∫ t in Set.Ioc a b, (Chebyshev.psi t-t)/(t*(log t)^2)| ≤ gmTransport a b := by
  have ha1 : 1 < a := by linarith
  have hF := gmPrimitive_continuousOn (a:=a) (b:=b) (by linarith)
  have hk := gmKernel_continuousOn (a:=a) (b:=b) ha1
  have hG := gmEnvelope_continuousOn (a:=a) (b:=b) (by linarith)
  have hiF : IntegrableOn (fun t => gmPrimitive t*gmKernel t) (Set.Ioc a b) :=
    (hF.mul hk).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hiG : IntegrableOn (fun t => gmEnvelope t*gmKernel t) (Set.Ioc a b) :=
    (hG.mul hk).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint {t : ℝ} (ht : a ≤ t) :
      |gmPrimitive t*gmKernel t| ≤ gmEnvelope t*gmKernel t := by
    have ht1 : 1 < t := ha1.trans_le ht
    have ht0 : 0 < t := by linarith
    have hl0 : 0 < log t := log_pos ht1
    have hk0 : 0 ≤ gmKernel t := by unfold gmKernel; positivity
    rw [abs_mul,abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right (hGM hRH t (ha.trans ht)) hk0
  have hI : |∫ t in Set.Ioc a b, gmPrimitive t*gmKernel t| ≤
      ∫ t in Set.Ioc a b, gmEnvelope t*gmKernel t := by
    apply (abs_integral_le_integral_abs).trans
    apply setIntegral_mono_on hiF.abs hiG measurableSet_Ioc
    intro t ht
    exact hpoint ht.1.le
  have hW {t : ℝ} (ht : a ≤ t) :
      |gmPrimitive t*gmWeight t| ≤ gmEnvelope t*gmWeight t := by
    have ht1 : 1 < t := ha1.trans_le ht
    have hw0 : 0 ≤ gmWeight t := by unfold gmWeight; positivity
    rw [abs_mul,abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (hGM hRH t (ha.trans ht)) hw0
  have hA := hW (t:=a) le_rfl
  have hB := hW hab
  have ht := abs_add_le (gmPrimitive b*gmWeight b-gmPrimitive a*gmWeight a)
    (∫ t in Set.Ioc a b, gmPrimitive t*gmKernel t)
  have hs : |gmPrimitive b*gmWeight b-gmPrimitive a*gmWeight a| ≤
      |gmPrimitive b*gmWeight b|+|gmPrimitive a*gmWeight a| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le (gmPrimitive b*gmWeight b) 0 (gmPrimitive a*gmWeight a)
  have hid : (∫ t in Set.Ioc a b, (Chebyshev.psi t-t)/(t*(log t)^2)) =
      gmPrimitive b*gmWeight b-gmPrimitive a*gmWeight a+
        ∫ t in Set.Ioc a b, gmPrimitive t*gmKernel t := by
    simpa [gmWeight,div_eq_mul_inv] using actual_gm_integral_parts ha1 hab
  rw [hid]
  unfold gmTransport
  linarith

/-- The desired actual-J transfer is derived from the published primitive
bound and proved integration calculus; it is not a new input predicate. -/
theorem actual_J_from_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    |riemannPrimeCounting b-IEANTN.li b-(Chebyshev.psi b-b)/log b| ≤
      |riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/log a|+
        gmTransport a b := by
  have hc := actual_riemann_compensation (by linarith : 1 < a) hab
  have h := actual_gm_weighted_error hRH hGM ha hab
  rw [← hc] at h
  have ht := abs_add_le
    ((riemannPrimeCounting b-IEANTN.li b-(Chebyshev.psi b-b)/log b)-
      (riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/log a))
    (riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/log a)
  simp only [sub_add_cancel] at ht
  linarith


set_option leancert.trust "kernel"
lemma gm_anchor_domain : (11:ℝ) < exp 8 ∧ exp 8 ≤ 10^(19:ℕ) := by
  constructor <;> interval_decide 80 (trust := kernel)

lemma actual_J_anchor_bound (hP : Buthe.v1.theorem_2_psi)
    (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {a : ℝ} (ha : 11 < a) (haU : a ≤ 10^(19:ℕ)) :
    |riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/log a| ≤
      (194/100:ℝ)*sqrt a/log a := by
  have hl : 0 < log a := log_pos (by linarith)
  have hJb : |riemannPrimeCounting a-IEANTN.li a| ≤ sqrt a/log a := by
    rw [abs_sub_comm]
    exact (hJ a (by linarith) haU).le
  have hPb : |Chebyshev.psi a-a| ≤ (94/100:ℝ)*sqrt a := by
    rw [abs_sub_comm]
    convert hP a ha haU using 1 <;> norm_num
  have hd : |(Chebyshev.psi a-a)/log a| ≤ (94/100:ℝ)*sqrt a/log a := by
    rw [abs_div,abs_of_pos hl]
    exact div_le_div_of_nonneg_right hPb hl.le
  have ht : |riemannPrimeCounting a-IEANTN.li a-(Chebyshev.psi a-a)/log a| ≤
      |riemannPrimeCounting a-IEANTN.li a|+|(Chebyshev.psi a-a)/log a| := by
    simpa only [sub_zero,zero_sub,abs_neg] using
      abs_sub_le (riemannPrimeCounting a-IEANTN.li a) 0 ((Chebyshev.psi a-a)/log a)
  calc _ ≤ _ := ht
    _ ≤ sqrt a/log a+(94/100:ℝ)*sqrt a/log a := add_le_add hJb hd
    _ = _ := by ring

lemma gm_anchor_full_budget :
    (194/100:ℝ)*sqrt (exp 8)/log (exp 8)+gmEnvelope (exp 8)*gmWeight (exp 8) ≤14 := by
  have he : exp (8:ℝ)=(exp 4)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hs : sqrt (exp (8:ℝ))=exp 4 := by rw [he,Real.sqrt_sq (exp_pos 4).le]
  unfold gmEnvelope gmWeight
  simp only [Real.log_exp,hs]
  interval_decide 80 (trust := kernel) <;> ring

/-- Fully explicit constructive J envelope. Both source constants1.9851 and
.5097/t are retained inside the endpoint AND the integral. -/
noncomputable def gmExplicitJBound (x : ℝ) : ℝ :=
  14+gmEnvelope x*gmWeight x+
    ∫ t in Set.Ioc (exp 8) x, gmEnvelope t*gmKernel t

theorem actual_J_explicit_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 8 ≤ x) :
    |riemannPrimeCounting x-IEANTN.li x-(Chebyshev.psi x-x)/log x| ≤ gmExplicitJBound x := by
  have hd := gm_anchor_domain
  have h := actual_J_from_GM hRH hGM (by linarith [hd.1] : (3:ℝ) ≤ exp 8) hx
  have hA := actual_J_anchor_bound hP hJ hd.1 hd.2
  have hB := gm_anchor_full_budget
  unfold gmTransport at h
  unfold gmExplicitJBound
  linarith

/-- Exact actual-prime signed transfer. The prime-power correction is retained
with its correct sign for downstream theta/prime-power interval providers. -/
theorem actual_pi_signed_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 8 ≤ x) :
    (Chebyshev.psi x-x)/log x-gmExplicitJBound x-
      (riemannPrimeCounting x-primeCounting x) ≤ primeCounting x-IEANTN.li x ∧
    primeCounting x-IEANTN.li x ≤ (Chebyshev.psi x-x)/log x+gmExplicitJBound x-
      (riemannPrimeCounting x-primeCounting x) := by
  have h := actual_J_explicit_GM hRH hGM hP hJ hx
  rw [abs_le] at h
  constructor <;> linarith [h.1,h.2]

#print axioms actual_J_explicit_GM
#print axioms actual_pi_signed_GM
#print axioms actual_J_from_GM
#print axioms actual_gm_integral_parts
end RHContinuation.Ramanujan
