import ActualGMTransfer
namespace RHContinuation.Ramanujan
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
noncomputable def gmSqrtLog (t : ℝ) : ℝ := sqrt t/(log t)^2
noncomputable def gmAntiderivativeUpper (t : ℝ) : ℝ :=
  (1386/5000:ℝ)*gmSqrtLog t-(919/500:ℝ)/log t-gmEnvelope t*gmWeight t

lemma gmEnvelope_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt gmEnvelope
      ((693/10000:ℝ)*sqrt t+919/500-(5097/10000:ℝ)/t^2) t := by
  have hs0 : sqrt t ≠ 0 := (sqrt_pos.mpr ht).ne'
  have h := ((((hasDerivAt_id t).mul (hasDerivAt_sqrt ht.ne')).const_mul (231/5000:ℝ)).add
    ((hasDerivAt_id t).const_mul (919/500:ℝ))).add_const (19851/10000:ℝ)
  have h2 := h.add (((hasDerivAt_id t).inv ht.ne').const_mul (5097/10000:ℝ))
  convert! h2 using 1
  · funext x
    simp [gmEnvelope,div_eq_mul_inv]
    ring
  · simp only [id_eq,mul_one]
    have he := sq_sqrt ht.le
    generalize hh : sqrt t=s at *
    rw [←he]
    field_simp [hs0]
    <;> ring

lemma gmSqrtLog_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt gmSqrtLog ((1/2-2/log t)/(sqrt t*(log t)^2)) t := by
  have ht0 : 0 < t := by linarith
  have hs0 : sqrt t ≠ 0 := (sqrt_pos.mpr ht0).ne'
  have hl0 : log t ≠ 0 := (log_pos ht).ne'
  have h := (hasDerivAt_sqrt ht0.ne').div ((hasDerivAt_log ht0.ne').pow 2)
    (pow_ne_zero 2 hl0)
  convert! h using 1
  simp only [Pi.mul_apply,Pi.pow_apply,id_eq,mul_one,Nat.cast_ofNat,Nat.reduceSub,pow_one]
  have he := sq_sqrt ht0.le
  generalize hh : sqrt t=s at *
  generalize hl : log t=l at *
  rw [←he]
  field_simp [hs0,hl0]
  <;> ring

lemma gmAntiderivativeUpper_derivative {t : ℝ} (ht : 1 < t) :
    HasDerivAt gmAntiderivativeUpper
      (gmEnvelope t*gmKernel t+
        (231/5000:ℝ)*(3/2-12/log t)/(sqrt t*(log t)^2)+
        (5097/10000:ℝ)/(t^3*(log t)^2)) t := by
  have ht0 : 0 < t := by linarith
  have hs0 : sqrt t ≠ 0 := (sqrt_pos.mpr ht0).ne'
  have hl0 : log t ≠ 0 := (log_pos ht).ne'
  have h := (((gmSqrtLog_derivative ht).const_mul (1386/5000:ℝ)).sub
    (((hasDerivAt_log ht0.ne').inv hl0).const_mul (919/500:ℝ))).sub
      ((gmEnvelope_derivative ht0).mul (gmWeight_derivative ht))
  convert! h using 1
  simp only [gmKernel,gmWeight,gmEnvelope,id_eq,mul_one]
  have he := sq_sqrt ht0.le
  generalize hh : sqrt t=s at *
  generalize hl : log t=l at *
  rw [←he]
  field_simp [hs0,hl0]
  <;> ring

lemma gmTransport_upper {a b : ℝ} (ha : exp 8 ≤ a) (hab : a ≤ b) :
    gmTransport a b ≤ (1386/5000:ℝ)*gmSqrtLog b+
      2*gmEnvelope a*gmWeight a+(919/500:ℝ)/log a := by
  have ha0 : 0 < a := (exp_pos 8).trans_le ha
  have ha1 : 1 < a := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<8)).trans_le ha
  have hL {t : ℝ} (ht : a ≤ t) : (8:ℝ) ≤ log t := by
    apply exp_le_exp.mp
    simpa only [exp_log (ha0.trans_le ht)] using ha.trans ht
  have hc : ContinuousOn gmAntiderivativeUpper (Set.Icc a b) := by
    intro t ht
    exact (gmAntiderivativeUpper_derivative (ha1.trans_le ht.1)).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun t => gmEnvelope t*gmKernel t) (Set.Icc a b) :=
    ((gmEnvelope_continuousOn ha0).mul (gmKernel_continuousOn ha1)).integrableOn_Icc
  have h := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le hab hc
    (fun t ht => (gmAntiderivativeUpper_derivative (ha1.trans ht.1)).hasDerivWithinAt) hi
    (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have hl0 : 0 < log t := log_pos (ha1.trans ht.1)
      have hl8 := hL ht.1.le
      have hq : 12/log t ≤ (3/2:ℝ) := (div_le_iff₀ hl0).mpr (by linarith)
      have hp : 0 ≤ (231/5000:ℝ)*(3/2-12/log t)/(sqrt t*(log t)^2) := by positivity
      have hp2 : 0 ≤ (5097/10000:ℝ)/(t^3*(log t)^2) := by positivity
      linarith)
  rw [intervalIntegral.integral_of_le hab] at h
  have hbL : 0 < log b := log_pos (ha1.trans_le hab)
  have hp : 0 ≤ (919/500:ℝ)/log b := by positivity
  have hpA : 0 ≤ (1386/5000:ℝ)*gmSqrtLog a := by unfold gmSqrtLog; positivity
  unfold gmTransport gmAntiderivativeUpper at *
  linarith

lemma gm_closed_anchor_budget :
    (194/100:ℝ)*sqrt (exp 8)/log (exp 8)+
      2*gmEnvelope (exp 8)*gmWeight (exp 8)+(919/500:ℝ)/log (exp 8) ≤14 := by
  have he : exp (8:ℝ)=(exp 4)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have hs : sqrt (exp (8:ℝ))=exp 4 := by rw [he,Real.sqrt_sq (exp_pos 4).le]
  unfold gmEnvelope gmWeight
  simp only [Real.log_exp,hs]
  interval_decide 80 (trust := kernel) <;> ring

/-- Closed whole-real J bound from the literal four-term GM source, with
all primitive/Abel/integration steps proved and no desired J-bound input. -/
theorem actual_J_closed_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 8 ≤ x) :
    |riemannPrimeCounting x-IEANTN.li x-(Chebyshev.psi x-x)/log x| ≤
      14+(1386/5000:ℝ)*sqrt x/(log x)^2 := by
  have hd := gm_anchor_domain
  have h := actual_J_from_GM hRH hGM (by linarith [hd.1] : (3:ℝ) ≤ exp 8) hx
  have hA := actual_J_anchor_bound hP hJ hd.1 hd.2
  have hT := gmTransport_upper (a:=exp 8) le_rfl hx
  have hB := gm_closed_anchor_budget
  unfold gmSqrtLog at hT
  simp only [div_eq_mul_inv,mul_assoc] at h hA hT hB ⊢
  linarith


/-- Actual prime-counting transfer retaining the exact prime-power correction. -/
theorem actual_pi_closed_GM (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    {x : ℝ} (hx : exp 8 ≤ x) :
    |primeCounting x-IEANTN.li x-(Chebyshev.psi x-x)/log x+
      (riemannPrimeCounting x-primeCounting x)| ≤
      14+(1386/5000:ℝ)*sqrt x/(log x)^2 := by
  convert actual_J_closed_GM hRH hGM hP hJ hx using 1 <;> ring

theorem actual_J_from_psi_profile (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 8 ≤ x)
    (hpsi : |Chebyshev.psi x-x| ≤ sqrt x*f (log x)) :
    |riemannPrimeCounting x-IEANTN.li x| ≤
      sqrt x/log x*f (log x)+14+(1386/5000:ℝ)*sqrt x/(log x)^2 := by
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<8)).trans_le hx
  have hl : 0 < log x := log_pos hx1
  have ht := actual_J_closed_GM hRH hGM hP hJ hx
  have hD : |(Chebyshev.psi x-x)/log x| ≤ sqrt x/log x*f (log x) := by
    rw [abs_div,abs_of_pos hl]
    have h := div_le_div_of_nonneg_right hpsi hl.le
    calc _ ≤ _ := h
      _ = _ := by ring
  have htri := abs_add_le
    (riemannPrimeCounting x-IEANTN.li x-(Chebyshev.psi x-x)/log x)
    ((Chebyshev.psi x-x)/log x)
  simp only [sub_add_cancel] at htri
  linarith

theorem actual_pi_signed_profile (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 8 ≤ x)
    (hpsi : |Chebyshev.psi x-x| ≤ sqrt x*f (log x)) :
    -(sqrt x/log x*f (log x)+14+(1386/5000:ℝ)*sqrt x/(log x)^2)-
      (riemannPrimeCounting x-primeCounting x) ≤ primeCounting x-IEANTN.li x ∧
    primeCounting x-IEANTN.li x ≤
      sqrt x/log x*f (log x)+14+(1386/5000:ℝ)*sqrt x/(log x)^2-
        (riemannPrimeCounting x-primeCounting x) := by
  have h := actual_J_from_psi_profile hRH hGM hP hJ f hx hpsi
  rw [abs_le] at h
  constructor <;> linarith [h.1,h.2]

theorem actual_pi_absolute_Li_profile (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (f : ℝ → ℝ) {x : ℝ} (hx : exp 8 ≤ x)
    (hpsi : |Chebyshev.psi x-x| ≤ sqrt x*f (log x)) :
    |primeCounting x-IEANTN.Li x| ≤
      sqrt x/log x*f (log x)+14+(1386/5000:ℝ)*sqrt x/(log x)^2+
        |IEANTN.li 2-(riemannPrimeCounting x-primeCounting x)| := by
  have hx1 : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<8)).trans_le hx
  have h := actual_J_from_psi_profile hRH hGM hP hJ f hx hpsi
  have hli := actual_li_Li_offset hx1
  have he : primeCounting x-IEANTN.Li x = (riemannPrimeCounting x-IEANTN.li x)+
      (IEANTN.li 2-(riemannPrimeCounting x-primeCounting x)) := by linarith
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

#print axioms actual_pi_closed_GM
#print axioms actual_pi_signed_profile
#print axioms actual_pi_absolute_Li_profile
#check @actual_J_closed_GM
#print axioms actual_J_closed_GM
end RHContinuation.Ramanujan
