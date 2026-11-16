import SynergyAnalytic.Laplace
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0

noncomputable def pairedFunctional (beta r L : ℝ) (Q : ℝ → ℝ) : ℝ :=
  Real.exp (-L*r)*Q (beta-r)+L*(∫ s in (beta-r)..beta, Real.exp (L*(s-beta))*Q s)

theorem pairedFactor_integral_form (D r L : ℝ) :
    pairedFactor D r L = Real.exp ((D-L)*r)+L*(∫ u in (0:ℝ)..r, Real.exp ((D-L)*u)) := by
  have hd : ∀ u : ℝ, HasDerivAt (fun v => Real.exp ((D-L)*v))
      ((D-L)*Real.exp ((D-L)*u)) u := by
    intro u
    convert (((hasDerivAt_id u).const_mul (D-L)).exp) using 1 <;>
      first | rfl | (norm_num;ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u hu => hd u)
    ((by fun_prop : Continuous (fun u : ℝ => (D-L)*Real.exp ((D-L)*u))).intervalIntegrable 0 r)
  rw [intervalIntegral.integral_const_mul] at he
  simp only [mul_zero,Real.exp_zero] at he
  unfold pairedFactor
  nlinarith

theorem pairedFunctional_exponential (c D beta r L : ℝ) :
    pairedFunctional beta r L (fun s => c*Real.exp (D*(beta-s))) = c*pairedFactor D r L := by
  have hbase : Real.exp (-L*r)*(c*Real.exp (D*(beta-(beta-r)))) = c*Real.exp ((D-L)*r) := by
    rw [mul_left_comm _ c,← Real.exp_add]
    congr 1
    ring
  have hi : (∫ s in (beta-r)..beta, Real.exp (L*(s-beta))*(c*Real.exp (D*(beta-s)))) =
      c*(∫ u in (0:ℝ)..r, Real.exp ((D-L)*u)) := by
    calc
      _ = ∫ s in (beta-r)..beta, c*Real.exp ((D-L)*(beta-s)) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change Real.exp (L*(s-beta))*(c*Real.exp (D*(beta-s))) = c*Real.exp ((D-L)*(beta-s))
        rw [mul_left_comm _ c,← Real.exp_add]
        congr 1
        ring
      _ = c*(∫ s in (beta-r)..beta, Real.exp ((D-L)*(beta-s))) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        have hv : (∫ s in (beta-r)..beta, Real.exp ((D-L)*(beta-s))) =
            ∫ u in (0:ℝ)..r, Real.exp ((D-L)*u) := by
          simpa only [sub_self,sub_sub_cancel] using
            (intervalIntegral.integral_comp_sub_left (fun u : ℝ => Real.exp ((D-L)*u))
              (a:=beta-r) (b:=beta) beta)
        rw [hv]
  unfold pairedFunctional
  rw [hbase,hi,pairedFactor_integral_form]
  ring

/-- A finite computational coefficient-vector replaces a two-dimensional
height/sigma quadrature by a sum of exact one-dimensional Laplace factors. -/
theorem pairedFunctional_sum_exponentials
    {ι : Type*} (S : Finset ι) (c D : ι → ℝ) (beta r L : ℝ) :
    pairedFunctional beta r L (fun s => ∑ j ∈ S, c j*Real.exp (D j*(beta-s))) =
      ∑ j ∈ S, c j*pairedFactor (D j) r L := by
  have hs : (∫ s in (beta-r)..beta, Real.exp (L*(s-beta))*(∑ j ∈ S, c j*Real.exp (D j*(beta-s)))) =
      ∑ j ∈ S, ∫ s in (beta-r)..beta, Real.exp (L*(s-beta))*(c j*Real.exp (D j*(beta-s))) := by
    calc
      _ = ∫ s in (beta-r)..beta, ∑ j ∈ S, Real.exp (L*(s-beta))*(c j*Real.exp (D j*(beta-s))) := by
        apply intervalIntegral.integral_congr
        intro s hx
        change Real.exp (L*(s-beta))*(∑ j ∈ S, c j*Real.exp (D j*(beta-s))) =
          ∑ j ∈ S, Real.exp (L*(s-beta))*(c j*Real.exp (D j*(beta-s)))
        rw [Finset.mul_sum]
      _ = _ := intervalIntegral.integral_finsetSum (by
        intro j hj
        exact (by fun_prop : Continuous (fun s : ℝ => Real.exp (L*(s-beta))*(c j*Real.exp (D j*(beta-s))))).intervalIntegrable _ _)
  unfold pairedFunctional
  rw [hs,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  exact pairedFunctional_exponential (c j) (D j) beta r L

theorem finite_profile_antitone
    {ι : Type*} (S : Finset ι) (c D : ι → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hc : ∀ j ∈ S, 0 ≤ c j) (hD : ∀ j ∈ S, 0 ≤ D j) :
    Antitone (fun L => ∑ j ∈ S, c j*pairedFactor (D j) r L) := by
  intro L K hLK
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (pairedFactor_antitone (hD j hj) hr hLK) (hc j hj)

#print axioms pairedFunctional_sum_exponentials
#print axioms finite_profile_antitone
end SynergyAnalytic
