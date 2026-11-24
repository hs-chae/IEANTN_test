import StieltjesRegular
import StieltjesDerivative

/-! Actual identification of the canonical Stieltjes limit with the first
regular-zeta derivative. All limits, interchanges and finite sums are proved;
there is no assumed Laurent coefficient or unverified numerical input. -/
namespace RHOcticPush.StieltjesZeta
open Real Set MeasureTheory Filter Finset
open scoped Topology
set_option maxHeartbeats 0

lemma termDerivative_summable : Summable (fun n : ℕ => termDerivative (n+1) 1) := by
  have hr : Summable (fun n : ℕ => (n:ℝ)^(-3/2:ℝ)) :=
    summable_nat_rpow.mpr (by norm_num)
  have hu : Summable (fun n : ℕ => 4*(((n+1:ℕ):ℝ))^(-3/2:ℝ)) :=
    ((summable_nat_add_iff 1).mpr hr).mul_left 4
  exact Summable.of_norm_bounded hu (fun n => termDerivative_bound (by omega) (by norm_num))

lemma coefficient_as_derivative (n : ℕ) (hn : 0<n) :
    coefficient n = ZetaAsymptotics.term n 1 + termDerivative n 1 := by
  have hd : IntervalIntegrable (derivativePacket n 1) volume (n:ℝ) (n+1) := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hp : 0<x := positive_on_unit n hn hx
    unfold derivativePacket
    exact ((((continuousAt_id.sub continuousAt_const).neg).mul
      (Real.continuousAt_log hp.ne')).mul
        (continuousAt_id.rpow_const (Or.inl hp.ne'))).continuousWithinAt
  unfold coefficient ZetaAsymptotics.term termDerivative
  rw [← intervalIntegral.integral_add (ZetaAsymptotics.term_welldef hn (by norm_num)) hd]
  apply intervalIntegral.integral_congr
  intro x hx
  have hp : 0<x := positive_on_unit n hn hx
  unfold derivativePacket
  norm_num [Real.rpow_neg hp.le]
  ring

theorem gamma1_eq_term_series : BoxMellinInputs.v1.gamma1 =
    ZetaAsymptotics.termTSum 1 + ∑' n : ℕ, termDerivative (n+1) 1 := by
  have hc : Summable (fun n : ℕ => coefficient (n+1)) :=
    (ZetaAsymptotics.term_tsum_one.summable.add termDerivative_summable).congr
      (fun n => (coefficient_as_derivative (n+1) (by omega)).symm)
  have hseq := RHLimit.Stieltjes.stieltjes_trapezoid.1.comp (tendsto_add_atTop_nat 1)
  have heq : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,coefficient (n+1))
      atTop (𝓝 BoxMellinInputs.v1.gamma1) := by
    convert! hseq using 1
    ext N
    exact coefficient_sum N
  have hsum : (∑' n : ℕ,coefficient (n+1)) = BoxMellinInputs.v1.gamma1 :=
    tendsto_nhds_unique hc.hasSum.tendsto_sum_nat heq
  rw [← hsum]
  rw [tsum_congr (fun n => coefficient_as_derivative (n+1) (by omega))]
  rw [ZetaAsymptotics.term_tsum_one.summable.tsum_add termDerivative_summable]
  rfl

/-- The actual regular-zeta derivative at1, identified through a complete
Euler-summation/derivative-series argument and the canonical sequence limit. -/
theorem realRegular_hasDerivAt : HasDerivAt realRegular (-BoxMellinInputs.v1.gamma1) 1 := by
  have ht : HasDerivAt (fun s : ℝ => 1-s*ZetaAsymptotics.termTSum s)
      (-(ZetaAsymptotics.termTSum 1+∑' n : ℕ,termDerivative (n+1) 1)) 1 := by
    convert! ((hasDerivAt_id (1:ℝ)).mul actual_termTSum_hasDerivAt).const_sub 1 using 1 <;>
      simp only [id_eq,one_mul,Pi.mul_apply]
  have hw : HasDerivWithinAt realRegular
      (-(ZetaAsymptotics.termTSum 1+∑' n : ℕ,termDerivative (n+1) 1)) (Set.Ici 1) 1 :=
    ht.hasDerivWithinAt.congr_of_mem (fun s hs => realRegular_eq_termTSum hs)
      (show (1:ℝ)∈Set.Ici 1 by simp)
  have hr := (realRegular_differentiable (1:ℝ)).hasDerivAt
  have hv : deriv realRegular 1 = -BoxMellinInputs.v1.gamma1 := by
    have hleft := hr.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici (1:ℝ))
    have hright := hw.derivWithin (uniqueDiffWithinAt_Ici (1:ℝ))
    rw [← gamma1_eq_term_series] at hright
    exact hleft.symm.trans hright
  exact hr.congr_deriv hv

/-- No-argument special-function input consumed by the actual Box J1 proof. -/
theorem regularizedZeta_hasDerivAt :
    HasDerivAt regularizedZeta (-BoxMellinInputs.v1.gamma1) 0 := by
  have hg : HasDerivAt (fun s : ℝ => 1+s) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add 1
  have hr : HasDerivAt realRegular (-BoxMellinInputs.v1.gamma1) ((fun s : ℝ => 1+s) 0) := by
    simpa only [add_zero] using realRegular_hasDerivAt
  have h := hr.comp 0 hg
  convert! h using 1
  · ext s
    simp [realRegular,regularizedZeta,Function.comp_apply]
  · ring

#print axioms coefficient_as_derivative
#print axioms gamma1_eq_term_series
#print axioms realRegular_hasDerivAt
#print axioms regularizedZeta_hasDerivAt
end RHOcticPush.StieltjesZeta
