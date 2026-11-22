import LiSeriesDerivative
import LiPVDefinition
import LeanCert.Tactic.IntervalAuto
namespace RHContinuation.Ramanujan
open Real Set Filter MeasureTheory RamanujanPV.AnalyticTransition
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"

noncomputable def liSeriesCore (x : ℝ) : ℝ := log (log x)+∑' n, eiTerm (log x) n
noncomputable def liSeriesConstant : ℝ := IEANTN.li 2-liSeriesCore 2

lemma eiTerm_summable (z : ℝ) : Summable (fun n => eiTerm z n) := by
  have hm := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial ‖z‖)
  apply hm.of_norm_bounded
  intro n
  unfold eiTerm
  change |z^(n+1)/((n+1:ℝ)*(Nat.factorial (n+1):ℝ))| ≤ _
  rw [abs_div,abs_pow,abs_mul,
    abs_of_pos (show (0:ℝ)<n+1 by positivity),
    abs_of_pos (show (0:ℝ)<(Nat.factorial (n+1):ℝ) by positivity)]
  have hn : (1:ℝ) ≤ n+1 := by linarith [(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]
  have hf : (0:ℝ) ≤ (Nat.factorial (n+1):ℝ) := by positivity
  have hp : (0:ℝ) ≤ ‖z‖^(n+1) := by positivity
  exact div_le_div_of_nonneg_left hp (by positivity) (by nlinarith)

lemma eiTerm_sum_bounds {z : ℝ} (hz : 0 ≤ z) :
    z ≤ ∑' n, eiTerm z n ∧ (∑' n, eiTerm z n) ≤ exp z-1 := by
  have hs := eiTerm_summable z
  have he := (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial z)
  have hshift := tsum_eq_zero_add' (f:=fun n : ℕ => z^n/(Nat.factorial n:ℝ)) he
  have hexp : exp z = 1+∑' n, z^(n+1)/(Nat.factorial (n+1):ℝ) := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    simpa using hshift
  have hterm : ∀ n, eiTerm z n ≤ z^(n+1)/(Nat.factorial (n+1):ℝ) := by
    intro n
    unfold eiTerm
    have hn : (1:ℝ) ≤ n+1 := by linarith [(Nat.cast_nonneg n : (0:ℝ)≤(n:ℝ))]
    have hf : (0:ℝ) ≤ (Nat.factorial (n+1):ℝ) := by positivity
    have hp : (0:ℝ) ≤ z^(n+1) := by positivity
    exact div_le_div_of_nonneg_left hp (by positivity) (by nlinarith)
  constructor
  · have h := hs.le_tsum 0 (fun n _ => eiTerm_nonneg hz n)
    simpa [eiTerm] using h
  · have h := hs.tsum_le_tsum hterm he
    linarith

lemma actual_li_two_bounds : (0:ℝ) ≤ IEANTN.li 2 ∧ IEANTN.li 2 ≤ 2 := by
  rw [li_pv_regularization (by norm_num : (1:ℝ)<2)]
  norm_num only [sub_self,show (2:ℝ)-1=1 by norm_num,log_one,add_zero]
  have hg0 : ∀ t : ℝ, 0 ≤ liRegularPositive t := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa only [liRegularPositive,ite_eq_left ht] using (liRegular_bounds ht).1
    · simp [liRegularPositive,ht]
  unfold liRegularPrimitive
  have hlo := intervalIntegral.integral_nonneg_of_forall (μ:=volume) (by norm_num : (0:ℝ)≤2)
    hg0
  have hup := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤2)
    (liRegularPositive_integrable 0 2) (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (1:ℝ)) volume 0 2)
    (fun t _ => (le_abs_self _).trans (liRegularPositive_norm t))
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hup
  exact ⟨hlo,hup⟩


/-- The genuine principal-value function has its Ei expansion with its own
additive constant. No identification of that constant with gamma is assumed. -/
theorem actual_li_relative_series {x : ℝ} (hx : 1 < x) :
    IEANTN.li x = liSeriesConstant+liSeriesCore x := by
  let F : ℝ → ℝ := fun y => IEANTN.li y-liSeriesCore y
  have hd : ∀ y ∈ Ioi (1:ℝ), HasDerivAt F 0 y := by
    intro y hy
    have h := (actual_li_hasDerivAt hy).sub (li_series_model_hasDerivAt 0 hy)
    convert! h using 1 <;> first | (funext t; simp [F,liSeriesCore]) | simp
  have hdiffer : DifferentiableOn ℝ F (Ioi (1:ℝ)) :=
    fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
  have hzero : EqOn (deriv F) 0 (Ioi (1:ℝ)) := by
    intro y hy
    exact (hd y hy).deriv
  have h := isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (1:ℝ)).isPreconnected
    hdiffer hzero hx (by norm_num : (2:ℝ) ∈ Ioi 1)
  dsimp [F,liSeriesConstant] at h ⊢
  linarith

/-- A coarse input-free interval for the integration constant is sufficient
for the factorial barriers; it does not assert the unproved gamma identity. -/
theorem liSeriesConstant_bounds : (-1:ℝ) ≤ liSeriesConstant ∧ liSeriesConstant ≤ 2 := by
  have hli := actual_li_two_bounds
  have hs := eiTerm_sum_bounds (show (0:ℝ)≤log 2 by positivity)
  rw [exp_log (by norm_num : (0:ℝ)<2)] at hs
  have hlo : (0:ℝ) ≤ log 2+log (log 2) := by
    interval_decide 80 (trust := kernel)
  have hup : log (log (2:ℝ)) ≤ 0 := by
    interval_decide 80 (trust := kernel)
  have hcore : (0:ℝ) ≤ liSeriesCore 2 ∧ liSeriesCore 2 ≤ 1 := by
    dsimp [liSeriesCore]
    constructor <;> linarith
  unfold liSeriesConstant
  constructor <;> linarith


lemma actual_li_two_upper : IEANTN.li 2 ≤ (3/2:ℝ) := by
  have hleft := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1)
    (liRegularPositive_integrable 0 1) (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (1:ℝ)) volume 0 1)
    (fun t _ => (le_abs_self _).trans (liRegularPositive_norm t))
  have hright := intervalIntegral.integral_mono_on (by norm_num : (1:ℝ)≤2)
    (liRegularPositive_integrable 1 2) (intervalIntegrable_const : IntervalIntegrable
      (fun _ : ℝ => (1/2:ℝ)) volume 1 2)
    (fun t ht => liRegularPositive_half ht.1)
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (liRegularPositive_integrable (0:ℝ) 1) (liRegularPositive_integrable 1 2)
  have he := li_pv_regularization (by norm_num : (1:ℝ)<2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hleft hright
  norm_num only [show (2:ℝ)-1=1 by norm_num,log_one,add_zero] at he
  unfold liRegularPrimitive at he
  linarith

lemma liSeriesConstant_upper_six_fifths : liSeriesConstant ≤ (6/5:ℝ) := by
  have hs := (eiTerm_sum_bounds (show (0:ℝ)≤log 2 by positivity)).1
  have hlo : (3/10:ℝ) ≤ log 2+log (log 2) := by
    interval_decide 80 (trust := kernel)
  have hcore : (3/10:ℝ) ≤ liSeriesCore 2 := by dsimp [liSeriesCore];linarith
  unfold liSeriesConstant
  linarith [actual_li_two_upper]


lemma actual_li_two_lower : (1/2:ℝ) ≤ IEANTN.li 2 := by
  have hleft := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) volume 0 1)
    (liRegularPositive_integrable 0 1)
    (fun t ht => liRegularPositive_lower_half ht.1 ht.2)
  have hg0 : ∀ t : ℝ, 0 ≤ liRegularPositive t := by
    intro t
    by_cases ht : 0 ≤ t
    · simpa only [liRegularPositive,ite_eq_left ht] using (liRegular_bounds ht).1
    · simp [liRegularPositive,ht]
  have hright := intervalIntegral.integral_nonneg_of_forall (μ:=volume)
    (by norm_num : (1:ℝ)≤2) hg0
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (liRegularPositive_integrable (0:ℝ) 1) (liRegularPositive_integrable 1 2)
  have he := li_pv_regularization (by norm_num : (1:ℝ)<2)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at hleft
  norm_num only [show (2:ℝ)-1=1 by norm_num,log_one,add_zero] at he
  unfold liRegularPrimitive at he
  linarith

lemma liSeriesConstant_lower_sixth : (-1/6:ℝ) ≤ liSeriesConstant := by
  have hs := (eiTerm_sum_bounds (show (0:ℝ)≤log 2 by positivity)).2
  rw [exp_log (by norm_num : (0:ℝ)<2)] at hs
  have hup : log (log (2:ℝ)) ≤ -1/3 := by
    interval_decide 80 (trust := kernel)
  have hcore : liSeriesCore 2 ≤ (2/3:ℝ) := by dsimp [liSeriesCore];linarith
  unfold liSeriesConstant
  linarith [actual_li_two_lower]

#print axioms eiTerm_summable
#print axioms actual_li_relative_series
#print axioms liSeriesConstant_lower_sixth
#print axioms liSeriesConstant_upper_six_fifths
end RHContinuation.Ramanujan
