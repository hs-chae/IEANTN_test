import FullRH
import RamanujanPV.CriticalSourceClosed
import RamanujanPV.FiniteExpLinked

open Real Set IEANTN RamanujanPV
namespace RealCrossing
set_option maxRecDepth 10000

def A : ℝ := 38358837682
def B : ℝ := 38358837683
noncomputable def f (x : ℝ) : ℝ := exp 1 * x / log x * 632207037 - 1644673232^2

/-- The two inherited source-linked counts give an exact real formula on
the entire critical unit, not just on the integer endpoints. -/
theorem on_unit {x : ℝ} (hx : x ∈ Icc A B) : gap x = f x := by
  have hP := QuotientCCell.source_execution_count CriticalSourceClosed.p_source
  have hQ := QuotientCCell.source_execution_count CriticalSourceClosed.q_source
  have hpc := FirstCriticalCell.preceding_count
  change Nat.primeCounting 38358837682 = Nat.primeCounting 38358837683 at hpc
  have hxp : (38358837682:ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by simpa [A] using hx.1)
  have hxq : ⌊x⌋₊ ≤ (38358837683:ℕ) := Nat.floor_le_of_le (by simpa [B] using hx.2)
  have hf : ⌊x⌋₊ = 38358837682 ∨ ⌊x⌋₊ = 38358837683 := by omega
  have hπ : primeCounting x = 1644673232 := by
    unfold primeCounting
    rcases hf with hh | hh
    · rw [hh,hpc,hP]; norm_num
    · rw [hh,hP]; norm_num
  let heap : QuotientCMachine.Heap := fun _ ↦ none
  have he := FiniteExpLinked.source_outputs_enclose_e
    (FiniteExpExecute.low_function_executes heap) (FiniteExpLinked.linked_high_executes heap)
  change (3133965575612453533:ℝ)/(2:ℝ)^60 ≤ exp 1 ∧
    exp 1 ≤ (3133965575612453555:ℝ)/(2:ℝ)^60 at he
  have hj0 : (14111427770:ℝ) ≤ x/exp 1 := by
    apply (le_div_iff₀ (exp_pos 1)).2
    have hh := mul_le_mul_of_nonneg_left he.2 (by norm_num : (0:ℝ) ≤ 14111427770)
    exact hh.trans ((by norm_num [A] : (14111427770:ℝ) *
      ((3133965575612453555:ℝ)/(2:ℝ)^60) ≤ A).trans hx.1)
  have hj1 : x/exp 1 < (14111427770:ℝ)+1 := by
    apply (div_lt_iff₀ (exp_pos 1)).2
    have hh := mul_le_mul_of_nonneg_left he.1 (by norm_num : (0:ℝ) ≤ 14111427770+1)
    exact hx.2.trans_lt ((by norm_num [B] : B < (14111427770+1:ℝ) *
      ((3133965575612453533:ℝ)/(2:ℝ)^60)).trans_le hh)
  have hj : ⌊x/exp 1⌋₊ = (14111427770:ℕ) := by
    apply (Nat.floor_eq_iff (by linarith : 0 ≤ x/exp 1)).2
    push_cast
    exact ⟨hj0,hj1⟩
  have hπj : primeCounting (x/exp 1) = 632207037 := by
    unfold primeCounting
    rw [hj,hQ]
    norm_num
  unfold gap f
  rw [hπj,hπ]

theorem log_one_lt {x : ℝ} (hx : x ∈ Icc A B) : 1 < log x := by
  apply (lt_log_iff_exp_lt (by linarith [hx.1,show (0:ℝ) < A by norm_num [A]])).2
  have hA : (3:ℝ) ≤ A := by norm_num [A]
  exact exp_one_lt_three.trans_le (hA.trans hx.1)

theorem continuous_unit : ContinuousOn f (Icc A B) := by
  have hlog : ContinuousOn log (Icc A B) := by
    apply continuousOn_log.mono
    intro x hx
    exact (Set.mem_compl_iff _ _).2 (by
      intro hh
      have hz : x = 0 := Set.mem_singleton_iff.mp hh
      linarith [hx.1,show (0:ℝ) < A by norm_num [A]])
  exact (((continuousOn_const.mul continuousOn_id).div hlog
    (fun x hx => by linarith [log_one_lt hx])).mul continuousOn_const).sub continuousOn_const

theorem strict_unit : StrictMonoOn f (Icc A B) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc A B) continuous_unit
  intro x hx
  have hx' := interior_subset hx
  have hx0 : x ≠ 0 := by linarith [show (0:ℝ) < A by norm_num [A], (mem_Icc.mp hx').1]
  have hl := log_one_lt hx'
  have H := ((((hasDerivAt_id x).const_mul (exp 1)).div (hasDerivAt_log hx0)
    (by linarith : log x ≠ 0)).mul_const (632207037:ℝ)).sub_const (1644673232^2)
  change HasDerivAt f _ x at H
  rw [H.deriv]
  have hxdiv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  have hp : 0 < exp 1 * (log x - 1) := mul_pos (exp_pos _) (by linarith)
  have hc : exp 1 * x * x⁻¹ = exp 1 := by rw [mul_assoc,hxdiv,mul_one]
  simp only [id_eq,mul_one]
  rw [hc]
  exact mul_pos (div_pos (by linarith) (by positivity)) (by norm_num)

theorem zero_in_unit :
    ∃ z ∈ Ioo A B, gap z = 0 ∧ (∀ x ∈ Icc A B, 0 < gap x ↔ z < x) := by
  have hAB : A < B := by norm_num [A,B]
  have hA : f A < 0 := by
    rw [← on_unit (x:=A) ⟨le_rfl,hAB.le⟩]
    exact CriticalSourceClosed.preceding_counterexample
  have hB : 0 < f B := by
    rw [← on_unit (x:=B) ⟨hAB.le,le_rfl⟩]
    exact lt_trans (by norm_num) (CriticalSourceClosed.first_critical_margin (x:=B)
      (by norm_num [B]) (by norm_num [B]))
  obtain ⟨z,hz,hfz⟩ := intermediate_value_Icc hAB.le continuous_unit
    (show (0:ℝ) ∈ Icc (f A) (f B) from ⟨hA.le,hB.le⟩)
  have hz1 : A < z := lt_of_le_of_ne hz.1 (by
    intro h; rw [← h] at hfz; linarith)
  have hz2 : z < B := lt_of_le_of_ne hz.2 (by
    intro h; rw [h] at hfz; linarith)
  refine ⟨z,⟨hz1,hz2⟩, (on_unit hz).trans hfz, ?_⟩
  intro x hx
  rw [on_unit hx,←hfz]
  exact strict_unit.lt_iff_lt hz hx

/-- Conditional global assembly. The large-ray proof supplied in prose is not
claimed as a Lean provider; published finite coverage is a separate argument. -/
theorem last_real (hRH : SharedRH.hypothesis)
    (finite : ∀ x ∈ Icc B (exp 103), 0 < gap x)
    (ray : SharedRH.hypothesis → ∀ x ≥ (640000000000:ℝ), 0 < gap x) :
    ∃ z ∈ Ioo A B, gap z = 0 ∧ ∀ x > z, 0 < gap x := by
  obtain ⟨z,hz,hg,hloc⟩ := zero_in_unit
  refine ⟨z,hz,hg,?_⟩
  intro x hzx
  by_cases hx : x ≤ B
  · exact (hloc x ⟨hz.1.le.trans hzx.le,hx⟩).2 hzx
  by_cases hx103 : x ≤ exp 103
  · exact finite x ⟨le_of_not_ge hx,hx103⟩
  · have hdom : (640000000000:ℝ) ≤ exp 103 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) exp_one_gt_two.le 103
      rw [exp_one_pow] at hh
      norm_num at hh
      linarith
    exact ray hRH x (hdom.trans (le_of_not_ge hx103))

#print axioms on_unit
#print axioms zero_in_unit
#print axioms last_real
end RealCrossing
