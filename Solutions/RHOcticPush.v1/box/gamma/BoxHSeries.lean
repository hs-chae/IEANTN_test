import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Actual regular Dirichlet correction: convergence, continuity and value at zero. -/
namespace RHOcticPush.BoxGamma
open Real Set Filter Finset
open scoped Topology
set_option maxHeartbeats 0

noncomputable def hTerm (s : ℝ) (n : ℕ) : ℝ :=
  ((n:ℝ)+1)^(-1-s)/(4*((n:ℝ)+1)^2-1)
noncomputable def hSeries (s : ℝ) : ℝ := ∑' n : ℕ,hTerm s n

lemma hTerm_nonneg {s : ℝ} (n : ℕ) : 0≤hTerm s n := by
  have hn : (1:ℝ)≤(n:ℝ)+1 := by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  unfold hTerm
  apply div_nonneg (Real.rpow_nonneg (by positivity) _)
  nlinarith [sq_nonneg ((n:ℝ)+1)]

lemma hTerm_bound {s : ℝ} (hs : -1≤s) (n : ℕ) :
    ‖hTerm s n‖ ≤ 1/((n:ℝ)+1)^2 := by
  have hn : (1:ℝ)≤(n:ℝ)+1 := by nlinarith [(Nat.cast_nonneg n : (0:ℝ)≤n)]
  have hd : 0<4*((n:ℝ)+1)^2-1 := by nlinarith [sq_nonneg (n:ℝ)]
  rw [Real.norm_eq_abs,abs_of_nonneg (hTerm_nonneg n)]
  unfold hTerm
  calc
    _ ≤ 1/(4*((n:ℝ)+1)^2-1) := div_le_div_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)) hd.le
    _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg (n:ℝ)])

lemma hMajorant_summable : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  convert! h using 1
  funext n
  rw [abs_of_pos (by positivity : (0:ℝ)<(n:ℝ)+1),Real.rpow_two]

lemma hTerm_summable {s : ℝ} (hs : -1≤s) : Summable (hTerm s) :=
  hMajorant_summable.of_norm_bounded (fun n => hTerm_bound hs n)

lemma hSeries_continuousOn : ContinuousOn hSeries (Ici (-1:ℝ)) := by
  apply continuousOn_tsum
  · intro n
    unfold hTerm
    have hn : (0:ℝ)<(n:ℝ)+1 := by positivity
    have hn0 : (n:ℝ)+1 ≠ 0 := hn.ne'
    exact (by fun_prop : Continuous (fun s : ℝ => ((n:ℝ)+1)^(-1-s)/(4*((n:ℝ)+1)^2-1))).continuousOn
  · exact hMajorant_summable
  · exact fun n s hs => hTerm_bound hs n

lemma hSeries_continuousAt_zero : ContinuousAt hSeries 0 :=
  hSeries_continuousOn.continuousAt (Ici_mem_nhds (by norm_num : (-1:ℝ)<0))

lemma hTerm_partial_zero (N : ℕ) :
    (∑ n ∈ range N,hTerm 0 n) =
      2*(harmonic (2*N):ℝ)-2*(harmonic N:ℝ)+1/(2*(N:ℝ)+1)-1 := by
  induction N with
  | zero => norm_num [hTerm]
  | succ N ih =>
    rw [sum_range_succ,ih,show 2*(N+1)=(2*N+1)+1 by omega,
      harmonic_succ,harmonic_succ,harmonic_succ]
    unfold hTerm
    push_cast
    norm_num only [zero_sub,sub_zero,Real.rpow_neg_one]
    have hd : 4*((N:ℝ)+1)^2-1 ≠ 0 := by nlinarith [(Nat.cast_nonneg N : (0:ℝ)≤N)]
    rw [show 4*((N:ℝ)+1)^2-1=(2*(N:ℝ)+1)*(2*(N:ℝ)+3) by ring]
    field_simp
    ring

lemma harmonic_double_limit :
    Tendsto (fun N : ℕ => (harmonic (2*N):ℝ)-(harmonic N:ℝ)) atTop (𝓝 (log 2)) := by
  have hN : Tendsto (fun N : ℕ => 2*N) atTop atTop :=
    tendsto_atTop.mpr (fun b => eventually_atTop.mpr ⟨b,by intro n hn;omega⟩)
  have h := ((Real.tendsto_harmonic_sub_log.comp hN).sub Real.tendsto_harmonic_sub_log).add_const (log 2)
  simp only [sub_self,zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN0
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN0.ne'
  dsimp only [Function.comp_apply]
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num) hn]
  ring

/-- The complete correction series, not a finite truncation, has this exact value. -/
theorem hSeries_zero : hSeries 0 = 2*log 2-1 := by
  have hi : Tendsto (fun N : ℕ => (2*(N:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_inv_atTop_zero.comp
    exact Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2)) tendsto_const_nhds
  have h := ((harmonic_double_limit.const_mul 2).add hi).sub_const 1
  simp only [add_zero] at h
  have he : Tendsto (fun N => ∑ n ∈ range N,hTerm 0 n) atTop (𝓝 (2*log 2-1)) := by
    apply h.congr'
    exact Eventually.of_forall (fun N => by dsimp only;rw [hTerm_partial_zero];ring)
  exact tendsto_nhds_unique (hTerm_summable (by norm_num : (-1:ℝ)≤0)).hasSum.tendsto_sum_nat he

#print axioms hSeries_continuousAt_zero
#print axioms hSeries_zero
end RHOcticPush.BoxGamma
