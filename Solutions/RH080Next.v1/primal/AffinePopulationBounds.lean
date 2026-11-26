import ExplicitAffineIntegrals
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
namespace RH080Next.Primal
open RH080Next.Explicit

private def ramp (x : ℝ) : ℝ := max 0 x-max 0 (x-1)
private lemma ramp_nonneg (x : ℝ) : 0≤ramp x := by
  unfold ramp
  apply sub_nonneg.mpr
  exact max_le_max le_rfl (by linarith)
private lemma ramp_le_one (x : ℝ) : ramp x≤1 := by
  unfold ramp
  simp only [max_def]
  split_ifs <;> linarith
private lemma hat_eq_ramp_sub (x : ℝ) : hat x=ramp (x+1)-ramp x := by
  unfold hat ramp
  simp only [abs, max_def]
  split_ifs <;> linarith

private def hatSum (N : ℕ) (t : ℝ) : ℝ :=
  hat t+∑ j ∈ Finset.Ico 1 N, (hat (t-j)+hat (t+j))

private theorem hatSum_eq (n : ℕ) (t : ℝ) :
    hatSum (n+1) t=ramp (t+((n+1 : ℕ) : ℝ))-ramp (t-(n : ℝ)) := by
  induction n with
  | zero => simpa [hatSum] using hat_eq_ramp_sub t
  | succ n ih =>
    unfold hatSum at ih ⊢
    rw [Finset.sum_Ico_succ_top (by omega : 1≤n+1)]
    rw [← add_assoc, ih]
    rw [hat_eq_ramp_sub (t-((n+1 : ℕ) : ℝ)), hat_eq_ramp_sub (t+((n+1 : ℕ) : ℝ))]
    have h1 : t-((n+1 : ℕ) : ℝ)+1=t-(n : ℝ) := by push_cast; ring
    have h2 : t+((n+1 : ℕ) : ℝ)+1=t+((n+1+1 : ℕ) : ℝ) := by push_cast; ring
    rw [h1,h2]
    ring

theorem hat_partition_upper (N : ℕ) (hN : 1≤N) (t : ℝ) :
    hat t+∑ j ∈ Finset.Ico 1 N, (hat (t-j)+hat (t+j)) ≤1 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  change hatSum (n+1) t≤1
  rw [hatSum_eq]
  linarith [ramp_nonneg (t-(n : ℝ)),ramp_le_one (t+((n+1 : ℕ) : ℝ))]

/-- The actual affine spectrum never exceeds the largest nodal absolute value.
This derives the interpolation bound from its finite hat syntax. -/
theorem affineSpectrum_abs_le (nodes : List ℚ) (m : ℕ) (M : ℝ)
    (hlen : 2≤nodes.length) (hM : 0≤M)
    (hnode : ∀ j : ℕ, j<nodes.length-1 → |node nodes j|≤M) (v : ℝ) :
    |affineSpectrum nodes m v|≤M := by
  have h0 := hnode 0 (by omega)
  have hfirst := mul_le_mul_of_nonneg_right h0 (hat_nonneg ((m : ℝ)*v))
  have hsum : (∑ j ∈ Finset.Ico 1 (nodes.length-1),
      |node nodes j| *(hat ((m : ℝ)*v-j)+hat ((m : ℝ)*v+j))) ≤
      ∑ j ∈ Finset.Ico 1 (nodes.length-1),
        M*(hat ((m : ℝ)*v-j)+hat ((m : ℝ)*v+j)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hnode j (Finset.mem_Ico.mp hj).2)
      (add_nonneg (hat_nonneg _) (hat_nonneg _))
  calc
    _ ≤ absoluteSpectrum nodes m v := abs_affineSpectrum_le_absoluteSpectrum nodes m v
    _ ≤ M*hat ((m : ℝ)*v)+∑ j ∈ Finset.Ico 1 (nodes.length-1),
        M*(hat ((m : ℝ)*v-j)+hat ((m : ℝ)*v+j)) := add_le_add hfirst hsum
    _ = M*(hat ((m : ℝ)*v)+∑ j ∈ Finset.Ico 1 (nodes.length-1),
        (hat ((m : ℝ)*v-j)+hat ((m : ℝ)*v+j))) := by rw [mul_add, Finset.mul_sum]
    _ ≤ M*1 := mul_le_mul_of_nonneg_left
      (hat_partition_upper (nodes.length-1) (by omega) ((m : ℝ)*v)) hM
    _ = M := mul_one M

/-- Beyond the unit endpoint, this supported family has just its boundary hat. -/
theorem affineSpectrum_right_single_boundary (nodes : List ℚ) (m : ℕ)
    (hm : 0<m) (hmN : m<nodes.length-1)
    (hzero : ∀ j : ℕ, m<j → node nodes j=0) (v : ℝ) (hv : 1<v) :
    affineSpectrum nodes m v=node nodes m*hat ((m : ℝ)*v-m) := by
  have hmr : (0 : ℝ)<m := by exact_mod_cast hm
  have hmx : (m : ℝ)<m*v := by nlinarith
  have hm1 : (1 : ℝ)≤m := by exact_mod_cast hm
  have hcenter : hat ((m : ℝ)*v)=0 :=
    hat_eq_zero _ ((by linarith : (1 : ℝ)≤m*v).trans (le_abs_self _))
  have hplus (j : ℕ) : hat ((m : ℝ)*v+j)=0 := by
    apply hat_eq_zero
    apply le_trans _ (le_abs_self _)
    have hj : (0 : ℝ)≤j := Nat.cast_nonneg _
    linarith
  unfold affineSpectrum
  rw [hcenter,mul_zero,zero_add,Finset.sum_eq_single m]
  · rw [hplus,add_zero]
  · intro j hj hne
    rcases lt_or_gt_of_ne hne with hjm | hmj
    · have hjr : (j : ℝ)+1≤m := by exact_mod_cast hjm
      have hminus : hat ((m : ℝ)*v-j)=0 := by
        apply hat_eq_zero
        apply le_trans _ (le_abs_self _)
        linarith
      rw [hminus,hplus,add_zero,mul_zero]
    · rw [hzero j hmj,zero_mul]
  · intro hn
    exact False.elim (hn (Finset.mem_Ico.mpr ⟨hm,hmN⟩))

private theorem integral_hat_positive_half : (∫ u in Ioi (0 : ℝ), hat u)=1/2 := by
  have h := integral_comp_abs (f := hat)
  have he (u : ℝ) : hat |u|=hat u := by simp [hat]
  simp_rw [he] at h
  rw [integral_hat] at h
  linarith

private theorem integral_boundary_hat (m : ℝ) (hm : 0<m) :
    (∫ v in Ioi (1 : ℝ), hat (m*v-m))=1/(2*m) := by
  rw [←integral_indicator measurableSet_Ioi]
  have he : (Ioi (1 : ℝ)).indicator (fun v : ℝ => hat (m*v-m)) =
      fun v : ℝ => (Ioi (0 : ℝ)).indicator (fun u : ℝ => hat (m*u)) (v-1) := by
    funext v
    by_cases hv : 1<v
    · have hv' : (0 : ℝ)<v-1 := by linarith
      rw [indicator_of_mem (show v∈Ioi (1 : ℝ) from hv),
        indicator_of_mem (show v-1∈Ioi (0 : ℝ) from hv')]
      congr 1
      ring
    · have hv' : ¬(0 : ℝ)<v-1 := by linarith
      rw [indicator_of_notMem (show v∉Ioi (1 : ℝ) from hv),
        indicator_of_notMem (show v-1∉Ioi (0 : ℝ) from hv')]
  rw [he,integral_sub_right_eq_self,integral_indicator measurableSet_Ioi,
    integral_comp_mul_left_Ioi hat 0 hm,mul_zero,integral_hat_positive_half]
  simp only [smul_eq_mul]
  ring

/-- Exact even-spectrum exterior splitting, without Fourier-L1 or inversion assumptions. -/
theorem exterior_positive_integral_even (f : ℝ → ℝ) (heven : Function.Even f) :
    (∫ v in {v : ℝ | 1< |v| }, max 0 (f v)) =
      2*(∫ v in Ioi (1 : ℝ), max 0 (f v)) := by
  have habs (v : ℝ) : f |v|=f v := by
    by_cases hv : 0≤v
    · rw [abs_of_nonneg hv]
    · rw [abs_of_neg (lt_of_not_ge hv),heven v]
  have hs : MeasurableSet {v : ℝ | 1< |v| } :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [←integral_indicator hs]
  have he : ({v : ℝ | 1< |v| }).indicator (fun v => max 0 (f v)) =
      fun v : ℝ => (Ioi (1 : ℝ)).indicator (fun v => max 0 (f v)) |v| := by
    funext v
    simp only [Set.indicator_apply,mem_ofPred_eq,mem_Ioi,habs]
  rw [he,integral_comp_abs,setIntegral_indicator measurableSet_Ioi]
  have hi : Ioi (0 : ℝ)∩Ioi 1=Ioi 1 := by
    apply inter_eq_right.mpr
    intro x hx
    change (1 : ℝ)<x at hx
    change (0 : ℝ)<x
    linarith
  rw [hi]

/-- Exact positive leakage for the single exterior boundary node. Interior nodes
may be arbitrary. This covers the actual small population source input. -/
theorem affineSpectrum_single_boundary_leak (nodes : List ℚ) (m : ℕ)
    (hm : 0<m) (hmN : m<nodes.length-1)
    (hzero : ∀ j : ℕ, m<j → node nodes j=0) (hboundary : 0≤node nodes m) :
    (∫ v in {v : ℝ | 1< |v| }, max 0 (affineSpectrum nodes m v)) = node nodes m/m := by
  rw [exterior_positive_integral_even _ (affineSpectrum_even nodes m)]
  have he : (∫ v in Ioi (1 : ℝ), max 0 (affineSpectrum nodes m v)) =
      node nodes m*(∫ v in Ioi (1 : ℝ), hat ((m : ℝ)*v-m)) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [affineSpectrum_right_single_boundary nodes m hm hmN hzero v hv,
      max_eq_right (mul_nonneg hboundary (hat_nonneg _))]
  rw [he,integral_boundary_hat m (by exact_mod_cast hm)]
  ring

#print axioms hat_partition_upper
#print axioms affineSpectrum_abs_le
#print axioms affineSpectrum_right_single_boundary
#print axioms exterior_positive_integral_even
#print axioms affineSpectrum_single_boundary_leak
end RH080Next.Primal
