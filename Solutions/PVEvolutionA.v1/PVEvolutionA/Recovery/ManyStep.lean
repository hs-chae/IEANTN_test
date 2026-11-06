/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.StepMoment

namespace PVEvolutionA.Recovery.ManyStep
open Real Set MeasureTheory Filter Topology
open WinnerDensityA.Piecewise
set_option maxHeartbeats 0

/-- The finite profile frontier, written so every integral correction has its
proper subtraction sign. The number of profiles is an explicit parameter. -/
noncomputable def coefficient (a c : ℕ→ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  c 0-∑j∈Finset.range n, if a (j+1)≤t then c j-c (j+1) else 0

noncomputable def majorant (a c : ℕ→ℝ) (n : ℕ) (p q d t : ℝ) : ℝ :=
  coefficient a c n t*t^p*log t^q+d*log t^(2:ℕ)

theorem coefficient_at {a c : ℕ→ℝ} {n k : ℕ} {t : ℝ} (hk : k≤n)
    (hcut : ∀j<n,a (j+1)≤t ↔ j<k) : coefficient a c n t=c k := by
  have he : (∑j∈Finset.range n,if a (j+1)≤t then c j-c (j+1) else 0)=
      ∑ j ∈ Finset.range k, (c j-c (j+1)) := by
    have hsub : Finset.range k⊆Finset.range n := Finset.range_mono hk
    have hs := Finset.sum_subset (f:=fun j=>if a (j+1)≤t then c j-c (j+1) else 0) hsub
      (by
        intro j hj hnot
        have hn : ¬j<k := by simpa only [Finset.mem_range] using hnot
        rw [if_neg (fun h=>hn ((hcut j (Finset.mem_range.mp hj)).mp h))])
    rw [←hs]
    apply Finset.sum_congr rfl
    intro j hj
    rw [if_pos ((hcut j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)).mpr
      (Finset.mem_range.mp hj))]
  unfold coefficient
  rw [he,Finset.sum_range_sub']
  ring

/-- At any height at least the first anchor, an actual applicable profile
produces this frontier. No monotonicity of the density function is assumed. -/
theorem exists_selected {a c : ℕ→ℝ} (ha : Monotone a) {n : ℕ} {t : ℝ}
    (ht : a 0≤t) : ∃k,k≤n ∧ a k≤t ∧ coefficient a c n t=c k := by
  classical
  let S := (Finset.range (n+1)).filter fun j=>a j≤t
  have hS : S.Nonempty := ⟨0,by simp [S,ht]⟩
  let k := S.max' hS
  have hkmem : k∈S := Finset.max'_mem S hS
  obtain ⟨hkr,hkt⟩ := Finset.mem_filter.mp hkmem
  have hkn : k≤n := by have hh:=Finset.mem_range.mp hkr;omega
  refine ⟨k,hkn,hkt,coefficient_at hkn ?_⟩
  intro j hj
  constructor
  · intro hjt
    have hmem : j+1∈S := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega),hjt⟩
    have hh := Finset.le_max' S (j+1) hmem
    change j+1≤k at hh
    omega
  · intro hjk
    exact (ha (by omega : j+1≤k)).trans hkt

theorem integrand_decomposition (a c : ℕ→ℝ) (n : ℕ) (p q d : ℝ) :
    (fun t=>majorant a c n p q d t/t^2)=fun t=>
      c 0*integrand p q t-
      (∑j∈Finset.range n,(c j-c (j+1))*cut p q (a (j+1)) t)+d*integrand 0 2 t := by
  funext t
  unfold majorant coefficient
  have he : ((∑j∈Finset.range n,if a (j+1)≤t then c j-c (j+1) else 0)*t^p*log t^q)/t^2 =
      ∑j∈Finset.range n,(c j-c (j+1))*cut p q (a (j+1)) t := by
    rw [Finset.sum_mul,Finset.sum_mul,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold cut integrand
    split_ifs <;> ring
  unfold integrand
  rw [show (t:ℝ)^(0:ℝ)=1 by simp,show log t^(2:ℝ)=log t^(2:ℕ) by rw [rpow_two]]
  rw [←he]
  ring

theorem integrable {a c : ℕ→ℝ} {n : ℕ} {p q d A : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : q≤4) :
    IntegrableOn (fun t=>majorant a c n p q d t/t^2) (Ioi A) := by
  have hi := integrand_integrable hA hl hp hp' hq
  have hj := integrand_integrable hA hl (p:=0) (q:=2) (by norm_num) (by norm_num) (by norm_num)
  rw [integrand_decomposition]
  apply ((hi.const_mul (c 0)).sub ?_).add (hj.const_mul d)
  exact integrable_finset_sum (Finset.range n) fun j _ =>
    (cut_integrable (a:=a (j+1)) hi).const_mul (c j-c (j+1))

theorem integral_eq {a c : ℕ→ℝ} {n : ℕ} {p q d A : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : q≤4)
    (ha : ∀j<n,A<a (j+1)) :
    (∫t in Ioi A,majorant a c n p q d t/t^2)=
      c 0*(∫t in Ioi A,integrand p q t)-
      (∑j∈Finset.range n,(c j-c (j+1))*(∫t in Ioi (a (j+1)),integrand p q t))+
      d*(∫t in Ioi A,integrand 0 2 t) := by
  have hi := integrand_integrable hA hl hp hp' hq
  have hj := integrand_integrable hA hl (p:=0) (q:=2) (by norm_num) (by norm_num) (by norm_num)
  have hcuts : ∀j∈Finset.range n,IntegrableOn
      (fun t=>(c j-c (j+1))*cut p q (a (j+1)) t) (Ioi A) := by
    intro j _
    exact (cut_integrable (a:=a (j+1)) hi).const_mul _
  have hsum := integrable_finset_sum (Finset.range n) hcuts
  rw [integrand_decomposition]
  have e0 := integral_add ((hi.const_mul (c 0)).sub hsum) (hj.const_mul d)
  have e1 := integral_sub (hi.const_mul (c 0)) hsum
  simp only [Pi.sub_apply] at e0 e1
  rw [e0,e1,integral_const_mul,integral_const_mul,
    integral_finset_sum (Finset.range n) hcuts]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,cut_integral (ha j (Finset.mem_range.mp hj))]

noncomputable def budget (a c : ℕ→ℝ) (n : ℕ) (p q d A : ℝ) : ℝ :=
  c 0*upper p q A-(∑j∈Finset.range n,(c j-c (j+1))*lower p q (a (j+1)))+
    d*((log A^(2:ℕ)+2*log A+2)/A)

theorem integral_upper {a c : ℕ→ℝ} {n : ℕ} {p q d A : ℝ}
    (hA : 1<A) (hl : 1≤log A) (hp : 0≤p) (hp' : p<1) (hq : 3≤q) (hq' : q≤4)
    (ha : ∀j<n,A<a (j+1)) (hc0 : 0≤c 0) (hc : ∀j<n,c (j+1)≤c j) :
    (∫t in Ioi A,majorant a c n p q d t/t^2)≤budget a c n p q d A := by
  rw [integral_eq hA hl hp hp' hq' ha,log_square_integral hA hl]
  have h0 := mul_le_mul_of_nonneg_left
    (WinnerDensityA.Piecewise.integral_upper hA hl hp hp' hq hq') hc0
  have hs : (∑j∈Finset.range n,(c j-c (j+1))*lower p q (a (j+1)))≤
      ∑j∈Finset.range n,(c j-c (j+1))*(∫t in Ioi (a (j+1)),integrand p q t) := by
    apply Finset.sum_le_sum
    intro j hj
    have hja := ha j (Finset.mem_range.mp hj)
    have hja1 : 1<a (j+1) := hA.trans hja
    have hlog : 1≤log (a (j+1)) := hl.trans (log_le_log (by linarith) hja.le)
    exact mul_le_mul_of_nonneg_left
      (WinnerDensityA.Piecewise.integral_lower hja1 hlog hp hp' hq hq')
      (sub_nonneg.mpr (hc j (Finset.mem_range.mp hj)))
  unfold budget
  linarith

theorem coefficient_above {a c : ℕ→ℝ} (ha : Monotone a) {n : ℕ} {t : ℝ}
    (ht : a n≤t) : coefficient a c n t=c n := by
  apply coefficient_at (le_refl n)
  intro j hj
  exact ⟨fun _=>hj,fun _=>(ha (by omega : j+1≤n)).trans ht⟩

theorem boundary_zero {a c : ℕ→ℝ} (ha : Monotone a) {n : ℕ} {p q d : ℝ}
    (hp : p<1) : Tendsto (fun t=>majorant a c n p q d t/t) atTop (𝓝 0) := by
  have h1 := (boundary_tendsto_zero (q:=q) hp).const_mul (c n)
  have h2 := (boundary_tendsto_zero (p:=0) (q:=2) (by norm_num)).const_mul d
  have hh := h1.add h2
  simp only [mul_zero,zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (a n),eventually_gt_atTop (0:ℝ)] with t ht ht0
  rw [rpow_sub ht0,rpow_one,show (0:ℝ)-1= -1 by norm_num,rpow_neg_one,rpow_two]
  simp only [majorant,coefficient_above ha ht]
  ring

#print axioms exists_selected
#print axioms integrable
#print axioms integral_upper
#print axioms boundary_zero
end PVEvolutionA.Recovery.ManyStep
