import ActualJIdentity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
namespace RHContinuation.Ramanujan
open Real Set Finset MeasureTheory Filter
set_option maxHeartbeats 0

noncomputable def gmPrimitive (x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*(x-n))-x^2/2

lemma gmPrimitive_eq_fixed {x b : ℝ} (hx : 0 ≤ x) (hxb : x ≤ b) :
    gmPrimitive x =
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*max 0 (x-n))-x^2/2 := by
  have hsub : Finset.Icc 0 ⌊x⌋₊ ⊆ Finset.Icc 0 ⌊b⌋₊ := by
    intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1,hn.2.trans (Nat.floor_le_floor hxb)⟩
  have he : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*(x-n))=
      ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*max 0 (x-n) := by
    apply sum_congr rfl
    intro n hn
    have hnle : (n:ℝ) ≤ x := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hx)
    rw [max_eq_right (by linarith : 0 ≤ x-n)]
  unfold gmPrimitive
  rw [he]
  congr 1
  apply sum_subset hsub
  intro n hn hnnot
  have hnf : ⌊x⌋₊ < n := by
    simp only [Finset.mem_Icc] at hn hnnot
    omega
  have hxn : x < n := (Nat.floor_lt hx).mp hnf
  rw [max_eq_left (by linarith : x-n ≤ 0),mul_zero]

lemma gmPrimitive_continuousOn {a b : ℝ} (ha : 0 ≤ a) :
    ContinuousOn gmPrimitive (Set.Icc a b) := by
  have hc : Continuous (fun x : ℝ =>
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*max 0 (x-n))-x^2/2) := by
    fun_prop
  apply hc.continuousOn.congr
  intro x hx
  exact gmPrimitive_eq_fixed (ha.trans hx.1) hx.2

lemma gmPrimitive_right_derivative {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt gmPrimitive (Chebyshev.psi x-x) (Set.Ioi x) x := by
  let f : ℝ → ℝ := fun y =>
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n:ℝ)*(y-n))-y^2/2
  have hd : HasDerivAt f (Chebyshev.psi x-x) x := by
    have hs := HasDerivAt.sum (u:=Finset.Icc 0 ⌊x⌋₊) (fun n hn =>
      ((hasDerivAt_id x).sub_const (n:ℝ)).const_mul (ArithmeticFunction.vonMangoldt n:ℝ))
    have h := hs.sub (((hasDerivAt_id x).pow 2).div_const 2)
    convert! h using 1
    · funext y
      simp [f]
    · simp [Chebyshev.psi_eq_sum_Icc]
  have he : gmPrimitive =ᶠ[nhdsWithin x (Set.Ioi x)] f := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (Nat.lt_floor_add_one x))] with y hy hyu
    have hy0 : 0 ≤ y := hx.trans (le_of_lt hy)
    have hf : ⌊y⌋₊=⌊x⌋₊ := (Nat.floor_eq_iff hy0).mpr
      ⟨(Nat.floor_le hx).trans (le_of_lt hy),hyu⟩
    simp [gmPrimitive,f,hf]
  exact hd.hasDerivWithinAt.congr_of_eventuallyEq he rfl

/-- Exact literal GM primitive, including ordinary endpoint conventions. -/
theorem gmPrimitive_eq_integral {x : ℝ} (hx : 0 ≤ x) :
    gmPrimitive x = ∫ t in (0:ℝ)..x, Chebyshev.psi t-t := by
  have hc : ContinuousOn gmPrimitive (Set.uIcc 0 x) := by
    rw [Set.uIcc_of_le hx]
    exact gmPrimitive_continuousOn le_rfl
  have hd : ∀ t ∈ Set.Ioo (min 0 x) (max 0 x),
      HasDerivWithinAt gmPrimitive (Chebyshev.psi t-t) (Set.Ioi t) t := by
    intro t ht
    rw [min_eq_left hx,max_eq_right hx] at ht
    exact gmPrimitive_right_derivative ht.1.le
  have hi : IntervalIntegrable (fun t : ℝ => Chebyshev.psi t-t) volume 0 x :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable 0 x)
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right hc hd hi
  simpa [gmPrimitive] using h.symm

#print axioms gmPrimitive_eq_integral
end RHContinuation.Ramanujan
