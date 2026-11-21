import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Real endpoint and RH guard theorems. No imported analytic bound is
asserted here; the finite comparison takes explicitly stated inputs. -/
namespace RHReal
open Real Set

theorem rh_on_strip (rh : RiemannHypothesis) {s : ℂ}
    (hs : riemannZeta s = 0) (h0 : 0 ≤ s.re) (h1 : s ≠ 1) : s.re = 1/2 := by
  refine rh s hs ?_ h1
  rintro ⟨n,hn⟩
  have ha := congrArg Complex.re hn
  norm_num [Complex.mul_re, Complex.add_re, Complex.neg_re,
    Complex.neg_im, Complex.natCast_re, Complex.natCast_im] at ha
  linarith [Nat.cast_nonneg (α:=ℝ) n]

noncomputable def pcount (x : ℝ) : ℝ := x |> Nat.floor |> Nat.primeCounting |> Nat.cast
noncomputable def coeff (x : ℝ) : ℝ := exp 1 * (x / log x)
noncomputable def Gap (x : ℝ) : ℝ := coeff x * pcount (x / exp 1) - pcount x ^ 2

theorem pcount_mono : Monotone pcount := by
  intro x y h
  unfold pcount
  exact_mod_cast (Nat.monotone_primeCounting (Nat.floor_le_floor h))

theorem pcount_nonneg (x : ℝ) : 0 ≤ pcount x := by
  unfold pcount
  positivity

theorem pcount_natcell (n : ℕ) {x : ℝ} (hl : (n : ℝ) ≤ x)
    (hh : x < (n : ℝ)+1) : pcount x = (n.primeCounting : ℝ) := by
  unfold pcount
  have hn : ⌊x⌋₊ = n := (Nat.floor_eq_iff ((Nat.cast_nonneg n).trans hl)).mpr ⟨hl,hh⟩
  simp [hn]

theorem coeff_strict : StrictMonoOn coeff (Ici (exp 1)) := by
  have hone : 1 < exp (1 : ℝ) := one_lt_exp_iff.mpr (by norm_num)
  have hpos : ∀ x ∈ Ici (exp 1), 0 < x := fun x hx =>
    (exp_pos 1).trans_le hx
  have hlog : ∀ x ∈ Ici (exp 1), 0 < log x := fun x hx =>
    log_pos (hone.trans_le hx)
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact continuousOn_const.mul (continuousOn_id.div
      (continuousOn_log.mono (fun x hx => ne_of_gt (hpos x hx))) (fun x hx => ne_of_gt (hlog x hx)))
  · intro x hx
    have hx' : exp 1 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hx0 := (exp_pos 1).trans hx'
    have hlog1 : 1 < log x := by
      rw [← log_exp 1]; exact strictMonoOn_log (exp_pos 1) hx0 hx'
    have hd : HasDerivAt coeff
      (exp 1 * ((1 * log x - x * x⁻¹)/ (log x)^2)) x :=
      ((hasDerivAt_id x).div (hasDerivAt_log hx0.ne') (by linarith)).const_mul _
    rw [hd.deriv]
    rw [mul_inv_cancel₀ hx0.ne',one_mul]
    exact mul_pos (exp_pos 1) (div_pos (by linarith) (by positivity))

theorem coeff_nonneg {x : ℝ} (hx : exp 1 ≤ x) : 0 ≤ coeff x := by
  have h : 1 < x := (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hlog := log_pos h
  unfold coeff
  positivity

/-- A directed test at a cell boundary yields a real-interval result. -/
theorem cell_positive {a b el lu plo phi : ℝ} (ha : exp 1 ≤ a)
    (he : 0 ≤ el) (hee : el ≤ exp 1) (hl : log a ≤ lu)
    (hp : 0 ≤ plo) (hlp : plo ≤ pcount (a/exp 1))
    (hup : pcount b ≤ phi) (htest : lu * phi^2 < el*a*plo) :
    ∀ x ∈ Icc a b, 0 < Gap x := by
  intro x hx
  have hx1 := ha.trans hx.1
  have ha1 : 1 < a :=
    (one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le ha
  have hla := log_pos ha1
  have hlu := hla.trans_le hl
  have ha0 : 0 ≤ a := le_of_lt (lt_trans zero_lt_one ha1)
  have cc : el*a*plo/lu ≤ coeff a * pcount (a/exp 1) := by
    have hmul : el*a*plo ≤ exp 1*a*pcount (a/exp 1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hee ha0) hlp hp
        (mul_nonneg (exp_pos 1).le ha0)
    have h0 : 0 ≤ el*a*plo := by positivity
    calc
      el*a*plo/lu ≤ el*a*plo/log a := div_le_div_of_nonneg_left h0 hla hl
      _ ≤ exp 1*a*pcount (a/exp 1)/log a := div_le_div_of_nonneg_right hmul hla.le
      _ = coeff a * pcount (a/exp 1) := by unfold coeff; ring
  have cm : coeff a ≤ coeff x := coeff_strict.monotoneOn ha hx1 hx.1
  have hcm : coeff a * pcount (a/exp 1) ≤ coeff x * pcount (x/exp 1) :=
    mul_le_mul cm (pcount_mono (div_le_div_of_nonneg_right hx.1 (exp_pos 1).le))
      (pcount_nonneg _) (coeff_nonneg hx1)
  have pp := pow_le_pow_left₀ (pcount_nonneg x) ((pcount_mono hx.2).trans hup) 2
  have tt : phi^2 < el*a*plo/lu := (lt_div_iff₀ hlu).mpr (by simpa [mul_comm] using htest)
  exact sub_pos.mpr (pp.trans_lt (tt.trans_le (cc.trans hcm)))

/-- Exact prime count on [n,n+1) is enough to lift a positive integer comparison. -/
theorem lift_integer {n : ℕ} (hn : exp 1 ≤ (n:ℝ))
    (h : 0 < Gap (n:ℝ)) {x : ℝ} (hx₀ : (n:ℝ) ≤ x) (hx₁ : x < (n:ℝ)+1) :
    0 < Gap x := by
  have he : pcount x = pcount (n:ℝ) := by
    rw [pcount_natcell n hx₀ hx₁, pcount_natcell n le_rfl (by linarith)]
  have hp : coeff (n:ℝ)*pcount ((n:ℝ)/exp 1) ≤ coeff x*pcount (x/exp 1) :=
    mul_le_mul (coeff_strict.monotoneOn hn (hn.trans hx₀) hx₀)
      (pcount_mono (div_le_div_of_nonneg_right hx₀ (exp_pos 1).le))
      (pcount_nonneg _) (coeff_nonneg (hn.trans hx₀))
  unfold Gap at *
  rw [he]
  linarith

#print axioms rh_on_strip
#print axioms cell_positive
#print axioms lift_integer
end RHReal
