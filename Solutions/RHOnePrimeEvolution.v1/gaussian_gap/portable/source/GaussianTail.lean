import GaussianCertificate
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RHOnePrime.GaussianKernel

/-- Uniform elementary tail domination for every monomial actually used by degree12. -/
theorem monomial_gaussian_tail_point (n : ℕ) (hn : n ≤ 24) (x : ℝ) (hx : 8 ≤ x) :
    x^n*Real.exp (-(x^2)) ≤
      (8 : ℝ)^n*Real.exp (-60)*Real.exp (-(x^2)/16) := by
  have hx0 : 0 ≤ x := by linarith
  have hx2 : (64 : ℝ) ≤ x^2 := by nlinarith [sq_nonneg (x-8)]
  have hdec : x^n*Real.exp (-(15/16 : ℝ)*x^2) ≤ (8 : ℝ)^n*Real.exp (-60) := by
    cases n with
    | zero =>
      simp only [pow_zero, one_mul]
      apply Real.exp_le_exp.mpr
      nlinarith
    | succ k =>
      let f : ℝ → ℝ := fun t => t^(k+1)*Real.exp (-(15/16 : ℝ)*t^2)
      have hd (t : ℝ) : HasDerivAt f
          (t^k*Real.exp (-(15/16 : ℝ)*t^2)*((k+1 : ℕ)-(15/8 : ℝ)*t^2)) t := by
        dsimp [f]
        have hraw := ((hasDerivAt_id t).pow (k+1)).mul
          ((((hasDerivAt_id t).pow 2).const_mul (-(15/16 : ℝ))).exp)
        apply hraw.congr_deriv
        simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
          Pi.mul_apply, Pi.pow_apply, id_eq]
        ring
      have hc : Continuous f := by
        exact (continuous_id.pow (k+1)).mul (Real.continuous_exp.comp
          ((continuous_id.pow 2).const_mul (-(15/16 : ℝ))))
      have ha : AntitoneOn f (Ici (8 : ℝ)) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ici (8 : ℝ)) hc.continuousOn
          (fun t ht => (hd t).differentiableAt.differentiableWithinAt)
        intro t ht
        rw [(hd t).deriv]
        have ht8 : (8 : ℝ) < t := by simpa only [interior_Ici, mem_Ioi] using ht
        have ht0 : 0 ≤ t := by linarith
        have ht2 : (64 : ℝ) ≤ t^2 := by nlinarith [sq_nonneg (t-8)]
        have hk : ((k+1 : ℕ) : ℝ) ≤ 24 := by exact_mod_cast hn
        have hlast : ((k+1 : ℕ) : ℝ)-(15/8 : ℝ)*t^2 ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlast
      have hh := ha (by norm_num : (8 : ℝ) ∈ Ici 8) hx hx
      norm_num [f] at hh
      simpa only [neg_mul] using hh
  have hm := mul_le_mul_of_nonneg_right hdec (Real.exp_nonneg (-(x^2)/16))
  have heq : Real.exp (-(15/16 : ℝ)*x^2)*Real.exp (-(x^2)/16) =
      Real.exp (-(x^2)) := by rw [← Real.exp_add]; congr 1; ring
  simpa only [mul_assoc, heq] using hm

def tailBudget : ℕ → List ℚ → ℚ
  | _, [] => 0
  | n, c::cs => |c| *(8 : ℚ)^n + tailBudget (n+1) cs

theorem tailBudget_nonneg (cs : List ℚ) (n : ℕ) : 0 ≤ tailBudget n cs := by
  induction cs generalizing n with
  | nil => simp [tailBudget]
  | cons c cs ih =>
    simp only [tailBudget]
    have := ih (n+1)
    positivity

/-- Pointwise tail bound for the actual rational Horner program, including abs. -/
theorem coeff_gaussian_tail_point (cs : List ℚ) (n : ℕ)
    (hn : n+cs.length ≤ 25) (x : ℝ) (hx : 8 ≤ x) :
    |x^n*coeffEval cs x| *Real.exp (-(x^2)) ≤
      (tailBudget n cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16) := by
  have hx0 : 0 ≤ x := by linarith
  induction cs generalizing n with
  | nil => simp [tailBudget, coeffEval]
  | cons c cs ih =>
    have hn24 : n ≤ 24 := by simp only [List.length_cons] at hn; omega
    have htail := ih (n+1) (by simp only [List.length_cons] at hn; omega)
    have hhead := mul_le_mul_of_nonneg_left (monomial_gaussian_tail_point n hn24 x hx)
      (abs_nonneg (c : ℝ))
    have heq : x^n*coeffEval (c::cs) x = (c : ℝ)*x^n + x^(n+1)*coeffEval cs x := by
      simp only [coeffEval, pow_succ]; ring
    rw [heq]
    calc
      |(c : ℝ)*x^n+x^(n+1)*coeffEval cs x| *Real.exp (-(x^2))
        ≤ (|(c : ℝ)*x^n| +|x^(n+1)*coeffEval cs x|)*Real.exp (-(x^2)) :=
          mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.exp_nonneg _)
      _ = |(c : ℝ)| *(x^n*Real.exp (-(x^2)))+
          |x^(n+1)*coeffEval cs x| *Real.exp (-(x^2)) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 n)]; ring
      _ ≤ |(c : ℝ)| *((8 : ℝ)^n*Real.exp (-60)*Real.exp (-(x^2)/16))+
          (tailBudget (n+1) cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16) :=
        add_le_add hhead htail
      _ = (tailBudget n (c::cs) : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16) := by
        simp only [tailBudget, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, Rat.cast_pow,
          Rat.cast_ofNat]
        ring

/-- The integrated infinite tail is bounded by a complete Gaussian integral. -/
theorem coeff_gaussian_infinite_tail (cs : List ℚ) (hn : cs.length ≤ 25) :
    (∫ x in Ioi (8 : ℝ), |coeffEval cs x| *Real.exp (-(x^2))) ≤
      (tailBudget 0 cs : ℝ)*Real.exp (-60)*8 := by
  have hgauss : Integrable (fun x : ℝ => Real.exp (-(x^2)/16)) := by
    have hg := integrable_exp_neg_mul_sq (b := (1/16 : ℝ)) (by norm_num)
    convert hg using 1 <;> funext x <;> congr 1 <;> ring
  have hc : 0 ≤ (tailBudget 0 cs : ℝ)*Real.exp (-60) := by
    have : 0 ≤ (tailBudget 0 cs : ℝ) := by exact_mod_cast tailBudget_nonneg cs 0
    positivity
  have hg : Integrable (fun x : ℝ =>
      (tailBudget 0 cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16)) :=
    hgauss.const_mul _
  have hpoint (x : ℝ) (hx : x ∈ Ioi (8 : ℝ)) :
      |coeffEval cs x| *Real.exp (-(x^2)) ≤
      (tailBudget 0 cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16) := by
    simpa only [pow_zero, one_mul, zero_add] using
      coeff_gaussian_tail_point cs 0 (by simpa using hn) x hx.le
  have hm := integral_mono_of_nonneg
    (f := fun x : ℝ => |coeffEval cs x| * Real.exp (-(x^2)))
    (g := fun x : ℝ => (tailBudget 0 cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16))
    (μ := volume.restrict (Ioi (8 : ℝ))) (ae_of_all _ (fun x => by positivity))
    hg.integrableOn (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hpoint x hx)
  have hset := setIntegral_le_integral (s := Ioi (8 : ℝ)) hg
    (ae_of_all _ (fun x => mul_nonneg hc (Real.exp_nonneg _)))
  have hfull : (∫ x : ℝ, (tailBudget 0 cs : ℝ)*Real.exp (-60)*Real.exp (-(x^2)/16)) =
      (tailBudget 0 cs : ℝ)*Real.exp (-60)*Real.sqrt (16*Real.pi) := by
    rw [integral_const_mul]
    have heq : (fun x : ℝ => Real.exp (-(x^2)/16)) =
        (fun x : ℝ => Real.exp (-(1/16 : ℝ)*x^2)) := by funext x; congr 1; ring
    rw [heq, integral_gaussian]
    congr 1
    congr 1
    ring
  have hpi : Real.sqrt (16*Real.pi) ≤ (8 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [Real.pi_lt_four]
  exact (hm.trans (hset.trans_eq hfull)).trans (mul_le_mul_of_nonneg_left hpi hc)

#print axioms monomial_gaussian_tail_point
#print axioms coeff_gaussian_infinite_tail
end RHOnePrime.GaussianKernel
