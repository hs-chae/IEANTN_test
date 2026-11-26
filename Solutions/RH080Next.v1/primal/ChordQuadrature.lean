import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open Real Set MeasureTheory
open scoped BigOperators Interval
namespace RH080Next.Primal

private lemma deriv_cos_quadratic (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos y+y^2/2) (-Real.sin x+x) x := by
  have hh : HasDerivAt (fun y : ℝ => y^2/2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const (2 : ℝ)
  exact (Real.hasDerivAt_cos x).add hh


private lemma convex_cos_quadratic :
    ConvexOn ℝ univ (fun y : ℝ => Real.cos y+y^2/2) := by
  have hd : deriv (fun y : ℝ => Real.cos y+y^2/2) = fun y => -Real.sin y+y :=
    funext fun y => (deriv_cos_quadratic y).deriv
  apply convexOn_of_deriv2_nonneg' convex_univ
  · intro x hx
    exact (deriv_cos_quadratic x).differentiableAt.differentiableWithinAt
  · rw [hd]
    fun_prop
  · intro x hx
    change 0 ≤ deriv (deriv _) x
    rw [hd]
    have h : HasDerivAt (fun y : ℝ => -Real.sin y+y) (-Real.cos x+1) x :=
      (Real.hasDerivAt_sin x).neg.add (hasDerivAt_id x)
    rw [h.deriv]
    linarith [Real.cos_le_one x]

private lemma convex_neg_cos_quadratic :
    ConvexOn ℝ univ (fun y : ℝ => -Real.cos y+y^2/2) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := convex_cos_quadratic.2 (mem_univ (x+Real.pi))
    (mem_univ (y+Real.pi)) ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a*(x+Real.pi)+b*(y+Real.pi) = a*x+b*y+Real.pi := by
    calc
      _ = a*x+b*y+(a+b)*Real.pi := by ring
      _ = _ := by rw [hab]; ring
  rw [he, Real.cos_add_pi, Real.cos_add_pi, Real.cos_add_pi] at h
  have hb' : b=1-a := by linarith
  rw [hb'] at h ⊢
  ring_nf at h ⊢
  linarith

/-- The absolute cosine interpolation error, retaining its quadratic shape. -/
theorem cosine_chord_error (a b t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    |Real.cos ((1-t)*a+t*b)-((1-t)*Real.cos a+t*Real.cos b)| ≤
      (b-a)^2/2*t*(1-t) := by
  have hp := convex_cos_quadratic.2 (mem_univ a) (mem_univ b)
    (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  have hn := convex_neg_cos_quadratic.2 (mem_univ a) (mem_univ b)
    (sub_nonneg.mpr ht.2) ht.1 (by ring : (1-t)+t=1)
  simp only [smul_eq_mul] at hp hn
  rw [abs_le]
  constructor <;> nlinarith

/-- Finite real cosine polynomial, allowing arbitrary frequencies. -/
def trigPolynomial {n : ℕ} (w k : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ j, w j*Real.cos (k j*x)

def curvatureBudget {n : ℕ} (w k : Fin n → ℝ) : ℝ := ∑ j, |w j| *(k j)^2

/-- A whole polynomial's chord error is bounded from the actual coefficients. -/
theorem trig_chord_error {n : ℕ} (w k : Fin n → ℝ) (a b t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    |trigPolynomial w k ((1-t)*a+t*b)-
      ((1-t)*trigPolynomial w k a+t*trigPolynomial w k b)| ≤
      curvatureBudget w k/2*(b-a)^2*t*(1-t) := by
  have he : trigPolynomial w k ((1-t)*a+t*b)-
      ((1-t)*trigPolynomial w k a+t*trigPolynomial w k b) =
      ∑ j, w j*(Real.cos (k j*((1-t)*a+t*b))-
        ((1-t)*Real.cos (k j*a)+t*Real.cos (k j*b))) := by
    simp only [trigPolynomial, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  calc
    _ ≤ ∑ j, |w j*(Real.cos (k j*((1-t)*a+t*b))-
        ((1-t)*Real.cos (k j*a)+t*Real.cos (k j*b)))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |w j| *((k j*b-k j*a)^2/2*t*(1-t)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      convert cosine_chord_error (k j*a) (k j*b) t ht using 1 <;> congr 2 <;> ring
    _ = curvatureBudget w k/2*(b-a)^2*t*(1-t) := by
      unfold curvatureBudget
      simp only [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Absolute values preserve an upper chord plus its proved curvature allowance. -/
theorem abs_chord_of_error {f : ℝ → ℝ} {M a b t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1)
    (h : |f ((1-t)*a+t*b)-((1-t)*f a+t*f b)| ≤ M/2*(b-a)^2*t*(1-t)) :
    |f ((1-t)*a+t*b)| ≤ (1-t)*|f a|+t*|f b|+M/2*(b-a)^2*t*(1-t) := by
  have ha : |(1-t)*f a+t*f b| ≤ (1-t)*|f a|+t*|f b| := by
    calc
      _ ≤ |(1-t)*f a|+|t*f b| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
  have he := abs_add_le (f ((1-t)*a+t*b)-((1-t)*f a+t*f b)) ((1-t)*f a+t*f b)
  simp only [sub_add_cancel] at he
  linarith

/-- Integrate a local absolute-value chord on its unit-interval parameter. -/
theorem integral_abs_affine_chord {f : ℝ → ℝ} (hf : Continuous f)
    {M a b : ℝ}
    (herr : ∀ t ∈ Icc (0 : ℝ) 1,
      |f ((1-t)*a+t*b)-((1-t)*f a+t*f b)| ≤ M/2*(b-a)^2*t*(1-t)) :
    (∫ t in (0 : ℝ)..1, |f ((1-t)*a+t*b)|) ≤
      (|f a|+|f b|)/2+M*(b-a)^2/12 := by
  let L : ℝ → ℝ := fun t =>
    (1-t)*|f a|+t*|f b|+M/2*(b-a)^2*t*(1-t)
  have hc1 : Continuous (fun t : ℝ => |f ((1-t)*a+t*b)|) :=
    hf.abs.comp (by fun_prop)
  have hc2 : Continuous L := by dsimp [L]; fun_prop
  have hi : (∫ t in (0 : ℝ)..1, |f ((1-t)*a+t*b)|) ≤ ∫ t in (0 : ℝ)..1, L t := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1)
    intro t ht
    exact abs_chord_of_error ht (herr t ht)
  apply hi.trans_eq
  have he : L = fun t : ℝ => |f a|+
      (|f b|-|f a|+M*(b-a)^2/2)*t-(M*(b-a)^2/2)*t^2 := by
    funext t
    dsimp [L]
    ring
  rw [he]
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  all_goals apply Continuous.intervalIntegrable; fun_prop

/-- The integrated chord on an actual physical cell, with its cubic error. -/
theorem integral_abs_cell_chord {f : ℝ → ℝ} (hf : Continuous f)
    {M a b : ℝ} (hab : a ≤ b)
    (herr : ∀ t ∈ Icc (0 : ℝ) 1,
      |f ((1-t)*a+t*b)-((1-t)*f a+t*f b)| ≤ M/2*(b-a)^2*t*(1-t)) :
    (∫ x in a..b, |f x|) ≤ (b-a)*(|f a|+|f b|)/2+M*(b-a)^3/12 := by
  have hi := integral_abs_affine_chord hf herr
  have he : (fun t : ℝ => |f ((1-t)*a+t*b)|) =
      fun t : ℝ => |f ((b-a)*t+a)| := by
    funext t
    congr 2
    ring
  rw [he] at hi
  have hc := intervalIntegral.smul_integral_comp_mul_add
    (fun x : ℝ => |f x|) (a := (0 : ℝ)) (b := (1 : ℝ)) (b-a) a
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at hc
  calc
    _ = (b-a)*(∫ t in (0 : ℝ)..1, |f ((b-a)*t+a)|) := hc.symm
    _ ≤ (b-a)*((|f a|+|f b|)/2+M*(b-a)^2/12) :=
      mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hab)
    _ = _ := by ring

/-- Composite periodic quadrature. Its hypotheses constrain the genuine function;
there is no numerical certificate or source execution in this analytic lemma. -/
theorem periodic_abs_chord_quadrature {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ}
    (herr : ∀ a b t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      |f ((1-t)*a+t*b)-((1-t)*f a+t*f b)| ≤ M/2*(b-a)^2*t*(1-t))
    (G : ℕ) (hG : 0 < G) (hperiod : f 1=f 0) :
    (∫ x in (0 : ℝ)..1, |f x|) ≤
      (∑ i ∈ Finset.range G, |f ((i : ℝ)/G)|)/(G : ℝ)+M/(12*(G : ℝ)^2) := by
  have hg : (0 : ℝ)<G := by exact_mod_cast hG
  have hgn : (G : ℝ)≠0 := ne_of_gt hg
  have hcell (i : ℕ) :
      (∫ x in ((i : ℝ)/G)..(((i+1 : ℕ) : ℝ)/G), |f x|) ≤
      (|f ((i : ℝ)/G)|+|f (((i+1 : ℕ) : ℝ)/G)|)/(2*(G : ℝ))+
        M/(12*(G : ℝ)^3) := by
    have hab : (i : ℝ)/G ≤ ((i+1 : ℕ) : ℝ)/G := by
      apply div_le_div_of_nonneg_right _ hg.le
      exact_mod_cast Nat.le_succ i
    have hi := integral_abs_cell_chord hf hab (herr _ _)
    convert hi using 1
    push_cast
    field_simp
    <;> ring
  have hsum := Finset.sum_le_sum (fun (i : ℕ) (_ : i∈Finset.range G) => hcell i)
  have hp := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => |f x|) (a := fun i : ℕ => (i : ℝ)/(G : ℝ)) (n := G)
    (fun i hi => hf.abs.intervalIntegrable _ _)
  rw [hp] at hsum
  simp only [Nat.cast_zero, zero_div, div_self hgn] at hsum
  have hshift : (∑ i ∈ Finset.range G, |f (((i+1 : ℕ) : ℝ)/G)|) =
      ∑ i ∈ Finset.range G, |f ((i : ℝ)/G)| := by
    have hs := Finset.sum_range_succ' (fun i : ℕ => |f ((i : ℝ)/G)|) G
    have ht := Finset.sum_range_succ (fun i : ℕ => |f ((i : ℝ)/G)|) G
    simp only [div_self hgn, Nat.cast_zero, zero_div, hperiod] at hs ht
    linarith
  apply hsum.trans_eq
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hshift,
    Finset.sum_const]
  simp only [Finset.card_range, nsmul_eq_mul]
  field_simp
  <;> ring

/-- The finite cosine-series interface used by the numerical C consumer. -/
theorem cosine_series_abs_chord_quadrature (n : ℕ) (w k : ℕ → ℝ)
    (G : ℕ) (hG : 0<G)
    (hperiod : (∑ j ∈ Finset.range n, w j*Real.cos (k j*1)) =
      ∑ j ∈ Finset.range n, w j*Real.cos (k j*0)) :
    (∫ x in (0 : ℝ)..1, |∑ j ∈ Finset.range n, w j*Real.cos (k j*x)|) ≤
      (∑ i ∈ Finset.range G, |∑ j ∈ Finset.range n, w j*Real.cos (k j*((i : ℝ)/G))|)/
        (G : ℝ)+(∑ j ∈ Finset.range n, |w j| *(k j)^2)/(12*(G : ℝ)^2) := by
  let f : ℝ → ℝ := fun x => ∑ j ∈ Finset.range n, w j*Real.cos (k j*x)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have herr (a b t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      |f ((1-t)*a+t*b)-((1-t)*f a+t*f b)| ≤
      (∑ j ∈ Finset.range n, |w j| *(k j)^2)/2*(b-a)^2*t*(1-t) := by
    have he (x : ℝ) : trigPolynomial (fun j : Fin n => w j) (fun j : Fin n => k j) x = f x :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => w j*Real.cos (k j*x)) n
    have hc : curvatureBudget (fun j : Fin n => w j) (fun j : Fin n => k j) =
        ∑ j ∈ Finset.range n, |w j| *(k j)^2 :=
      Fin.sum_univ_eq_sum_range (fun j : ℕ => |w j| *(k j)^2) n
    have h := trig_chord_error (fun j : Fin n => w j) (fun j : Fin n => k j) a b t ht
    rw [he, he, he, hc] at h
    exact h
  exact periodic_abs_chord_quadrature hf herr G hG hperiod

#print axioms cosine_chord_error
#print axioms trig_chord_error
#print axioms abs_chord_of_error
#print axioms integral_abs_affine_chord
#print axioms integral_abs_cell_chord
#print axioms periodic_abs_chord_quadrature
#print axioms cosine_series_abs_chord_quadrature
end RH080Next.Primal
