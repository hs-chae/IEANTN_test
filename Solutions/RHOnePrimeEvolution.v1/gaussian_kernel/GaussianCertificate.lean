import GaussianMajorant
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RHOnePrime.GaussianKernel

/-- Suggestions are untrusted; every field is connected by `CellValid`. -/
structure GaussianCellData where
  a : ℚ
  h : ℚ
  B : ℚ
  E : ℚ
  M : ℚ
  I : ℚ
  upper : ℚ
  m : ℕ
  shifted : List ℚ
  majorant : List ℚ
  product : List ℚ
  deriving DecidableEq

def CellValid (absMode : Bool) (source : List ℚ) (d : GaussianCellData) : Prop :=
  0 ≤ d.a ∧ 0 ≤ d.h ∧ 0 < d.m ∧
  coeffComp source [d.a,d.h] = d.shifted ∧
  coeffMajorant absMode d.shifted = d.majorant ∧
  coeffMul d.majorant (taylorCoeffs d.a d.h 8) = d.product ∧
  coeffAbsBudget d.majorant ≤ d.M ∧
  coeffMoment 0 d.product = d.I ∧
  (∑ i ∈ Finset.range 24, (-(d.a*d.a/d.m))^i/(i.factorial : ℚ)) +
    (d.a*d.a/d.m)^24/(24 : ℕ).factorial ≤ d.B ∧
  d.B^d.m ≤ d.E ∧
  d.h*d.E*(max 0 d.I + d.M*((2*d.a*d.h+d.h*d.h)^8/(8 : ℕ).factorial)) ≤ d.upper

instance (absMode : Bool) (source : List ℚ) (d : GaussianCellData) :
    Decidable (CellValid absMode source d) := by
  unfold CellValid
  infer_instance

/-- General soundness of the executable rational certificate for actual Gaussian integrals. -/
theorem cellValid_integral_upper (absMode : Bool) (source : List ℚ) (d : GaussianCellData)
    (hv : CellValid absMode source d) :
    (∫ u in (d.a : ℝ)..((d.a+d.h : ℚ) : ℝ),
      positivePartOrAbs absMode (coeffEval source u)*Real.exp (-(u^2))) ≤ (d.upper : ℝ) := by
  rcases hv with ⟨ha,hh,hm,hshift,hmajorant,hproduct,hbudget,hI,hbase,hpow,hfinal⟩
  have ha' : 0 ≤ (d.a : ℝ) := by exact_mod_cast ha
  have hh' : 0 ≤ (d.h : ℝ) := by exact_mod_cast hh
  have hM : 0 ≤ (d.M : ℝ) := by
    exact_mod_cast (coeffAbsBudget_nonneg d.majorant).trans hbudget
  have hR : 0 ≤ (((2*d.a*d.h+d.h*d.h)^8/(8 : ℕ).factorial : ℚ) : ℝ) := by
    exact_mod_cast (by positivity : (0 : ℚ) ≤ (2*d.a*d.h+d.h*d.h)^8/(8 : ℕ).factorial)
  have he : Real.exp (-((d.a : ℝ)^2)) ≤ (d.E : ℝ) := by
    have := exp_neg_upper_reduction (d.a*d.a) d.B d.E (mul_nonneg ha ha) d.m 24 hm hbase hpow
    simpa only [Rat.cast_mul, pow_two] using this
  have hbud (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |realEval (coeffPoly d.majorant) t| ≤ (d.M : ℝ) := by
    rw [realEval_coeffPoly]
    exact (abs_coeffEval_le _ _ ht).trans (by exact_mod_cast hbudget)
  have heval (t : ℝ) :
      realEval ((coeffPoly d.majorant)*expNegPoly d.a d.h 8) t =
      coeffEval d.product t := by
    simp only [realEval, Polynomial.eval₂_mul]
    change realEval (coeffPoly d.majorant) t * realEval (expNegPoly d.a d.h 8) t = _
    rw [realEval_coeffPoly, ← coeffEval_taylorCoeffs, ← coeffEval_mul, hproduct]
  have hratI : (unitIntegral ((coeffPoly d.majorant)*expNegPoly d.a d.h 8) : ℝ) = (d.I : ℝ) := by
    rw [← integral_realEval_unit]
    simp_rw [heval]
    rw [integral_coeffEval, hI]
  have hquad := gaussian_cell_integral_upper (coeffPoly d.majorant)
    (expNegPoly d.a d.h 8) d.a d.h d.M
    (((2*d.a*d.h+d.h*d.h)^8/(8 : ℕ).factorial : ℚ) : ℝ) d.E hM hR hbud
    (expNegPoly_error d.a d.h ha hh 8) he
  rw [hratI] at hquad
  have hsub (t : ℝ) : coeffEval source ((d.a : ℝ)+(d.h : ℝ)*t) = coeffEval d.shifted t := by
    have heq := coeffEval_comp source [d.a,d.h] t
    rw [hshift] at heq
    simpa only [coeffEval, mul_zero, zero_mul, add_zero, mul_comm t] using heq.symm
  have hcover (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      positivePartOrAbs absMode (coeffEval source ((d.a : ℝ)+(d.h : ℝ)*t)) ≤
      realEval (coeffPoly d.majorant) t := by
    rw [hsub, realEval_coeffPoly, ← hmajorant]
    exact coeffMajorant_sound _ _ _ ht
  have hc0 := continuous_positivePartOrAbs absMode source
  have hcont : Continuous (fun t : ℝ =>
      positivePartOrAbs absMode (coeffEval source ((d.a : ℝ)+(d.h : ℝ)*t)) *
      Real.exp (-(((d.a : ℝ)+(d.h : ℝ)*t)^2))) := by
    apply (hc0.comp (continuous_const.add (continuous_const.mul continuous_id))).mul
    exact Real.continuous_exp.comp ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 2).neg
  have hcont' : Continuous (fun t : ℝ => realEval (coeffPoly d.majorant) t *
      Real.exp (-(((d.a : ℝ)+(d.h : ℝ)*t)^2))) := by
    apply (continuous_realEval _).mul
    exact Real.continuous_exp.comp ((continuous_const.add
      (continuous_const.mul continuous_id)).pow 2).neg
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hcont.intervalIntegrable 0 1) (hcont'.intervalIntegrable 0 1)
    (fun t ht => mul_le_mul_of_nonneg_right (hcover t ht) (Real.exp_nonneg _))
  have htotal := mul_le_mul_of_nonneg_left (hmono.trans hquad) hh'
  have hfin : (d.h : ℝ)*(d.E : ℝ)*(max 0 (d.I : ℝ)+(d.M : ℝ)*
      (((2*d.a*d.h+d.h*d.h)^8/(8 : ℕ).factorial : ℚ) : ℝ)) ≤ (d.upper : ℝ) := by
    exact_mod_cast hfinal
  have hcell := integral_affine_cell (fun u : ℝ =>
      positivePartOrAbs absMode (coeffEval source u)*Real.exp (-(u^2))) d.a d.h
  have hstep : (d.h : ℝ)*(∫ t in (0 : ℝ)..1,
      positivePartOrAbs absMode (coeffEval source ((d.a : ℝ)+(d.h : ℝ)*t))*
      Real.exp (-(((d.a : ℝ)+(d.h : ℝ)*t)^2))) ≤ (d.upper : ℝ) := by
    exact htotal.trans (by simpa only [mul_assoc] using hfin)
  rw [hcell] at hstep
  simpa only [Rat.cast_add] using hstep

#print axioms cellValid_integral_upper
end RHOnePrime.GaussianKernel
