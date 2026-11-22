/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Actual Mobius consumer of three explicit Mellin integral enclosures.
The displayed enclosure obligations remain explicit until the complex-analytic
chain is formalized; this module does not claim they have been discharged. -/
import MobiusSmoothing
import ReciprocalScalars
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic
namespace RHContinuation.PerronPower
open Real MeasureTheory Set
open RHContinuation.MobiusSmoothing
noncomputable def sigma : ℝ := 3/4
noncomputable def epsilon : ℝ := 8/25
noncomputable def kappa : ℝ := 107/132
noncomputable def C : ℝ := 150000
noncomputable def h (x:ℝ) : ℝ := x^kappa
noncomputable def V (x:ℝ) : ℝ := 4*x/h x
noncomputable def s (t:ℝ) : ℂ := (sigma:ℂ)+t*Complex.I
noncomputable def kernel (x t:ℝ) : ℂ :=
  (((x+h x:ℝ):ℂ)^(s t+1)-(x:ℂ)^(s t+1))/
    ((2*Real.pi*h x:ℝ)*s t*(s t+1)*riemannZeta (s t))
noncomputable def I0 (x:ℝ) : ℂ := ∫ t in Icc (-1:ℝ) 1, kernel x t
noncomputable def I1 (x:ℝ) : ℂ := (∫t in Icc (-V x) (V x),kernel x t)-I0 x
noncomputable def I2 (x:ℝ) : ℂ := (∫t, kernel x t)-(∫t in Icc (-V x) (V x),kernel x t)
/-- The precise normalized form of Simonic2201.10771v1(45), PDFp17.
This source input is the Mellin identity, not an M-bound or a numerical enclosure. -/
def Perron45At (x:ℝ) : Prop :=
  Integrable (kernel x) ∧ (smoothedM (x+h x)-smoothedM x)/h x=(∫t,kernel x t).re

theorem h_bounds {x:ℝ} (hx:1≤x) : 1≤h x ∧ h x≤x := by
  have hx0 : 0<x := by linarith
  constructor
  · exact Real.one_le_rpow hx (by norm_num [kappa])
  · calc h x = x^kappa := rfl
      _ ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num [kappa])
      _ = x := Real.rpow_one x

theorem height_bounds {x:ℝ} (hx:1≤x) : 4≤V x := by
  have hh := h_bounds hx
  have hh0 : 0<h x := by linarith [hh.1]
  apply (le_div_iff₀ hh0).mpr
  nlinarith [hh.2]

theorem middle_power {x:ℝ} (hx:1≤x) :
    x^sigma*(V x)^epsilon=4^epsilon*x^kappa := by
  have hx0 : 0<x := by linarith
  dsimp [V,h]
  rw [Real.div_rpow (by positivity) (Real.rpow_nonneg hx0.le _),
      Real.mul_rpow (by norm_num) hx0.le,← Real.rpow_mul hx0.le,
      mul_div_assoc]
  calc _ = 4^epsilon*(x^sigma*x^epsilon/x^(kappa*epsilon)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0,← Real.rpow_sub hx0]
      norm_num [sigma,epsilon,kappa]

theorem high_power {x:ℝ} (hx:1≤x) :
    x^(sigma+1)/h x*(V x)^(epsilon-1)=4^(epsilon-1)*x^kappa := by
  have hx0 : 0<x := by linarith
  dsimp [V,h]
  rw [Real.div_rpow (by positivity) (Real.rpow_nonneg hx0.le _),
      Real.mul_rpow (by norm_num) hx0.le,← Real.rpow_mul hx0.le]
  have hp : x^kappa≠0 := (Real.rpow_pos_of_pos hx0 _).ne'
  have hp2 : x^(kappa*(epsilon-1))≠0 := (Real.rpow_pos_of_pos hx0 _).ne'
  have heq : sigma+1+(epsilon-1)=kappa*2+(epsilon-1)*kappa := by norm_num [sigma,epsilon,kappa]
  field_simp
  have hsq : (x^kappa)^2=x^(kappa*2) := by rw [Real.rpow_mul hx0.le,Real.rpow_two]
  rw [← Real.rpow_add hx0,hsq,← Real.rpow_add hx0,heq]

noncomputable def coefficient : ℝ :=
  2+(2:ℝ)^sigma*C/Real.pi*(1/sigma+4^epsilon/epsilon+4^epsilon/(1-epsilon))

theorem coefficient_lt : coefficient<1100000 := by
  have h2 : (2:ℝ)^sigma<2 := by
    calc _ < (2:ℝ)^(1:ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num [sigma])
      _ = 2 := Real.rpow_one _
  have h4 : (4:ℝ)^epsilon<2 := by
    calc _ ≤ (6:ℝ)^epsilon := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num [epsilon])
      _ < 2 := by convert RHContinuation.ReciprocalScalars.six_rpow_point32_lt_two using 1 <;> norm_num [epsilon]
  have h20 : 0<(2:ℝ)^sigma := by positivity
  have h40 : 0<(4:ℝ)^epsilon := by positivity
  have hp := Real.pi_gt_three
  dsimp [coefficient,sigma,epsilon,C]
  have hc : (2:ℝ)^(3/4:ℝ)*150000/Real.pi <100000 := by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    dsimp [sigma] at h2
    nlinarith
  have hb : 1/(3/4:ℝ)+(4:ℝ)^(8/25:ℝ)/(8/25)+(4:ℝ)^(8/25:ℝ)/(1-8/25)<10.6 := by
    norm_num [epsilon] at h4 ⊢
    linarith
  have hb0 : 0<1/(3/4:ℝ)+(4:ℝ)^(8/25:ℝ)/(8/25)+(4:ℝ)^(8/25:ℝ)/(1-8/25) := by positivity
  nlinarith

/-- An actual M(x) consumer. The three pending hypotheses are exact enclosures
of actual zeta-Mellin integrals, not a premise asserting the conclusion. This
partial theorem must not be reported as closing those analytic enclosures. -/
theorem actual_M_from_three_enclosures {x:ℝ} (hx:1≤x) (hP:Perron45At x)
    (h0:‖I0 x‖≤2^sigma*C/(Real.pi*sigma)*x^sigma)
    (h1:‖I1 x‖≤2^sigma*C/(Real.pi*epsilon)*x^sigma*(V x)^epsilon)
    (h2:‖I2 x‖≤2^(sigma+2)*C/(Real.pi*(1-epsilon))*x^(sigma+1)/h x*(V x)^(epsilon-1)) :
    |M x|<1100000*x^kappa := by
  have hx0 : 0<x := by linarith
  have hh := h_bounds hx
  have hdisc := smoothing_discrepancy (by linarith : 0≤x) (by linarith : 0<h x)
  have hid : (∫t,kernel x t)=I0 x+I1 x+I2 x := by dsimp [I0,I1,I2]; ring
  have hnorm : |(smoothedM (x+h x)-smoothedM x)/h x|≤‖I0 x‖+‖I1 x‖+‖I2 x‖ := by
    rw [hP.2,hid]
    exact (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _))
  have htri : |M x|≤h x+1+‖I0 x‖+‖I1 x‖+‖I2 x‖ := by
    have ht := abs_add_le ((smoothedM (x+h x)-smoothedM x)/h x-M x)
      (-((smoothedM (x+h x)-smoothedM x)/h x))
    have ha : (smoothedM (x+h x)-smoothedM x)/h x-M x + -((smoothedM (x+h x)-smoothedM x)/h x) = -M x := by ring
    rw [ha,abs_neg] at ht
    simp only [abs_neg] at ht
    linarith
  have hs : x^sigma≤x^kappa := Real.rpow_le_rpow_of_exponent_le hx (by norm_num [sigma,kappa])
  have hm := middle_power hx
  have hhi := high_power hx
  have he : (2:ℝ)^(sigma+2)=4*2^sigma := by rw [Real.rpow_add (by norm_num)]; norm_num; ring
  have he4 : (4:ℝ)^(epsilon-1)=4^epsilon/4 := by rw [Real.rpow_sub (by norm_num)]; norm_num
  rw [he] at h2
  have hr : |M x|≤coefficient*x^kappa := by
    have h0' : ‖I0 x‖≤2^sigma*C/(Real.pi*sigma)*x^kappa := h0.trans (by gcongr; norm_num [sigma,C]; positivity)
    have h1' : ‖I1 x‖≤2^sigma*C/(Real.pi*epsilon)*(4^epsilon*x^kappa) := by
      calc _ ≤ _ := h1
        _ = _ := by rw [mul_assoc,hm]
    have h2' : ‖I2 x‖≤2^sigma*C/(Real.pi*(1-epsilon))*(4^epsilon*x^kappa) := by
      calc _ ≤ _ := h2
        _ = _ := by
          have heq := hhi
          rw [he4] at heq
          calc _ = 4*(2^sigma*C/(Real.pi*(1-epsilon)))*(x^(sigma+1)/h x*(V x)^(epsilon-1)) := by ring
            _ = _ := by rw [heq]; ring
    dsimp [coefficient,h] at *
    have hq : 0<Real.pi*sigma := by norm_num [sigma]; positivity
    have hqe : 0<Real.pi*epsilon := by norm_num [epsilon]; positivity
    have hqr : 0<Real.pi*(1-epsilon) := by norm_num [epsilon]; positivity
    have halg : (2:ℝ)*x^kappa+2^sigma*C/(Real.pi*sigma)*x^kappa+
      2^sigma*C/(Real.pi*epsilon)*(4^epsilon*x^kappa)+
      2^sigma*C/(Real.pi*(1-epsilon))*(4^epsilon*x^kappa)=
      (2+2^sigma*C/Real.pi*(1/sigma+4^epsilon/epsilon+4^epsilon/(1-epsilon)))*x^kappa := by field_simp; ring
    rw [← halg]
    linarith
  exact hr.trans_lt (mul_lt_mul_of_pos_right coefficient_lt (Real.rpow_pos_of_pos hx0 _))
#print axioms actual_M_from_three_enclosures
end RHContinuation.PerronPower
