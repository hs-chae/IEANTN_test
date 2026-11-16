import Mathlib
namespace SynergyAnalytic
open Real Set MeasureTheory Finset
set_option maxHeartbeats 0
set_option maxRecDepth 20000

noncomputable def positiveExpPoly (n:ℕ) (z:ℝ) : ℝ :=
  ∑k∈range (n+1),z^k/(k.factorial:ℝ)

 theorem positiveExpPoly_zero (n:ℕ) : positiveExpPoly n 0=1 := by
  induction n with
  | zero => simp [positiveExpPoly]
  | succ n ih =>
    unfold positiveExpPoly at *
    rw [sum_range_succ]
    simp [ih]

 theorem positiveExpPoly_deriv (n:ℕ) (z:ℝ) :
    HasDerivAt (positiveExpPoly n) (positiveExpPoly n z-z^n/(n.factorial:ℝ)) z := by
  induction n with
  | zero =>
    have he : positiveExpPoly 0=(fun _:ℝ=>1) := by funext x;simp [positiveExpPoly]
    rw [he]
    simpa using hasDerivAt_const z (1:ℝ)
  | succ n ih =>
    have hfn : positiveExpPoly (n+1) = fun x=>positiveExpPoly n x+x^(n+1)/((n+1).factorial:ℝ) := by
      funext x
      exact sum_range_succ _ _
    have hn : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hs : (n+1:ℝ) ≠ 0 := by positivity
    have ht := ((hasDerivAt_id z).pow (n+1)).div_const ((n+1).factorial:ℝ)
    simp only [id_eq,Nat.add_sub_cancel] at ht
    rw [hfn]
    convert ih.add ht using 1 <;> first
      | rfl
      | (try simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one];
         try field_simp;ring)

/-- Exact real counterpart of the finite exponential-moment expression in
basis_fp128_tangent.cpp. Its interval implementation is a separate obligation. -/
noncomputable def exponentialMoment (n:ℕ) (lambda width:ℝ) : ℝ :=
  (n.factorial:ℝ)/lambda^(n+1)*
    (1-Real.exp (-lambda*width)*positiveExpPoly n (lambda*width))

 theorem exponentialMoment_deriv {lambda:ℝ} (hl:lambda ≠ 0) (n:ℕ) (w:ℝ) :
    HasDerivAt (exponentialMoment n lambda) (w^n*Real.exp (-lambda*w)) w := by
  have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hp := (positiveExpPoly_deriv n (lambda*w)).comp w ((hasDerivAt_id w).const_mul lambda)
  have he := (((hasDerivAt_id w).const_mul (-lambda)).exp)
  have hd := ((hasDerivAt_const w (1:ℝ)).sub (he.mul hp)).const_mul ((n.factorial:ℝ)/lambda^(n+1))
  unfold exponentialMoment
  convert hd using 1 <;> first
    | rfl
    | (funext y;rfl)
    | (dsimp only [id_eq,Function.comp_def]; rw [mul_pow,pow_succ]; field_simp <;> ring)

 theorem exponentialMoment_integral {lambda:ℝ} (hl:lambda ≠ 0) (n:ℕ) (w:ℝ) :
    (∫v in (0:ℝ)..w,v^n*Real.exp (-lambda*v))=exponentialMoment n lambda w := by
  have hcont : Continuous (fun v:ℝ=>v^n*Real.exp (-lambda*v)) := by fun_prop
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv=>exponentialMoment_deriv hl n v) (hcont.intervalIntegrable 0 w)
  have hz : exponentialMoment n lambda 0=0 := by simp [exponentialMoment,positiveExpPoly_zero]
  simpa only [hz,sub_zero] using he

 theorem exponentialMoment_nonneg {lambda width:ℝ} (hl:lambda ≠ 0) (hw:0 ≤ width) (n:ℕ) :
    0 ≤ exponentialMoment n lambda width := by
  rw [←exponentialMoment_integral hl]
  apply intervalIntegral.integral_nonneg hw
  intro x hx
  exact mul_nonneg (pow_nonneg hx.1 n) (Real.exp_pos _).le

/-- Consequently the source's positive subtraction clamps an exact
nonnegative real residue; it does not introduce a new analytic allowance. -/
 theorem exponentialMoment_residue_nonneg {lambda width:ℝ}
    (hl:0 < lambda) (hw:0 ≤ width) (n:ℕ) :
    0 ≤ 1-Real.exp (-lambda*width)*positiveExpPoly n (lambda*width) := by
  have hf : 0 < (n.factorial:ℝ)/lambda^(n+1) := by positivity
  have hn := exponentialMoment_nonneg hl.ne' hw n
  unfold exponentialMoment at hn
  exact nonneg_of_mul_nonneg_right hn hf

#print axioms exponentialMoment_integral
#print axioms exponentialMoment_residue_nonneg
end SynergyAnalytic
