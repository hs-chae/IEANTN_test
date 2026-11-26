/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.Explicit

/-- A smooth modulus for finite-cutoff integration by parts.  Its constant
epsilon floor must be removed, or epsilon sent to zero, before infinity. -/
def cmsSmoothModulus (F : ℝ → ℝ) (ε x : ℝ) : ℝ := Real.sqrt ((F x)^2+ε^2)
def cmsSmoothModulusDeriv (F F' : ℝ → ℝ) (ε x : ℝ) : ℝ :=
  F x*F' x/Real.sqrt ((F x)^2+ε^2)

theorem cmsSmoothModulus_pos (F : ℝ → ℝ) {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    0<cmsSmoothModulus F ε x := by
  apply Real.sqrt_pos.2
  have := sq_pos_of_pos hε
  nlinarith [sq_nonneg (F x)]

theorem cmsSmoothModulus_hasDerivAt {F F' : ℝ → ℝ} {ε x : ℝ}
    (hd : HasDerivAt F (F' x) x) (hε : 0<ε) :
    HasDerivAt (cmsSmoothModulus F ε) (cmsSmoothModulusDeriv F F' ε x) x := by
  have positive : 0<(F x)^2+ε^2 := by nlinarith [sq_nonneg (F x),sq_pos_of_pos hε]
  have hpow : HasDerivAt (fun y=>(F y)^2) (2*F x*F' x) x := by
    simpa using! hd.pow 2
  have hin : HasDerivAt (fun y=>(F y)^2+ε^2) (2*F x*F' x) x := hpow.add_const (ε^2)
  have h:=hin.sqrt (ne_of_gt positive)
  change HasDerivAt (fun y=>Real.sqrt ((F y)^2+ε^2))
    (F x*F' x/Real.sqrt ((F x)^2+ε^2)) x
  convert! h using 1
  field_simp

theorem cmsSmoothModulusDeriv_continuous {F F' : ℝ → ℝ} {ε : ℝ}
    (hd : ∀x,HasDerivAt F (F' x) x) (hc : Continuous F') (hε : 0<ε) :
    Continuous (cmsSmoothModulusDeriv F F' ε) := by
  have hF : Continuous F := continuous_iff_continuousAt.2 (fun x=>(hd x).continuousAt)
  exact (hF.mul hc).div ((hF.pow 2).add continuous_const).sqrt
    (fun x=>ne_of_gt (cmsSmoothModulus_pos F hε x))

theorem cmsSmoothModulus_bounds (F : ℝ → ℝ) {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    |F x|≤cmsSmoothModulus F ε x ∧ cmsSmoothModulus F ε x≤|F x|+ε := by
  have hs : (cmsSmoothModulus F ε x)^2=(F x)^2+ε^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (F x),sq_nonneg ε])
  have hp:=(cmsSmoothModulus_pos F hε x).le
  have ha:=abs_nonneg (F x)
  have hasq:=sq_abs (F x)
  constructor <;> nlinarith

theorem cmsSmoothModulus_uniform_error (F : ℝ → ℝ) {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    0≤cmsSmoothModulus F ε x-|F x| ∧ cmsSmoothModulus F ε x-|F x|≤ε := by
  obtain ⟨lo,hi⟩:=cmsSmoothModulus_bounds F hε x
  constructor <;> linarith

theorem cmsSmoothModulusDeriv_abs_le (F F' : ℝ → ℝ) {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    |cmsSmoothModulusDeriv F F' ε x|≤|F' x| := by
  have positive:=cmsSmoothModulus_pos F hε x
  have bounds:=cmsSmoothModulus_bounds F hε x
  change 0<Real.sqrt ((F x)^2+ε^2) at positive
  rw [cmsSmoothModulusDeriv,abs_div,abs_mul,abs_of_pos positive]
  change |F x| * |F' x| / cmsSmoothModulus F ε x ≤ |F' x|
  apply (div_le_iff₀ positive).2
  simpa only [cmsSmoothModulus,mul_comm] using
    mul_le_mul_of_nonneg_right bounds.1 (abs_nonneg (F' x))

/-- Removing the epsilon floor preserves smoothness and gives a globally
nonnegative approximation bounded ABOVE by the true modulus. -/
theorem cmsSmoothModulus_centered_bounds (F : ℝ → ℝ) {ε : ℝ} (hε : 0<ε) (x : ℝ) :
    0≤cmsSmoothModulus F ε x-ε ∧
      cmsSmoothModulus F ε x-ε≤|F x| ∧
      |F x|-(cmsSmoothModulus F ε x-ε)≤ε := by
  have hs : (cmsSmoothModulus F ε x)^2=(F x)^2+ε^2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg (F x),sq_nonneg ε])
  have hp:=(cmsSmoothModulus_pos F hε x).le
  obtain ⟨lo,hi⟩:=cmsSmoothModulus_bounds F hε x
  refine ⟨?_,?_,?_⟩ <;> nlinarith [sq_nonneg (F x)]

#print axioms cmsSmoothModulus_hasDerivAt
#print axioms cmsSmoothModulusDeriv_continuous
#print axioms cmsSmoothModulus_bounds
#print axioms cmsSmoothModulusDeriv_abs_le
#print axioms cmsSmoothModulus_centered_bounds
end RH080Next.Explicit
