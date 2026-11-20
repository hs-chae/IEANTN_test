/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.CoupledIntegralEnvelope

/-! Exact scalar comparison for a prospective common-integral application.
Every analytic guard below must be proved by the application. This module
neither asserts a numerical transition point nor supplies an analytic input. -/
namespace RamanujanPV.CoupledScalarComparison
set_option autoImplicit false

/-- Retaining the shared integral absorbs the change from 1.95 to 1.945
and keeps an additional q/1000. The constants and all guards are exact. -/
theorem comparison {A B k q S U J : ℝ}
    (hq : 0 ≤ q) (hU : 0 ≤ U) (hJ : 0 ≤ J)
    (hS : S ≤ (3/4)*q) (hUq : U ≤ (131/1000)*q)
    (hB : (94/125) ≤ 2*k*B)
    (hSmall : k*(q/20+U+J) ≤ (1/1000)) :
    A-(389/200)*S-k*B^2+q/1000 ≤
      A-(39/20)*S-U-k*(B-(q/20+U+J))^2 := by
  let Z := q/20+U+J
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hcoeff : (3/4:ℝ) ≤ 2*k*B-k*Z := by
    dsimp [Z]
    linarith
  have hproduct := mul_le_mul_of_nonneg_right hcoeff hZ
  have hgain : (3/4)*Z ≤ k*Z*(2*B-Z) := by nlinarith
  have hlinear : q/1000 ≤ -(1/200)*S-U+(3/4)*Z := by
    dsimp [Z]
    linarith
  have identity :
      (A-(39/20)*S-U-k*(B-Z)^2) - (A-(389/200)*S-k*B^2) =
      -(1/200)*S-U+k*Z*(2*B-Z) := by ring
  change A-(389/200)*S-k*B^2+q/1000 ≤ A-(39/20)*S-U-k*(B-Z)^2
  linarith

#print axioms comparison
end RamanujanPV.CoupledScalarComparison
