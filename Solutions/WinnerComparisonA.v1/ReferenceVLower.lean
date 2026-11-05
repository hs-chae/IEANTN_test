/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalSharpScalars
namespace WinnerOriginalScalars.Reference
open Real LeanCert.Core
set_option maxHeartbeats 0
abbrev aRef : Expr := lit (2371/20000)
abbrev dRef : Expr := lit (3599/10000)
def cFiveFloor (v : ℚ) : Expr :=
  let L := add h (lit v)
  mul (mul (dv (mul (mul pival mzero) (lit (529/1000))) (mul (lit 2) dRef))
    (sq (add (lit 1) (dv (mul (lit 2) dRef) L)))) (.exp (dv dRef L))
def cSixFloor (v : ℚ) : Expr :=
  let L := add h (lit v)
  add (mul (mul (dv (lit (529/1000)) (mul (mul (lit 5) dRef) (.exp dRef)))
    (sq (add (lit 1) (dv dRef L))))
    (.exp (dv (mul dRef (sub (lit (1/2)) (.log (lit 5)))) h)))
    (dv (mul (lit (121/200)) (.exp (.neg (mul (lit 2) dRef)))) (sq L))
def vFloor (v : ℚ) : Expr := add (mul (lit 2) (cFiveFloor v))
  (mul (dv (rt pival) (rt (mul (lit 2) aRef))) (cSixFloor v))

noncomputable def sourceCFiveFloor (v : ℝ) : ℝ :=
  Real.pi*sourceM0*(529/1000)/(2*(3599/10000))*
    (1+2*(3599/10000)/(log height+v))^2*exp ((3599/10000)/(log height+v))
noncomputable def sourceCSixFloor (v : ℝ) : ℝ :=
  (529/1000)/(5*(3599/10000)*exp (3599/10000))*
    (1+(3599/10000)/(log height+v))^2*
      exp ((3599/10000)*(1/2-log 5)/log height)+
    (121/200)*exp (-2*(3599/10000))/(log height+v)^2
noncomputable def sourceVFloor (v : ℝ) : ℝ :=
  2*sourceCFiveFloor v+sqrt Real.pi/sqrt (2*(2371/20000))*sourceCSixFloor v

theorem cfive_floor_semantics (v : ℚ) : value (cFiveFloor v)=sourceCFiveFloor v := by
  simp [cFiveFloor,sourceCFiveFloor,dRef,mzero_semantics,log_semantics]

theorem csix_floor_semantics (v : ℚ) : value (cSixFloor v)=sourceCSixFloor v := by
  simp [cSixFloor,sourceCSixFloor,dRef,log_semantics]

theorem vfloor_semantics (v : ℚ) : value (vFloor v)=sourceVFloor v := by
  simp only [vFloor,value_add,value_mul,value_div,value_lit,cfive_floor_semantics,csix_floor_semantics]
  rw [value_rt _ (by simp;exact Real.pi_pos),value_rt _ (by norm_num [aRef])]
  simp [sourceVFloor,aRef]

theorem lower_one : (36/5:ℝ)≤sourceVFloor 1 := by
  have h := closed_lower (vFloor 1) (36/5) (by native_decide)
  simpa [vfloor_semantics] using h

theorem lower_two : (719/100:ℝ)≤sourceVFloor 2 := by
  have h := closed_lower (vFloor 2) (719/100) (by native_decide)
  simpa [vfloor_semantics] using h

theorem lower_four : (179/25:ℝ)≤sourceVFloor 4 := by
  have h := closed_lower (vFloor 4) (179/25) (by native_decide)
  simpa [vfloor_semantics] using h

theorem lower_eight : (178/25:ℝ)≤sourceVFloor 8 := by
  have h := closed_lower (vFloor 8) (178/25) (by native_decide)
  simpa [vfloor_semantics] using h

#print axioms lower_one
#print axioms lower_two
#print axioms lower_four
#print axioms lower_eight
end WinnerOriginalScalars.Reference
