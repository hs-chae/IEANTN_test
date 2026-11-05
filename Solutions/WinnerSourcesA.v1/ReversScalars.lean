/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ReversAmplitude
namespace WinnerOriginalScalars.Revers
open Real LeanCert.Core
set_option maxHeartbeats 0

def rzeroNew : Expr := dv (lit (281/100)) (mul (mul (lit (611/1000)) rootHeight) h)
def roneNew : Expr := .inv (mul (mul (mul (lit (611/1000)) rootHeight) h) (rt h))
noncomputable def sourceR0New : ℝ := (281/100)/((611/1000)*height^((1:ℝ)/6)*log height)
noncomputable def sourceR1New : ℝ := 1/((611/1000)*height^((1:ℝ)/6)*log height*sqrt (log height))

theorem rzero_new_check : value rzeroNew≤137/100000 := by
  have h := closed_upper rzeroNew (137/100000) (by native_decide)
  norm_num at h ⊢
  exact h

theorem rone_new_check : value roneNew≤47/500000 := by
  have h := closed_upper roneNew (47/500000) (by native_decide)
  norm_num at h ⊢
  exact h

theorem rzero_new_semantics : value rzeroNew=sourceR0New := by
  simp [rzeroNew,sourceR0New,rootHeight_semantics,log_semantics]

theorem rone_new_semantics : value roneNew=sourceR1New := by
  simp only [roneNew,value_inv,value_mul,value_lit,rootHeight_semantics,log_semantics]
  rw [value_rt _ (by rw [log_semantics]; have h:=source_log_lower;linarith)]
  rw [log_semantics]
  norm_num [sourceR1New,one_div]

theorem source_rzero_upper : sourceR0New≤137/100000 := by
  simpa [rzero_new_semantics] using rzero_new_check

theorem source_rone_upper : sourceR1New≤47/500000 := by
  simpa [rone_new_semantics] using rone_new_check

theorem finite_U1286 :
    8*(601/5000:ℝ)*(1000000000001/1000000000000)*(611/1000)^2*(358075/100000)
      ≤643/500 := by norm_num

#print axioms source_rzero_upper
#print axioms source_rone_upper
end WinnerOriginalScalars.Revers
