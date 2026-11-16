/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalSharpScalars
namespace WinnerOriginalScalars
open Real LeanCert.Core
set_option maxHeartbeats 0

def amplitudeFloor : Expr := add
  (dv (mul (lit 6) (lit (309/500))) (.exp (lit 1))) (lit (1461/1000))

theorem amplitude_floor_check : value amplitudeFloor≤1413/500 := by
  have h := closed_upper amplitudeFloor (1413/500) (by native_decide)
  norm_num at h ⊢
  exact h

theorem amplitude_floor_upper : (6:ℝ)*(309/500)/exp 1+1461/1000≤1413/500 := by
  simpa [amplitudeFloor] using amplitude_floor_check

#print axioms amplitude_floor_upper
end WinnerOriginalScalars
