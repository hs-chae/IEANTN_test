/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalB.Common
import WinnerProgramA.Program
namespace HighAnchorIntervalB.LowNumerical
open Real LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def logExpr : Expr := add (lit (693/10)) (.log (lit (1980000/11)))
def lowExpr : Expr := mul (lit (201/44))
  (mul (.exp (lit (-66/5))) (add logExpr (divE (powE logExpr 2) (lit 2))))
def row : Row := ⟨lowExpr,1⟩
def program : List Row := [row]
def output : IntervalDyadic×Bool := runRow row

theorem execution : Exec program [output] := rfl

noncomputable def value_real : ℝ :=
  (201/44:ℝ)*exp (-66/5)*((693/10:ℝ)+log (1980000/11)+
    ((693/10:ℝ)+log (1980000/11))^2/2)

theorem semantics : value program=value_real := by
  simp only [value,program,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rowValue,row,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton]
  norm_num [lowExpr,logExpr,Expr.eval,lit,add,mul,WinnerProgramA.divE,powE,value_real]
  ring

theorem checked : acceptUpper [output] [(3/100:ℚ)]=true := by native_decide

theorem value_real_le : value_real≤(3/100:ℝ) := by
  have h := source_linked_upper program [output] [(3/100:ℚ)] execution checked
  rw [semantics] at h
  norm_num at h ⊢
  exact h

theorem rejects_small_cap : acceptUpper [output] [(26/1000:ℚ)]=false := by native_decide
#print axioms value_real_le
end HighAnchorIntervalB.LowNumerical
