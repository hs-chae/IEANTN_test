/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.NumericalProgram
import DirectIntervalA.Common

namespace DirectIntervalA.Numerical
open Real LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def sigma (i : Fin cells) : ℝ := (sigmaq i : ℝ)
noncomputable def u : ℝ := 66 + log ((201:ℝ)/100)

noncomputable def momentReal (s : ℝ) : ℝ :=
  let b := (8*s-5)/3
  let p := 5-2*s
  let z := b*u
  (1959/200:ℝ)*exp (-b*u+p*log u)/b *
    (1+p/z+p*(p-1)/z^2+p*(p-1)*(p-2)/z^3+p*(p-1)*(p-2)*(p-3)/z^4)+
  (893/200:ℝ)*exp (-u)*(u^2+2*u+2)

noncomputable def weight (i : Fin cells) : ℝ :=
  2*k*exp (66-330*(1-sigma i))*(exp ((330:ℝ)/4096)-1)

noncomputable def gridBudget : ℝ := ∑ i : Fin cells, weight i*(momentCap i : ℝ)
noncomputable def actualMomentGrid : ℝ :=
  ∑ i : Fin cells, weight i * moment (sigma i) (U 330)

theorem u_pos : 0<u := by
  have hk : 0 ≤ log ((201:ℝ)/100) := Real.log_nonneg (by norm_num)
  dsimp [u]
  linarith

theorem U330_exp : U 330=exp u := by
  unfold U u
  norm_num only [show (330:ℝ)/5=66 by norm_num]
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<201/100)]
  ring

theorem log_U330 : log (U 330)=u := by rw [U330_exp,Real.log_exp]

theorem momentReal_eq (s : ℝ) : momentReal s=moment s (U 330) := by
  have hU : 0<U 330 := by rw [U330_exp]; positivity
  have hb : 1-8*(1-s)/3=(8*s-5)/3 := by ring
  have hm : (U 330)^(8*(1-s)/3-1) * log (U 330)^(5-2*s)=
      exp (-((8*s-5)/3)*u+(5-2*s)*log u) := by
    rw [Real.rpow_def_of_pos hU,log_U330,Real.rpow_def_of_pos u_pos,←Real.exp_add]
    congr 1
    ring
  unfold moment CH2QRH.densityMomentMain
  dsimp only
  rw [hm,hb,log_U330,U330_exp]
  unfold momentReal
  rw [Real.exp_neg]
  ring

theorem momentExpr_semantics (s : Expr) (env : ℕ→ℝ) :
    Expr.eval env (momentExpr s)=momentReal (Expr.eval env s) := by
  simp only [momentExpr,momentReal,uExpr,u,Expr.eval,powE,lit,add,mul,sub,divE,kq,
    WinnerProgramA.sub,WinnerProgramA.divE]
  push_cast
  ring

theorem momentRow_semantics (i : Fin cells) :
    rowValue (momentRow i)=moment (sigma i) (U 330) := by
  simp only [rowValue,momentRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton]
  rw [momentExpr_semantics]
  simp only [lit,Expr.eval,←momentReal_eq,sigma]

theorem weightExpr_semantics (i : Fin cells) (env : ℕ→ℝ) :
    Expr.eval env (weightExpr i)=weight i := by
  simp only [weightExpr,Expr.eval,lit,add,mul,sub,WinnerProgramA.sub,weight,sigma,kq,stepq,k]
  push_cast
  norm_num [sub_eq_add_neg]
  <;> ring

theorem weightedExpr_semantics (i : Fin cells) (env : ℕ→ℝ) :
    Expr.eval env (weightedExpr i)=weight i*(momentCap i:ℝ) := by
  simp only [weightedExpr,Expr.eval,mul,lit,weightExpr_semantics]

theorem sumExpr_semantics (es : List Expr) (env : ℕ→ℝ) :
    Expr.eval env (sumExpr es)=(es.map (Expr.eval env)).sum := by
  induction es with
  | nil => simp [sumExpr,lit,Expr.eval]
  | cons e es ih => simp [sumExpr,add,Expr.eval,ih]

theorem budget_semantics : value budgetProgram=gridBudget := by
  simp only [value,budgetProgram,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rowValue,budgetRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton]
  rw [budgetExpr,sumExpr_semantics,List.map_ofFn,List.sum_ofFn]
  unfold gridBudget
  apply Finset.sum_congr rfl
  intro i _
  exact weightedExpr_semantics i _

theorem weight_nonneg (i : Fin cells) : 0≤weight i := by
  unfold weight
  apply mul_nonneg
  · positivity
  · exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))

end DirectIntervalA.Numerical
