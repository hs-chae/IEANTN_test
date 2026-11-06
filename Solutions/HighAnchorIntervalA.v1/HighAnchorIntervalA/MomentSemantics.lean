/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.MomentProgram
import HighAnchorIntervalA.Cells
import DirectIntervalA.NumericalIntegral
namespace HighAnchorIntervalA.Numerical
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem factorExpr_semantics (s:Expr) (env:ℕ→ℝ) :
    Expr.eval env (factorExpr s)=HighAnchorIntervalA.factorReal (Expr.eval env s) := by
  rw [HighAnchorIntervalA.factor_alt]
  simp only [factorExpr,uExpr,Expr.eval,powE,lit,add,mul,sub,divE,kq,
    WinnerProgramA.sub,WinnerProgramA.divE,
    HighAnchorIntervalA.u,HighAnchorIntervalA.ulog,HighAnchorIntervalA.eta,
    HighAnchorIntervalA.p,HighAnchorIntervalA.q,HighAnchorIntervalA.b,HighAnchorIntervalA.k,
    DirectIntervalA.factor4,DirectIntervalA.q,DirectIntervalA.b,DirectIntervalA.p]
  push_cast
  ring

theorem momentRow_semantics (i:Fin cells) :
    rowValue (momentRow i)=HighAnchorIntervalA.factorReal (HighAnchorIntervalA.sigma i) := by
  simp only [rowValue,momentRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton]
  rw [factorExpr_semantics]
  rfl

theorem weightExpr_semantics (i:Fin cells) (env:ℕ→ℝ) :
    Expr.eval env (weightExpr i)=HighAnchorIntervalA.weight i := by
  simp only [weightExpr,Expr.eval,lit,add,mul,sub,WinnerProgramA.sub,
    HighAnchorIntervalA.weight,HighAnchorIntervalA.sigma]
  norm_num [Kq,Bq,lambdaq,stepq,Profile.row,Profile.slope,
    HighAnchorIntervalA.lambdaWeight,HighAnchorIntervalA.K,HighAnchorIntervalA.B,
    sigmaq,HighAnchorIntervalA.sigmaq]
  <;> ring

theorem correctionExpr_semantics (env:ℕ→ℝ) :
    Expr.eval env correctionExpr=HighAnchorIntervalA.correction := by
  simp only [correctionExpr,HighAnchorIntervalA.correction,uExpr,Expr.eval,lit,add,mul,sub,powE,
    WinnerProgramA.sub,HighAnchorIntervalA.u,HighAnchorIntervalA.ulog,HighAnchorIntervalA.eta,
    HighAnchorIntervalA.k,kq]
  push_cast
  norm_num [sub_eq_add_neg]
  <;> ring

theorem weightedExpr_semantics (i:Fin cells) (env:ℕ→ℝ) :
    Expr.eval env (weightedExpr i)=HighAnchorIntervalA.weight i*(momentCap i:ℝ) := by
  simp only [weightedExpr,Expr.eval,mul,lit,weightExpr_semantics]

theorem budget_semantics :
    value budgetProgram=HighAnchorIntervalA.gridBudget momentCap := by
  simp only [value,budgetProgram,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rowValue,budgetRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,budgetExpr,Expr.eval,add]
  rw [DirectIntervalA.Numerical.sumExpr_semantics,List.map_ofFn,List.sum_ofFn,correctionExpr_semantics]
  unfold HighAnchorIntervalA.gridBudget
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact weightedExpr_semantics i _

#print axioms factorExpr_semantics
#print axioms budget_semantics
end HighAnchorIntervalA.Numerical
