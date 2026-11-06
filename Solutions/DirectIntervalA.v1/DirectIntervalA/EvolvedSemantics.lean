/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.EvolvedProgram
import DirectIntervalA.NumericalIntegral
import DirectIntervalA.MomentRay

namespace DirectIntervalA.Evolved
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

noncomputable def sigma (i : Fin cells) : ℝ := (sigmaq i:ℝ)
noncomputable def factorReal (s : ℝ) : ℝ :=
  exp ((1-b s)*log k+q s*log Numerical.u)/b s*factor4 s Numerical.u
noncomputable def weight (i : Fin cells) : ℝ :=
  (2*(1959/200:ℝ)*330/154)*exp (-154*(1-sigma i))*(exp ((154:ℝ)/512)-1)
noncomputable def correction : ℝ :=
  2*(893/200:ℝ)*(Numerical.u^2+2*Numerical.u+2)*(exp (-(330:ℝ)/8)-exp (-(330:ℝ)/4))
noncomputable def gridBudget : ℝ :=
  (∑i:Fin cells,weight i*(momentCap i:ℝ))+correction
noncomputable def actualGrid : ℝ :=
  (∑i:Fin cells,weight i*factorReal (sigma i))+correction

 theorem b_eq (s : ℝ) : b s=(8*s-5)/3 := by unfold b p;ring
 theorem u_ge_one : 1≤Numerical.u := by
  have hk : 0≤log ((201:ℝ)/100) := log_nonneg (by norm_num)
  dsimp [Numerical.u]
  linarith

 theorem factorExpr_semantics (s : Expr) (env : ℕ→ℝ) :
    Expr.eval env (factorExpr s)=factorReal (Expr.eval env s) := by
  simp only [factorExpr,factorReal,factor4,q,b_eq,Numerical.uExpr,Numerical.u,Expr.eval,
    powE,lit,add,mul,sub,divE,Numerical.kq,k,WinnerProgramA.sub,WinnerProgramA.divE]
  push_cast
  ring

 theorem momentRow_semantics (i : Fin cells) : rowValue (momentRow i)=factorReal (sigma i) := by
  simp only [rowValue,momentRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton]
  rw [factorExpr_semantics]
  rfl

 theorem weightExpr_semantics (i : Fin cells) (env : ℕ→ℝ) : Expr.eval env (weightExpr i)=weight i := by
  simp only [weightExpr,Expr.eval,lit,add,mul,sub,WinnerProgramA.sub,weight,sigma]
  push_cast
  norm_num [sub_eq_add_neg]
  <;> ring

 theorem correctionExpr_semantics (env : ℕ→ℝ) : Expr.eval env correctionExpr=correction := by
  simp only [correctionExpr,correction,Numerical.uExpr,Numerical.u,Expr.eval,lit,add,mul,sub,
    powE,WinnerProgramA.sub,Numerical.kq]
  push_cast
  norm_num [sub_eq_add_neg]
  <;> ring

 theorem weightedExpr_semantics (i : Fin cells) (env : ℕ→ℝ) :
    Expr.eval env (weightedExpr i)=weight i*(momentCap i:ℝ) := by
  simp only [weightedExpr,Expr.eval,mul,lit,weightExpr_semantics]

 theorem budget_semantics : value budgetProgram=gridBudget := by
  simp only [value,budgetProgram,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
    rowValue,budgetRow,Nat.sub_self,Finset.Icc_self,Finset.sum_singleton,budgetExpr,Expr.eval,add]
  rw [Numerical.sumExpr_semantics,List.map_ofFn,List.sum_ofFn,correctionExpr_semantics]
  unfold gridBudget
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact weightedExpr_semantics i _

 theorem weight_nonneg (i : Fin cells) : 0≤weight i := by
  unfold weight
  apply mul_nonneg
  · positivity
  · exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))

 theorem factor_nonneg {s : ℝ} (hs : s∈Icc (3/4:ℝ) (7/8:ℝ)) : 0≤factorReal s := by
  have hb : 0<b s := by unfold b p;linarith [hs.1]
  have hf := factor4_nonneg hs Numerical.u_pos
  unfold factorReal
  positivity

 theorem factor_continuous : ContinuousOn factorReal (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs
  have hb : b s≠0 := by unfold b p;linarith [hs.1]
  have hu : Numerical.u≠0 := Numerical.u_pos.ne'
  have hbu : b s*Numerical.u≠0 := mul_ne_zero hb hu
  unfold factorReal factor4 b p q
  fun_prop (disch := first | assumption | positivity)

 theorem factor_antitone : AntitoneOn factorReal (Icc (3/4:ℝ) (7/8:ℝ)) := by
  intro s hs t ht hst
  have hbs : 0<b s := by unfold b p;linarith [hs.1]
  have hbt : 0<b t := by unfold b p;linarith [ht.1]
  have hb : b s≤b t := by unfold b p;linarith
  have hu : 0<Numerical.u := Numerical.u_pos
  have hlu : 0≤log Numerical.u := log_nonneg u_ge_one
  have hlk : 0≤log k := log_nonneg (by norm_num [k])
  have hq0 : 0≤q t := by unfold q;linarith [ht.2]
  have hq1 : 0≤q t-1 := by unfold q;linarith [ht.2]
  have hq2 : 0≤q t-2 := by unfold q;linarith [ht.2]
  have hq3 : 0≤q t-3 := by unfold q;linarith [ht.2]
  have hq : q t≤q s := by unfold q;linarith
  have hqs0 : 0≤q s := hq0.trans hq
  have hqs1 : 0≤q s-1 := by linarith
  have hqs2 : 0≤q s-2 := by linarith
  have hqs3 : 0≤q s-3 := by linarith
  have hF : factor4 t Numerical.u≤factor4 s Numerical.u := by
    unfold factor4
    gcongr <;> first | positivity | linarith
  have hex : exp ((1-b t)*log k+q t*log Numerical.u)≤
      exp ((1-b s)*log k+q s*log Numerical.u) := by
    apply exp_le_exp.mpr
    nlinarith
  have hdiv : exp ((1-b t)*log k+q t*log Numerical.u)/b t≤
      exp ((1-b s)*log k+q s*log Numerical.u)/b s := by
    exact div_le_div₀ (exp_pos _).le hex hbs hb
  unfold factorReal
  exact mul_le_mul hdiv hF (factor4_nonneg ht hu) (by positivity)

end DirectIntervalA.Evolved
#print axioms DirectIntervalA.Evolved.factor_antitone
