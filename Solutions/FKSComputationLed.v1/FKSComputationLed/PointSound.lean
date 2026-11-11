/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.CellProgram
open LeanCert.Core LeanCert.Engine Real
namespace FKSComputationLed.PointSound
open PointProgram CellProgram

lemma prepared_mem (e : Expr) (ρr : Nat→ℝ) (ρd : IntervalDyadicEnv)
    (hρ : envMemDyadic ρr ρd)
    (hv : (LeanCert.Internal.Dyadic.evalPreparedCached e ρd ctx).2=true) :
    Expr.eval ρr e ∈ (LeanCert.Internal.Dyadic.evalPreparedCached e ρd ctx).1 := by
  have hd : checkDomainValidDyadic e ρd cfg=true := by
    simpa only [ctx,evalIntervalDyadicPreparedCached_snd] using hv
  change Expr.eval ρr e ∈
    (LeanCert.Internal.Dyadic.evalPreparedCached e ρd
      (LeanCert.Internal.Dyadic.prepareContext cfg)).1
  rw [evalIntervalDyadicPreparedCached_fst e ρd cfg]
  exact evalIntervalDyadic_correct_of_domain e ρr ρd hρ cfg (by decide)
    (checkDomainValidDyadic_correct e ρd cfg hd)
lemma integer_mem (n : Nat) : (n:ℝ)∈integerInterval n := by
  simp [integerInterval,IntervalDyadic.mem_def,IntervalDyadic.singleton,
    LeanCert.Core.Dyadic.toRat_ofInt]
lemma log_mem (n : Nat) (hv : (logPoint n).2=true) :
    log (n:ℝ)∈(logPoint n).1 := by
  have hh := prepared_mem (.log (.var 0)) (fun _=>(n:ℝ))
    (fun _=>integerInterval n) (fun _=>integer_mem n) hv
  change log (n:ℝ)∈(LeanCert.Internal.Dyadic.evalPreparedCached (.log (.var 0)) (fun _=>integerInterval n) ctx).1
  simpa only [Expr.eval_log,Expr.eval_var] using hh
lemma primitive_mem (n : Nat) (hlog : (logPoint n).2=true)
    (hv : (primitivePoint n).2=true) :
    LiTaylor.primitive 79 (log (n:ℝ))∈(primitivePoint n).1 := by
  have hh := prepared_mem primitiveExpr (fun _=>log (n:ℝ))
    (fun _=>(logPoint n).1) (fun _=>log_mem n hlog) hv
  change LiTaylor.primitive 79 (log (n:ℝ))∈(LeanCert.Internal.Dyadic.evalPreparedCached primitiveExpr (fun _=>(logPoint n).1) ctx).1
  simpa only [primitiveExpr_value] using hh
lemma log_two_valid : (logPoint 2).2=true := by
  unfold logPoint run ctx
  rw [evalIntervalDyadicPreparedCached_snd (.log (.var 0)) (fun _=>integerInterval 2) cfg]
  norm_num [checkDomainValidDyadic,LeanCert.Internal.Dyadic.evalUnchecked,
    integerInterval,IntervalDyadic.toIntervalRat,IntervalDyadic.singleton,
    LeanCert.Core.Dyadic.toRat_ofInt]

/-- Point helper correctness includes the actual interval program and every checked domain. -/
theorem pointInfo_sound (n : Nat) (hv : (pointInfo n).valid=true) :
    2≤n ∧ 2≤log (n:ℝ) ∧ log (n:ℝ)≤24 ∧
    LiTaylor.Li2 (n:ℝ)∈(pointInfo n).liI ∧
    log (n:ℝ)/sqrt (n:ℝ)∈(pointInfo n).weightI := by
  simp only [pointInfo,Bool.and_eq_true,and_assoc] at hv
  rcases hv with ⟨hn,hl,hp,hb,hs,hw,hlo,hhi⟩
  have hn' : 2≤n := of_decide_eq_true hn
  have hlog := log_mem n hl
  have hlo' : (2:ℝ)≤log (n:ℝ) :=
    (IntervalDyadic.lowerBoundedBy_spec hlo).trans (IntervalDyadic.lo_le_of_mem hlog)
  have hhi' : log (n:ℝ)≤24 :=
    (IntervalDyadic.le_hi_of_mem hlog).trans (IntervalDyadic.upperBoundedBy_spec hhi)
  have hFn := primitive_mem n hl hp
  have hFb := primitive_mem 2 log_two_valid hb
  norm_num only [Nat.cast_ofNat] at hFb
  have hnr : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn'
  have hn0 : (0:ℝ)<(n:ℝ) := by linarith
  have hE : |LiTaylor.Li2 (n:ℝ) -
      (LiTaylor.primitive 79 (log (n:ℝ))-LiTaylor.primitive 79 (log (2:ℝ)))| ≤ (eps:ℝ) := by
    simpa [eps] using LiTaylor.Li2_approx hnr hhi'
  have hEmem : (LiTaylor.Li2 (n:ℝ)-
      (LiTaylor.primitive 79 (log (n:ℝ))-LiTaylor.primitive 79 (log (2:ℝ))))∈errorInterval := by
    apply IntervalDyadic.mem_ofIntervalRat _ cfg.precision (by decide)
    simpa only [IntervalRat.mem_def,Rat.cast_neg] using abs_le.mp hE
  have hLi := IntervalDyadic.mem_add (IntervalDyadic.mem_sub hFn hFb) hEmem
  have hcancel : LiTaylor.primitive 79 (log (n:ℝ))-LiTaylor.primitive 79 (log (2:ℝ))+
      (LiTaylor.Li2 (n:ℝ)-(LiTaylor.primitive 79 (log (n:ℝ))-LiTaylor.primitive 79 (log (2:ℝ))))
      = LiTaylor.Li2 (n:ℝ) := by ring
  rw [hcancel] at hLi
  have hLimem : LiTaylor.Li2 (n:ℝ)∈(pointInfo n).liI := by
    change LiTaylor.Li2 (n:ℝ)∈IntervalDyadic.add
      (IntervalDyadic.sub (primitivePoint n).1 base.1) errorInterval
    simpa only [base] using hLi
  have hsq := prepared_mem (.exp (.mul (.const (1/2)) (.var 0)))
    (fun _=>log (n:ℝ)) (fun _=>(logPoint n).1) (fun _=>hlog) hs
  have hsqrteq : sqrt (n:ℝ)=exp ((1/2:ℝ)*log (n:ℝ)) := by
    rw [sqrt_eq_rpow,Real.rpow_def_of_pos hn0]
    congr 1
    ring
  have hsqmem : sqrt (n:ℝ)∈
      (run (.exp (.mul (.const (1/2)) (.var 0))) (logPoint n).1).1 := by
    simpa only [Expr.eval_exp,Expr.eval_mul,Expr.eval_const,Expr.eval_var,
      Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,←hsqrteq] using hsq
  have hwm := prepared_mem (.mul (.var 0) (.inv (.var 1)))
    (fun i=>if i=0 then log (n:ℝ) else sqrt (n:ℝ))
    (fun i=>if i=0 then (logPoint n).1 else
      (run (.exp (.mul (.const (1/2)) (.var 0))) (logPoint n).1).1)
    (by
      intro i
      by_cases hi:i=0
      · simpa only [if_pos hi] using hlog
      · simpa only [if_neg hi] using hsqmem) hw
  refine ⟨hn',hlo',hhi',hLimem,?_⟩
  have heval : Expr.eval (fun i=>if i=0 then log (n:ℝ) else sqrt (n:ℝ))
      (.mul (.var 0) (.inv (.var 1))) = log (n:ℝ)/sqrt (n:ℝ) := by
    norm_num [Expr.eval,div_eq_mul_inv]
  rw [heval] at hwm
  change log (n:ℝ)/sqrt (n:ℝ) ∈
    (LeanCert.Internal.Dyadic.evalPreparedCached (.mul (.var 0) (.inv (.var 1)))
      (fun i=>if i=0 then (logPoint n).1 else
        (run (.exp (.mul (.const (1/2)) (.var 0))) (logPoint n).1).1) ctx).1
  exact hwm
#print axioms pointInfo_sound
end FKSComputationLed.PointSound
