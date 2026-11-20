/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.FiniteExpSource
import RamanujanPV.QuotientCDeterminism
import RamanujanPV.AnalyticTransition
namespace RamanujanPV.FiniteExpExecute
open LCMSourcePV.Witness.C QuotientCMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
def noCalls : Service := fun _ _ => none
def initial (heap : Heap) : State := ⟨emptyEnv,heap⟩
def termState (heap : Heap) : State := {initial heap with env:=bind (initial heap).env "term" (.u64 1152921504606846976)}
def totalState (heap : Heap) : State := {termState heap with env:=bind (termState heap).env "total" (.u64 1152921504606846976)}
def before_1 (heap : Heap) : State := {totalState heap with env:=bind (totalState heap).env "k" (.u64 1)}
def condition : Expr := .binary "<=" (.var "k") (.nat 20)
def step : Expr := .unary "++" (.var "k")
def divideTerm : Expr := .binary "=" (.var "term") (.binary "/" (.var "term") (.var "k"))
def addTerm : Expr := .binary "=" (.var "total") (.binary "+" (.var "total") (.var "term"))
def iteration : Stmt := .sequence [.eval divideTerm,.eval addTerm]
def after_term_1 (heap : Heap) : State := {before_1 heap with env:=bind (before_1 heap).env "term" (.u64 1152921504606846976)}
def after_sum_1 (heap : Heap) : State := {after_term_1 heap with env:=bind (after_term_1 heap).env "total" (.u64 2305843009213693952)}
def after_body_1 (heap : Heap) : State := closeScope (before_1 heap) (after_sum_1 heap)
def before_2 (heap : Heap) : State := {after_body_1 heap with env:=bind (after_body_1 heap).env "k" (.u64 2)}
theorem divide_1 (heap : Heap) : Eval noCalls divideTerm (before_1 heap) (after_term_1 heap) (.u64 1152921504606846976) := by rfl
theorem add_1 (heap : Heap) : Eval noCalls addTerm (after_term_1 heap) (after_sum_1 heap) (.u64 2305843009213693952) := by rfl
theorem increment_1 (heap : Heap) : Eval noCalls step (after_body_1 heap) (before_2 heap) (.u64 2) := by rfl
theorem guard_1 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_1 heap) (before_1 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_1 (heap : Heap) : Run noCalls iteration (before_1 heap) (.continuing (after_body_1 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_1 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_1 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_1 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_2 (heap : Heap) : State := {before_2 heap with env:=bind (before_2 heap).env "term" (.u64 576460752303423488)}
def after_sum_2 (heap : Heap) : State := {after_term_2 heap with env:=bind (after_term_2 heap).env "total" (.u64 2882303761517117440)}
def after_body_2 (heap : Heap) : State := closeScope (before_2 heap) (after_sum_2 heap)
def before_3 (heap : Heap) : State := {after_body_2 heap with env:=bind (after_body_2 heap).env "k" (.u64 3)}
theorem divide_2 (heap : Heap) : Eval noCalls divideTerm (before_2 heap) (after_term_2 heap) (.u64 576460752303423488) := by rfl
theorem add_2 (heap : Heap) : Eval noCalls addTerm (after_term_2 heap) (after_sum_2 heap) (.u64 2882303761517117440) := by rfl
theorem increment_2 (heap : Heap) : Eval noCalls step (after_body_2 heap) (before_3 heap) (.u64 3) := by rfl
theorem guard_2 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_2 heap) (before_2 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_2 (heap : Heap) : Run noCalls iteration (before_2 heap) (.continuing (after_body_2 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_2 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_2 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_2 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_3 (heap : Heap) : State := {before_3 heap with env:=bind (before_3 heap).env "term" (.u64 192153584101141162)}
def after_sum_3 (heap : Heap) : State := {after_term_3 heap with env:=bind (after_term_3 heap).env "total" (.u64 3074457345618258602)}
def after_body_3 (heap : Heap) : State := closeScope (before_3 heap) (after_sum_3 heap)
def before_4 (heap : Heap) : State := {after_body_3 heap with env:=bind (after_body_3 heap).env "k" (.u64 4)}
theorem divide_3 (heap : Heap) : Eval noCalls divideTerm (before_3 heap) (after_term_3 heap) (.u64 192153584101141162) := by rfl
theorem add_3 (heap : Heap) : Eval noCalls addTerm (after_term_3 heap) (after_sum_3 heap) (.u64 3074457345618258602) := by rfl
theorem increment_3 (heap : Heap) : Eval noCalls step (after_body_3 heap) (before_4 heap) (.u64 4) := by rfl
theorem guard_3 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_3 heap) (before_3 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_3 (heap : Heap) : Run noCalls iteration (before_3 heap) (.continuing (after_body_3 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_3 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_3 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_3 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_4 (heap : Heap) : State := {before_4 heap with env:=bind (before_4 heap).env "term" (.u64 48038396025285290)}
def after_sum_4 (heap : Heap) : State := {after_term_4 heap with env:=bind (after_term_4 heap).env "total" (.u64 3122495741643543892)}
def after_body_4 (heap : Heap) : State := closeScope (before_4 heap) (after_sum_4 heap)
def before_5 (heap : Heap) : State := {after_body_4 heap with env:=bind (after_body_4 heap).env "k" (.u64 5)}
theorem divide_4 (heap : Heap) : Eval noCalls divideTerm (before_4 heap) (after_term_4 heap) (.u64 48038396025285290) := by rfl
theorem add_4 (heap : Heap) : Eval noCalls addTerm (after_term_4 heap) (after_sum_4 heap) (.u64 3122495741643543892) := by rfl
theorem increment_4 (heap : Heap) : Eval noCalls step (after_body_4 heap) (before_5 heap) (.u64 5) := by rfl
theorem guard_4 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_4 heap) (before_4 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_4 (heap : Heap) : Run noCalls iteration (before_4 heap) (.continuing (after_body_4 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_4 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_4 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_4 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_5 (heap : Heap) : State := {before_5 heap with env:=bind (before_5 heap).env "term" (.u64 9607679205057058)}
def after_sum_5 (heap : Heap) : State := {after_term_5 heap with env:=bind (after_term_5 heap).env "total" (.u64 3132103420848600950)}
def after_body_5 (heap : Heap) : State := closeScope (before_5 heap) (after_sum_5 heap)
def before_6 (heap : Heap) : State := {after_body_5 heap with env:=bind (after_body_5 heap).env "k" (.u64 6)}
theorem divide_5 (heap : Heap) : Eval noCalls divideTerm (before_5 heap) (after_term_5 heap) (.u64 9607679205057058) := by rfl
theorem add_5 (heap : Heap) : Eval noCalls addTerm (after_term_5 heap) (after_sum_5 heap) (.u64 3132103420848600950) := by rfl
theorem increment_5 (heap : Heap) : Eval noCalls step (after_body_5 heap) (before_6 heap) (.u64 6) := by rfl
theorem guard_5 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_5 heap) (before_5 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_5 (heap : Heap) : Run noCalls iteration (before_5 heap) (.continuing (after_body_5 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_5 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_5 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_5 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_6 (heap : Heap) : State := {before_6 heap with env:=bind (before_6 heap).env "term" (.u64 1601279867509509)}
def after_sum_6 (heap : Heap) : State := {after_term_6 heap with env:=bind (after_term_6 heap).env "total" (.u64 3133704700716110459)}
def after_body_6 (heap : Heap) : State := closeScope (before_6 heap) (after_sum_6 heap)
def before_7 (heap : Heap) : State := {after_body_6 heap with env:=bind (after_body_6 heap).env "k" (.u64 7)}
theorem divide_6 (heap : Heap) : Eval noCalls divideTerm (before_6 heap) (after_term_6 heap) (.u64 1601279867509509) := by rfl
theorem add_6 (heap : Heap) : Eval noCalls addTerm (after_term_6 heap) (after_sum_6 heap) (.u64 3133704700716110459) := by rfl
theorem increment_6 (heap : Heap) : Eval noCalls step (after_body_6 heap) (before_7 heap) (.u64 7) := by rfl
theorem guard_6 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_6 heap) (before_6 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_6 (heap : Heap) : Run noCalls iteration (before_6 heap) (.continuing (after_body_6 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_6 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_6 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_6 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_7 (heap : Heap) : State := {before_7 heap with env:=bind (before_7 heap).env "term" (.u64 228754266787072)}
def after_sum_7 (heap : Heap) : State := {after_term_7 heap with env:=bind (after_term_7 heap).env "total" (.u64 3133933454982897531)}
def after_body_7 (heap : Heap) : State := closeScope (before_7 heap) (after_sum_7 heap)
def before_8 (heap : Heap) : State := {after_body_7 heap with env:=bind (after_body_7 heap).env "k" (.u64 8)}
theorem divide_7 (heap : Heap) : Eval noCalls divideTerm (before_7 heap) (after_term_7 heap) (.u64 228754266787072) := by rfl
theorem add_7 (heap : Heap) : Eval noCalls addTerm (after_term_7 heap) (after_sum_7 heap) (.u64 3133933454982897531) := by rfl
theorem increment_7 (heap : Heap) : Eval noCalls step (after_body_7 heap) (before_8 heap) (.u64 8) := by rfl
theorem guard_7 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_7 heap) (before_7 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_7 (heap : Heap) : Run noCalls iteration (before_7 heap) (.continuing (after_body_7 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_7 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_7 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_7 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_8 (heap : Heap) : State := {before_8 heap with env:=bind (before_8 heap).env "term" (.u64 28594283348384)}
def after_sum_8 (heap : Heap) : State := {after_term_8 heap with env:=bind (after_term_8 heap).env "total" (.u64 3133962049266245915)}
def after_body_8 (heap : Heap) : State := closeScope (before_8 heap) (after_sum_8 heap)
def before_9 (heap : Heap) : State := {after_body_8 heap with env:=bind (after_body_8 heap).env "k" (.u64 9)}
theorem divide_8 (heap : Heap) : Eval noCalls divideTerm (before_8 heap) (after_term_8 heap) (.u64 28594283348384) := by rfl
theorem add_8 (heap : Heap) : Eval noCalls addTerm (after_term_8 heap) (after_sum_8 heap) (.u64 3133962049266245915) := by rfl
theorem increment_8 (heap : Heap) : Eval noCalls step (after_body_8 heap) (before_9 heap) (.u64 9) := by rfl
theorem guard_8 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_8 heap) (before_8 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_8 (heap : Heap) : Run noCalls iteration (before_8 heap) (.continuing (after_body_8 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_8 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_8 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_8 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_9 (heap : Heap) : State := {before_9 heap with env:=bind (before_9 heap).env "term" (.u64 3177142594264)}
def after_sum_9 (heap : Heap) : State := {after_term_9 heap with env:=bind (after_term_9 heap).env "total" (.u64 3133965226408840179)}
def after_body_9 (heap : Heap) : State := closeScope (before_9 heap) (after_sum_9 heap)
def before_10 (heap : Heap) : State := {after_body_9 heap with env:=bind (after_body_9 heap).env "k" (.u64 10)}
theorem divide_9 (heap : Heap) : Eval noCalls divideTerm (before_9 heap) (after_term_9 heap) (.u64 3177142594264) := by rfl
theorem add_9 (heap : Heap) : Eval noCalls addTerm (after_term_9 heap) (after_sum_9 heap) (.u64 3133965226408840179) := by rfl
theorem increment_9 (heap : Heap) : Eval noCalls step (after_body_9 heap) (before_10 heap) (.u64 10) := by rfl
theorem guard_9 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_9 heap) (before_9 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_9 (heap : Heap) : Run noCalls iteration (before_9 heap) (.continuing (after_body_9 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_9 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_9 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_9 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_10 (heap : Heap) : State := {before_10 heap with env:=bind (before_10 heap).env "term" (.u64 317714259426)}
def after_sum_10 (heap : Heap) : State := {after_term_10 heap with env:=bind (after_term_10 heap).env "total" (.u64 3133965544123099605)}
def after_body_10 (heap : Heap) : State := closeScope (before_10 heap) (after_sum_10 heap)
def before_11 (heap : Heap) : State := {after_body_10 heap with env:=bind (after_body_10 heap).env "k" (.u64 11)}
theorem divide_10 (heap : Heap) : Eval noCalls divideTerm (before_10 heap) (after_term_10 heap) (.u64 317714259426) := by rfl
theorem add_10 (heap : Heap) : Eval noCalls addTerm (after_term_10 heap) (after_sum_10 heap) (.u64 3133965544123099605) := by rfl
theorem increment_10 (heap : Heap) : Eval noCalls step (after_body_10 heap) (before_11 heap) (.u64 11) := by rfl
theorem guard_10 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_10 heap) (before_10 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_10 (heap : Heap) : Run noCalls iteration (before_10 heap) (.continuing (after_body_10 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_10 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_10 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_10 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_11 (heap : Heap) : State := {before_11 heap with env:=bind (before_11 heap).env "term" (.u64 28883114493)}
def after_sum_11 (heap : Heap) : State := {after_term_11 heap with env:=bind (after_term_11 heap).env "total" (.u64 3133965573006214098)}
def after_body_11 (heap : Heap) : State := closeScope (before_11 heap) (after_sum_11 heap)
def before_12 (heap : Heap) : State := {after_body_11 heap with env:=bind (after_body_11 heap).env "k" (.u64 12)}
theorem divide_11 (heap : Heap) : Eval noCalls divideTerm (before_11 heap) (after_term_11 heap) (.u64 28883114493) := by rfl
theorem add_11 (heap : Heap) : Eval noCalls addTerm (after_term_11 heap) (after_sum_11 heap) (.u64 3133965573006214098) := by rfl
theorem increment_11 (heap : Heap) : Eval noCalls step (after_body_11 heap) (before_12 heap) (.u64 12) := by rfl
theorem guard_11 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_11 heap) (before_11 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_11 (heap : Heap) : Run noCalls iteration (before_11 heap) (.continuing (after_body_11 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_11 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_11 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_11 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_12 (heap : Heap) : State := {before_12 heap with env:=bind (before_12 heap).env "term" (.u64 2406926207)}
def after_sum_12 (heap : Heap) : State := {after_term_12 heap with env:=bind (after_term_12 heap).env "total" (.u64 3133965575413140305)}
def after_body_12 (heap : Heap) : State := closeScope (before_12 heap) (after_sum_12 heap)
def before_13 (heap : Heap) : State := {after_body_12 heap with env:=bind (after_body_12 heap).env "k" (.u64 13)}
theorem divide_12 (heap : Heap) : Eval noCalls divideTerm (before_12 heap) (after_term_12 heap) (.u64 2406926207) := by rfl
theorem add_12 (heap : Heap) : Eval noCalls addTerm (after_term_12 heap) (after_sum_12 heap) (.u64 3133965575413140305) := by rfl
theorem increment_12 (heap : Heap) : Eval noCalls step (after_body_12 heap) (before_13 heap) (.u64 13) := by rfl
theorem guard_12 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_12 heap) (before_12 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_12 (heap : Heap) : Run noCalls iteration (before_12 heap) (.continuing (after_body_12 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_12 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_12 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_12 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_13 (heap : Heap) : State := {before_13 heap with env:=bind (before_13 heap).env "term" (.u64 185148169)}
def after_sum_13 (heap : Heap) : State := {after_term_13 heap with env:=bind (after_term_13 heap).env "total" (.u64 3133965575598288474)}
def after_body_13 (heap : Heap) : State := closeScope (before_13 heap) (after_sum_13 heap)
def before_14 (heap : Heap) : State := {after_body_13 heap with env:=bind (after_body_13 heap).env "k" (.u64 14)}
theorem divide_13 (heap : Heap) : Eval noCalls divideTerm (before_13 heap) (after_term_13 heap) (.u64 185148169) := by rfl
theorem add_13 (heap : Heap) : Eval noCalls addTerm (after_term_13 heap) (after_sum_13 heap) (.u64 3133965575598288474) := by rfl
theorem increment_13 (heap : Heap) : Eval noCalls step (after_body_13 heap) (before_14 heap) (.u64 14) := by rfl
theorem guard_13 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_13 heap) (before_13 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_13 (heap : Heap) : Run noCalls iteration (before_13 heap) (.continuing (after_body_13 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_13 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_13 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_13 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_14 (heap : Heap) : State := {before_14 heap with env:=bind (before_14 heap).env "term" (.u64 13224869)}
def after_sum_14 (heap : Heap) : State := {after_term_14 heap with env:=bind (after_term_14 heap).env "total" (.u64 3133965575611513343)}
def after_body_14 (heap : Heap) : State := closeScope (before_14 heap) (after_sum_14 heap)
def before_15 (heap : Heap) : State := {after_body_14 heap with env:=bind (after_body_14 heap).env "k" (.u64 15)}
theorem divide_14 (heap : Heap) : Eval noCalls divideTerm (before_14 heap) (after_term_14 heap) (.u64 13224869) := by rfl
theorem add_14 (heap : Heap) : Eval noCalls addTerm (after_term_14 heap) (after_sum_14 heap) (.u64 3133965575611513343) := by rfl
theorem increment_14 (heap : Heap) : Eval noCalls step (after_body_14 heap) (before_15 heap) (.u64 15) := by rfl
theorem guard_14 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_14 heap) (before_14 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_14 (heap : Heap) : Run noCalls iteration (before_14 heap) (.continuing (after_body_14 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_14 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_14 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_14 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_15 (heap : Heap) : State := {before_15 heap with env:=bind (before_15 heap).env "term" (.u64 881657)}
def after_sum_15 (heap : Heap) : State := {after_term_15 heap with env:=bind (after_term_15 heap).env "total" (.u64 3133965575612395000)}
def after_body_15 (heap : Heap) : State := closeScope (before_15 heap) (after_sum_15 heap)
def before_16 (heap : Heap) : State := {after_body_15 heap with env:=bind (after_body_15 heap).env "k" (.u64 16)}
theorem divide_15 (heap : Heap) : Eval noCalls divideTerm (before_15 heap) (after_term_15 heap) (.u64 881657) := by rfl
theorem add_15 (heap : Heap) : Eval noCalls addTerm (after_term_15 heap) (after_sum_15 heap) (.u64 3133965575612395000) := by rfl
theorem increment_15 (heap : Heap) : Eval noCalls step (after_body_15 heap) (before_16 heap) (.u64 16) := by rfl
theorem guard_15 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_15 heap) (before_15 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_15 (heap : Heap) : Run noCalls iteration (before_15 heap) (.continuing (after_body_15 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_15 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_15 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_15 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_16 (heap : Heap) : State := {before_16 heap with env:=bind (before_16 heap).env "term" (.u64 55103)}
def after_sum_16 (heap : Heap) : State := {after_term_16 heap with env:=bind (after_term_16 heap).env "total" (.u64 3133965575612450103)}
def after_body_16 (heap : Heap) : State := closeScope (before_16 heap) (after_sum_16 heap)
def before_17 (heap : Heap) : State := {after_body_16 heap with env:=bind (after_body_16 heap).env "k" (.u64 17)}
theorem divide_16 (heap : Heap) : Eval noCalls divideTerm (before_16 heap) (after_term_16 heap) (.u64 55103) := by rfl
theorem add_16 (heap : Heap) : Eval noCalls addTerm (after_term_16 heap) (after_sum_16 heap) (.u64 3133965575612450103) := by rfl
theorem increment_16 (heap : Heap) : Eval noCalls step (after_body_16 heap) (before_17 heap) (.u64 17) := by rfl
theorem guard_16 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_16 heap) (before_16 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_16 (heap : Heap) : Run noCalls iteration (before_16 heap) (.continuing (after_body_16 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_16 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_16 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_16 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_17 (heap : Heap) : State := {before_17 heap with env:=bind (before_17 heap).env "term" (.u64 3241)}
def after_sum_17 (heap : Heap) : State := {after_term_17 heap with env:=bind (after_term_17 heap).env "total" (.u64 3133965575612453344)}
def after_body_17 (heap : Heap) : State := closeScope (before_17 heap) (after_sum_17 heap)
def before_18 (heap : Heap) : State := {after_body_17 heap with env:=bind (after_body_17 heap).env "k" (.u64 18)}
theorem divide_17 (heap : Heap) : Eval noCalls divideTerm (before_17 heap) (after_term_17 heap) (.u64 3241) := by rfl
theorem add_17 (heap : Heap) : Eval noCalls addTerm (after_term_17 heap) (after_sum_17 heap) (.u64 3133965575612453344) := by rfl
theorem increment_17 (heap : Heap) : Eval noCalls step (after_body_17 heap) (before_18 heap) (.u64 18) := by rfl
theorem guard_17 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_17 heap) (before_17 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_17 (heap : Heap) : Run noCalls iteration (before_17 heap) (.continuing (after_body_17 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_17 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_17 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_17 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_18 (heap : Heap) : State := {before_18 heap with env:=bind (before_18 heap).env "term" (.u64 180)}
def after_sum_18 (heap : Heap) : State := {after_term_18 heap with env:=bind (after_term_18 heap).env "total" (.u64 3133965575612453524)}
def after_body_18 (heap : Heap) : State := closeScope (before_18 heap) (after_sum_18 heap)
def before_19 (heap : Heap) : State := {after_body_18 heap with env:=bind (after_body_18 heap).env "k" (.u64 19)}
theorem divide_18 (heap : Heap) : Eval noCalls divideTerm (before_18 heap) (after_term_18 heap) (.u64 180) := by rfl
theorem add_18 (heap : Heap) : Eval noCalls addTerm (after_term_18 heap) (after_sum_18 heap) (.u64 3133965575612453524) := by rfl
theorem increment_18 (heap : Heap) : Eval noCalls step (after_body_18 heap) (before_19 heap) (.u64 19) := by rfl
theorem guard_18 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_18 heap) (before_18 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_18 (heap : Heap) : Run noCalls iteration (before_18 heap) (.continuing (after_body_18 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_18 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_18 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_18 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_19 (heap : Heap) : State := {before_19 heap with env:=bind (before_19 heap).env "term" (.u64 9)}
def after_sum_19 (heap : Heap) : State := {after_term_19 heap with env:=bind (after_term_19 heap).env "total" (.u64 3133965575612453533)}
def after_body_19 (heap : Heap) : State := closeScope (before_19 heap) (after_sum_19 heap)
def before_20 (heap : Heap) : State := {after_body_19 heap with env:=bind (after_body_19 heap).env "k" (.u64 20)}
theorem divide_19 (heap : Heap) : Eval noCalls divideTerm (before_19 heap) (after_term_19 heap) (.u64 9) := by rfl
theorem add_19 (heap : Heap) : Eval noCalls addTerm (after_term_19 heap) (after_sum_19 heap) (.u64 3133965575612453533) := by rfl
theorem increment_19 (heap : Heap) : Eval noCalls step (after_body_19 heap) (before_20 heap) (.u64 20) := by rfl
theorem guard_19 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_19 heap) (before_19 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_19 (heap : Heap) : Run noCalls iteration (before_19 heap) (.continuing (after_body_19 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_19 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_19 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_19 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
def after_term_20 (heap : Heap) : State := {before_20 heap with env:=bind (before_20 heap).env "term" (.u64 0)}
def after_sum_20 (heap : Heap) : State := {after_term_20 heap with env:=bind (after_term_20 heap).env "total" (.u64 3133965575612453533)}
def after_body_20 (heap : Heap) : State := closeScope (before_20 heap) (after_sum_20 heap)
def before_21 (heap : Heap) : State := {after_body_20 heap with env:=bind (after_body_20 heap).env "k" (.u64 21)}
theorem divide_20 (heap : Heap) : Eval noCalls divideTerm (before_20 heap) (after_term_20 heap) (.u64 0) := by rfl
theorem add_20 (heap : Heap) : Eval noCalls addTerm (after_term_20 heap) (after_sum_20 heap) (.u64 3133965575612453533) := by rfl
theorem increment_20 (heap : Heap) : Eval noCalls step (after_body_20 heap) (before_21 heap) (.u64 21) := by rfl
theorem guard_20 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_20 heap) (before_20 heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 1) (by rfl)
theorem body_20 (heap : Heap) : Run noCalls iteration (before_20 heap) (.continuing (after_body_20 heap)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_20 heap))
  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_20 heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_20 heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))
  · rfl
theorem guard_21 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_21 heap) (before_21 heap) false := by exact LCMSourcePV.ASTLoops.GuardRun.present (value:=.i32 0) (by rfl)
theorem loop_21 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_21 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.done (guard_21 heap)
theorem loop_20 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_20 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_20 heap) (body_20 heap) (increment_20 heap) (loop_21 heap)
theorem loop_19 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_19 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_19 heap) (body_19 heap) (increment_19 heap) (loop_20 heap)
theorem loop_18 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_18 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_18 heap) (body_18 heap) (increment_18 heap) (loop_19 heap)
theorem loop_17 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_17 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_17 heap) (body_17 heap) (increment_17 heap) (loop_18 heap)
theorem loop_16 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_16 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_16 heap) (body_16 heap) (increment_16 heap) (loop_17 heap)
theorem loop_15 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_15 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_15 heap) (body_15 heap) (increment_15 heap) (loop_16 heap)
theorem loop_14 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_14 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_14 heap) (body_14 heap) (increment_14 heap) (loop_15 heap)
theorem loop_13 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_13 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_13 heap) (body_13 heap) (increment_13 heap) (loop_14 heap)
theorem loop_12 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_12 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_12 heap) (body_12 heap) (increment_12 heap) (loop_13 heap)
theorem loop_11 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_11 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_11 heap) (body_11 heap) (increment_11 heap) (loop_12 heap)
theorem loop_10 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_10 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_10 heap) (body_10 heap) (increment_10 heap) (loop_11 heap)
theorem loop_9 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_9 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_9 heap) (body_9 heap) (increment_9 heap) (loop_10 heap)
theorem loop_8 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_8 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_8 heap) (body_8 heap) (increment_8 heap) (loop_9 heap)
theorem loop_7 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_7 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_7 heap) (body_7 heap) (increment_7 heap) (loop_8 heap)
theorem loop_6 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_6 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_6 heap) (body_6 heap) (increment_6 heap) (loop_7 heap)
theorem loop_5 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_5 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_5 heap) (body_5 heap) (increment_5 heap) (loop_6 heap)
theorem loop_4 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_4 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_4 heap) (body_4 heap) (increment_4 heap) (loop_5 heap)
theorem loop_3 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_3 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_3 heap) (body_3 heap) (increment_3 heap) (loop_4 heap)
theorem loop_2 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_2 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_2 heap) (body_2 heap) (increment_2 heap) (loop_3 heap)
theorem loop_1 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_1 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_1 heap) (body_1 heap) (increment_1 heap) (loop_2 heap)
def after_for (heap : Heap) : State := closeScope (totalState heap) (before_21 heap)
def finalState (heap : Heap) : State := closeScope (initial heap) (after_for heap)
theorem low_function_executes (heap : Heap) : Run noCalls FiniteExpSource.lowFunction.body (initial heap) (.returned (finalState heap) (.u64 3133965575612453533)) := by
  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.returned (after_for heap) (.u64 3133965575612453533))
  · apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (t:=termState heap) (by rfl))
    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (t:=totalState heap) (by rfl))
    apply LCMSourcePV.ASTLoops.SeqRun.next (t:=after_for heap)
    · exact LCMSourcePV.ASTLoops.StmtRun.forLoop (LCMSourcePV.ASTLoops.StmtRun.declare (by rfl)) (loop_1 heap) (by rfl)
    · exact LCMSourcePV.ASTLoops.SeqRun.returned (LCMSourcePV.ASTLoops.StmtRun.returnValue (by rfl))
  · rfl
theorem low_completed_correct {heap : Heap} {t : State} {out : Value} (run : Run noCalls FiniteExpSource.lowFunction.body (initial heap) (.returned t out)) : out=.u64 AnalyticTransition.finiteELow := by
  have h:= (QuotientCDeterminism.returned_unique run (low_function_executes heap)).2
  simpa only [AnalyticTransition.finiteELow_value] using h
#print axioms low_function_executes
#print axioms low_completed_correct
end RamanujanPV.FiniteExpExecute
