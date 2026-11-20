#!/usr/bin/env python3
"""Untrusted proposal of concrete20-step actual typed C execution witnesses."""
from pathlib import Path
S=Path(__file__).resolve().parents[1]
HEADER="/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n"
def main():
 text=HEADER+'import RamanujanPV.FiniteExpSource\nimport RamanujanPV.QuotientCDeterminism\nimport RamanujanPV.AnalyticTransition\nnamespace RamanujanPV.FiniteExpExecute\nopen LCMSourcePV.Witness.C QuotientCMachine\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 10000\nset_option Elab.async false\ndef noCalls : Service := fun _ _ => none\ndef initial (heap : Heap) : State := ⟨emptyEnv,heap⟩\ndef termState (heap : Heap) : State := {initial heap with env:=bind (initial heap).env "term" (.u64 1152921504606846976)}\ndef totalState (heap : Heap) : State := {termState heap with env:=bind (termState heap).env "total" (.u64 1152921504606846976)}\ndef before_1 (heap : Heap) : State := {totalState heap with env:=bind (totalState heap).env "k" (.u64 1)}\ndef condition : Expr := .binary "<=" (.var "k") (.nat 20)\ndef step : Expr := .unary "++" (.var "k")\ndef divideTerm : Expr := .binary "=" (.var "term") (.binary "/" (.var "term") (.var "k"))\ndef addTerm : Expr := .binary "=" (.var "total") (.binary "+" (.var "total") (.var "term"))\ndef iteration : Stmt := .sequence [.eval divideTerm,.eval addTerm]\n'
 term=total=1<<60
 for i in range(1,21):
  term//=i;total+=term
  text+=f'def after_term_{i} (heap : Heap) : State := {{before_{i} heap with env:=bind (before_{i} heap).env "term" (.u64 {term})}}\n'
  text+=f'def after_sum_{i} (heap : Heap) : State := {{after_term_{i} heap with env:=bind (after_term_{i} heap).env "total" (.u64 {total})}}\n'
  text+=f'def after_body_{i} (heap : Heap) : State := closeScope (before_{i} heap) (after_sum_{i} heap)\n'
  text+=f'def before_{i+1} (heap : Heap) : State := {{after_body_{i} heap with env:=bind (after_body_{i} heap).env "k" (.u64 {i+1})}}\n'
  text+=f'theorem divide_{i} (heap : Heap) : Eval noCalls divideTerm (before_{i} heap) (after_term_{i} heap) (.u64 {term}) := by rfl\n'
  text+=f'theorem add_{i} (heap : Heap) : Eval noCalls addTerm (after_term_{i} heap) (after_sum_{i} heap) (.u64 {total}) := by rfl\n'
  text+=f'theorem increment_{i} (heap : Heap) : Eval noCalls step (after_body_{i} heap) (before_{i+1} heap) (.u64 {i+1}) := by rfl\n'
  text+=f'theorem guard_{i} (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_{i} heap) (before_{i} heap) true := by exact LCMSourcePV.ASTLoops.GuardRun.present (Eval:=Eval noCalls) (truth:=truth) (value:=Value.i32 1) (by rfl)\n'
  text+=f'theorem body_{i} (heap : Heap) : Run noCalls iteration (before_{i} heap) (.continuing (after_body_{i} heap)) := by\n  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.continuing (after_sum_{i} heap))\n  · exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (divide_{i} heap)) (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.evaluate (add_{i} heap)) (LCMSourcePV.ASTLoops.SeqRun.nil _))\n  · rfl\n'
 text+='theorem guard_21 (heap : Heap) : LCMSourcePV.ASTLoops.GuardRun (Eval noCalls) truth (some condition) (before_21 heap) (before_21 heap) false := by exact LCMSourcePV.ASTLoops.GuardRun.present (Eval:=Eval noCalls) (truth:=truth) (value:=Value.i32 0) (by rfl)\n'
 text+='theorem loop_21 (heap : Heap) : ForRun noCalls (some condition) step iteration (before_21 heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.done (guard_21 heap)\n'
 for i in range(20,0,-1):text+=f'theorem loop_{i} (heap : Heap) : ForRun noCalls (some condition) step iteration (before_{i} heap) (.continuing (before_21 heap)) := LCMSourcePV.ASTLoops.ForRun.next (guard_{i} heap) (body_{i} heap) (increment_{i} heap) (loop_{i+1} heap)\n'
 text+='def after_for (heap : Heap) : State := closeScope (totalState heap) (before_21 heap)\ndef finalState (heap : Heap) : State := closeScope (initial heap) (after_for heap)\n'
 text+='theorem low_function_executes (heap : Heap) : Run noCalls FiniteExpSource.lowFunction.body (initial heap) (.returned (finalState heap) (.u64 3133965575612453533)) := by\n  apply LCMSourcePV.ASTLoops.StmtRun.sequence (inner:=.returned (after_for heap) (.u64 3133965575612453533))\n  · apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (t:=termState heap) (by rfl))\n    apply LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (t:=totalState heap) (by rfl))\n    apply LCMSourcePV.ASTLoops.SeqRun.next (t:=after_for heap)\n    · exact LCMSourcePV.ASTLoops.StmtRun.forLoop (LCMSourcePV.ASTLoops.StmtRun.declare (by rfl)) (loop_1 heap) (by rfl)\n    · exact LCMSourcePV.ASTLoops.SeqRun.returned (LCMSourcePV.ASTLoops.StmtRun.returnValue (by rfl))\n  · rfl\n'
 text+='theorem low_completed_correct {heap : Heap} {t : State} {out : Value} (run : Run noCalls FiniteExpSource.lowFunction.body (initial heap) (.returned t out)) : out=.u64 AnalyticTransition.finiteELow := by\n  have h:= (QuotientCDeterminism.returned_unique run (low_function_executes heap)).2\n  simpa only [AnalyticTransition.finiteELow_value] using h\n#print axioms low_function_executes\n#print axioms low_completed_correct\nend RamanujanPV.FiniteExpExecute\n'
 p=S/'RamanujanPV/FiniteExpExecute.lean'
 if p.exists()and p.read_text()!=text:raise ValueError('preserve an existing proof attempt before regenerating')
 p.write_text(text);print(p)
if __name__=='__main__':main()
