/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.WordFrames
import SynergyC.Generated
namespace SynergyC.AddBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def guard : Expr := .binary "<" (.binary "-" (.var "MAXU") (.var "a")) (.var "b")
def returned : Expr := .binary "+" (.var "a") (.var "b")

theorem source_addU (code : List Function) (installed : Generated.f_addU ∈ code)
    {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hab : Range (a+b)) :
    SourceCall Header.layout code 1 "addU" [value a,value b] s (value (a+b)) s := by
  have hma : a ≤ maxWord := by rcases ha with ⟨_,_⟩;unfold maxWord;omega
  have hdiff : Range (maxWord-a) := by
    rcases ha with ⟨_,_⟩
    rcases max_range with ⟨_,_⟩
    unfold Range at *
    constructor <;> omega
  have hsafe : b ≤ maxWord-a := by
    rcases hab with ⟨_,h⟩
    unfold maxWord
    omega
  have bsub : binaryValue Header.layout (frame s a b) "-" (value maxWord) (value a) =
      some (value (maxWord-a)) := by
    simp only [binaryValue,value,word_sub max_range ha hma,Option.bind_some]
    rfl
  have badd : binaryValue Header.layout (frame s a b) "+" (value a) (value b) =
      some (value (a+b)) := by
    simp only [binaryValue,value,word_add ha hb hab,Option.bind_some]
    rfl
  have blt : binaryValue Header.layout (frame s a b) "<" (value (maxWord-a)) (value b) =
      some (boolean Header.layout false) := by
    simp only [binaryValue,value,word_lt_false hdiff hb hsafe,Option.bind_some]
    rfl
  have sub_eval : evalExpr Header.layout RuntimeCore.call 5 (frame s a b)
      (.binary "-" (.var "MAXU") (.var "a")) = some (value (maxWord-a),frame s a b) := by
    rw [evalExpr] <;> try { decide +kernel }
    simp [Bind.bind,Option.bind,eval_max _ _ ctx,eval_a,bsub]
  have guard_eval : Eval Header.layout RuntimeCore.call guard (frame s a b) (frame s a b)
      (boolean Header.layout false) := by
    refine ⟨6,?_⟩
    rw [guard,evalExpr,sub_eval] <;> try { decide +kernel }
    simp [Bind.bind,Option.bind,eval_b,blt]
  have return_eval : Eval Header.layout RuntimeCore.call returned (frame s a b) (frame s a b)
      (value (a+b)) := by
    refine ⟨4,?_⟩
    rw [returned,evalExpr] <;> try { decide +kernel }
    simp [Bind.bind,Option.bind,eval_a,eval_b,badd]
  have statement : Run Header.layout RuntimeCore.call Generated.f_addU.body (frame s a b)
      (.returned (frame s a b) (value (a+b))) := by
    change Run Header.layout RuntimeCore.call
      (.sequence [.branch guard (.eval (.call (.var "fail") [])) .skip,.returnStmt returned])
      (frame s a b) (.returned (frame s a b) (value (a+b)))
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · apply Loops.StmtRun.branch guard_eval
        exact Loops.StmtRun.skip _
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue return_eval)
    · exact ⟨rfl,by simp [popScope]⟩
  have finished : Finish Header.layout Generated.f_addU s
      (.returned (frame s a b) (value (a+b))) (value (a+b)) s := by
    change castValue Header.layout (frame s a b) 100 "static U" (value (a+b)) = some (value (a+b)) ∧
      s=popScope s (frame s a b)
    exact ⟨cast_word (frame s a b) hab,(pop_frame s a b).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=0) installed
    (fun _ _ _ _ _ h=>h) (WordFrames.bind s ha hb) statement finished

#print axioms source_addU
end SynergyC.AddBody
