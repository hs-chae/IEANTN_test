/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.WordFrames
import SynergyC.WordMulDiv
import SynergyC.Generated

namespace SynergyC.MulBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def intZero : Scalar.Value := ⟨⟨true,32⟩,0⟩
def guard : Expr := .binary "&&" (.binary "!=" (.var "a") (.nat 0))
  (.binary "<" (.binary "/" (.var "MAXU") (.var "a")) (.var "b"))
def returned : Expr := .binary "*" (.var "a") (.var "b")

theorem word_ne_zero {a : Int} (ha : Range a) :
    Scalar.binary "!=" (word a) intZero = some (Scalar.boolean (a != 0)) := by
  have ha' := range_scalar ha
  have hz : Scalar.InRange intZero.type intZero.number := by decide +kernel
  have h0 : Range 0 := by norm_num [Range]
  have hc : Scalar.cast type intZero = some (word 0) := by
    exact Scalar.make_exact (range_scalar h0)
  simp only [word,Scalar.binary,ha',hz,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type intZero
             pure (Scalar.boolean (x.number != y.number))) = _
  rw [cast_scalar ha,hc]
  rfl

theorem literal_zero (service : Call) (fuel : Nat) (s : State) :
    evalExpr Header.layout service (fuel+1) s (.nat 0) = some (.integer intZero,s) := by
  rfl

theorem neq_eval (service : Call) (s : State) {a b : Int} (ha : Range a) :
    evalExpr Header.layout service 6 (frame s a b) (.binary "!=" (.var "a") (.nat 0)) =
      some (boolean Header.layout (a != 0),frame s a b) := by
  have bv : binaryValue Header.layout (frame s a b) "!=" (value a) (.integer intZero) =
      some (boolean Header.layout (a != 0)) := by
    simp only [binaryValue,value,word_ne_zero ha,Option.bind_some]
    cases h : (a != 0) <;> simp [h,Bind.bind,Option.bind,Scalar.boolean,Scalar.truth]
  rw [evalExpr] <;> try { decide +kernel }
  simp [Bind.bind,Option.bind,eval_a,literal_zero,bv]

theorem source_mulU (code : List Function) (installed : Generated.f_mulU ∈ code)
    {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hab : Range (a*b)) :
    SourceCall Header.layout code 1 "mulU" [value a,value b] s (value (a*b)) s := by
  have bmul : binaryValue Header.layout (frame s a b) "*" (value a) (value b) =
      some (value (a*b)) := by
    simp only [binaryValue,value,word_mul ha hb hab,Option.bind_some]
    rfl
  have guard_eval : Eval Header.layout RuntimeCore.call guard (frame s a b) (frame s a b)
      (boolean Header.layout false) := by
    refine ⟨7,?_⟩
    rw [guard,evalExpr,neq_eval _ _ ha]
    by_cases ha0 : a = 0
    · simp [ha0,Bind.bind,Option.bind,truth,Machine.boolean,Scalar.boolean,Scalar.truth]
    · have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
      have hq := quotient_range max_range hap
      have hsafe := mul_guard_safe hap hab
      have bdiv : binaryValue Header.layout (frame s a b) "/" (value maxWord) (value a) =
          some (value (maxWord/a)) := by
        simp only [binaryValue,value,word_div max_range ha hap,Option.bind_some]
        rfl
      have blt : binaryValue Header.layout (frame s a b) "<" (value (maxWord/a)) (value b) =
          some (boolean Header.layout false) := by
        simp only [binaryValue,value,word_lt_false hq hb hsafe,Option.bind_some]
        rfl
      have div_eval : evalExpr Header.layout RuntimeCore.call 5 (frame s a b)
          (.binary "/" (.var "MAXU") (.var "a")) = some (value (maxWord/a),frame s a b) := by
        rw [evalExpr] <;> try { decide +kernel }
        simp [Bind.bind,Option.bind,eval_max _ _ ctx,eval_a,bdiv]
      have lt_eval : evalExpr Header.layout RuntimeCore.call 6 (frame s a b)
          (.binary "<" (.binary "/" (.var "MAXU") (.var "a")) (.var "b")) =
          some (boolean Header.layout false,frame s a b) := by
        rw [evalExpr,div_eval] <;> try { decide +kernel }
        simp [Bind.bind,Option.bind,eval_b,blt]
      simp [ha0,Bind.bind,Option.bind,truth,Machine.boolean,Scalar.boolean,Scalar.truth,lt_eval]
  have return_eval : Eval Header.layout RuntimeCore.call returned (frame s a b) (frame s a b)
      (value (a*b)) := by
    refine ⟨4,?_⟩
    rw [returned,evalExpr] <;> try { decide +kernel }
    simp [Bind.bind,Option.bind,eval_a,eval_b,bmul]
  have statement : Run Header.layout RuntimeCore.call Generated.f_mulU.body (frame s a b)
      (.returned (frame s a b) (value (a*b))) := by
    change Run Header.layout RuntimeCore.call
      (.sequence [.branch guard (.eval (.call (.var "fail") [])) .skip,.returnStmt returned])
      (frame s a b) (.returned (frame s a b) (value (a*b)))
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · apply Loops.StmtRun.branch guard_eval
        exact Loops.StmtRun.skip _
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue return_eval)
    · exact ⟨rfl,by simp [popScope]⟩
  have finished : Finish Header.layout Generated.f_mulU s
      (.returned (frame s a b) (value (a*b))) (value (a*b)) s := by
    change castValue Header.layout (frame s a b) 100 "static U" (value (a*b)) = some (value (a*b)) ∧
      s = popScope s (frame s a b)
    exact ⟨cast_word (frame s a b) hab,(pop_frame s a b).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=0) installed
    (fun _ _ _ _ _ h=>h) (WordFrames.bind s ha hb) statement finished

end SynergyC.MulBody
