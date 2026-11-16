/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.WordRemainder
import ScopedC.CallEvents
import ScopedC.ExpressionBinary

namespace SynergyC.CeilDivBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def addParameters (code : List Function) : Bool := code.all fun f =>
  f.name != "addU" || decide (f.parameters = [("U","a"),("U","b")])

theorem add_parameters (code : List Function) (checked : addParameters code = true)
    (f : Function) (mem : f ∈ code) (named : f.name = "addU") :
    f.parameters = [("U","a"),("U","b")] := by
  have h := (List.all_eq_true.mp checked) f mem
  simpa [named] using h

theorem generated_add_parameters : addParameters Generated.functions = true := by decide +kernel

def result (a b : Int) : Int := a/b + bit (a%b != 0)
def guard : Expr := .binary "==" (.var "b") (.nat 0)
def returned : Expr := .call (.var "addU") [
  .binary "/" (.var "a") (.var "b"),
  .binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0)]

theorem source_ceilDiv (code : List Function) (installed : Generated.f_ceilDiv ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (checked : addParameters code = true)
    {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hb0 : 0 < b) (fit : Range (result a b)) :
    SourceCall Header.layout code 2 "ceilDiv" [value a,value b] s (value (result a b)) s := by
  let before := frame s a b
  let q := a/b
  let flag := a%b != 0
  have hq : Range q := quotient_range ha hb0
  have hr : Range (a%b) := remainder_range hb hb0
  have hc : MaxContext before := WordService.allocateContext
    (WordService.allocateContext (WordService.emptyEnvContext ctx) "U" "a" (some (value a)))
    "U" "b" (some (value b))
  have addProof : SourceCall Header.layout code 1 "addU"
      [value q,boolean Header.layout flag] before (value (result a b)) before := by
    have h := AddBody.source_addU code addInstalled hc hq (bit_range flag) fit
    apply ArgumentConversion.replace_arguments h (by rfl)
    intro f mem named
    rw [add_parameters code checked f mem named]
    have raw := TypedFrames.bind_two Header.layout before "U" "a" "U" "b"
      (value q) (boolean Header.layout flag) (value q) (value (bit flag))
      (cast_word _ hq) (cast_boolean _ flag)
    rw [raw,WordFrames.bind before hq (bit_range flag)]
    rfl
  let event : CallEvents.Event Header.layout code 1 :=
    ⟨"addU",[value q,boolean Header.layout flag],before,value (result a b),before,addProof⟩
  let service := CallEvents.one event
  have bdiv : binaryValue Header.layout before "/" (value a) (value b) = some (value q) := by
    simp only [binaryValue,value,word_div ha hb hb0,Option.bind_some]
    rfl
  have bmod : binaryValue Header.layout before "%" (value a) (value b) = some (value (a%b)) := by
    simp only [binaryValue,value,word_mod ha hb hb0,Option.bind_some]
    rfl
  have bne : binaryValue Header.layout before "!=" (value (a%b)) (.integer MulBody.intZero) =
      some (boolean Header.layout flag) := by
    simp only [binaryValue,value,MulBody.word_ne_zero hr,Option.bind_some]
    change (do let v ← some (Scalar.boolean flag)
               if ["<","<=",">",">=","==","!="].contains "!=" then
                 pure (boolean Header.layout (Scalar.truth v))
               else pure (Value.integer v)) = _
    cases flag <;> rfl
  have beq : binaryValue Header.layout before "==" (value b) (.integer MulBody.intZero) =
      some (boolean Header.layout false) := by
    simp only [binaryValue,value,word_eq_zero hb,Option.bind_some]
    simp [Bind.bind,Option.bind,Scalar.boolean,Scalar.truth,ne_of_gt hb0]
  have guard_eval : Eval Header.layout service guard before before (boolean Header.layout false) := by
    refine ⟨5,?_⟩
    exact ExpressionTemplates.binary Header.layout service (by decide) (by decide) (by decide) (by decide)
      (eval_b service 3 s a b) (MulBody.literal_zero service 3 before) beq
  have div_eval : evalExpr Header.layout service 5 before (.binary "/" (.var "a") (.var "b")) =
      some (value q,before) :=
    ExpressionTemplates.binary Header.layout service (by decide) (by decide) (by decide) (by decide)
      (eval_a service 3 s a b) (eval_b service 3 s a b) bdiv
  have mod_eval : evalExpr Header.layout service 4 before (.binary "%" (.var "a") (.var "b")) =
      some (value (a%b),before) :=
    ExpressionTemplates.binary Header.layout service (by decide) (by decide) (by decide) (by decide)
      (eval_a service 2 s a b) (eval_b service 2 s a b) bmod
  have ne_eval : evalExpr Header.layout service 5 before
      (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0)) =
      some (boolean Header.layout flag,before) :=
    ExpressionTemplates.binary Header.layout service (by decide) (by decide) (by decide) (by decide)
      mod_eval (MulBody.literal_zero service 3 before) bne
  have return_eval : Eval Header.layout service returned before before (value (result a b)) := by
    exact ⟨6,ExpressionTemplates.call_two Header.layout service div_eval ne_eval (CallEvents.one_self event)⟩
  have statement : Run Header.layout service Generated.f_ceilDiv.body before
      (.returned before (value (result a b))) := by
    change Run Header.layout service
      (.sequence [.branch guard (.eval (.call (.var "fail") [])) .skip,.returnStmt returned])
      before (.returned before (value (result a b)))
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · apply Loops.StmtRun.branch guard_eval
        exact Loops.StmtRun.skip _
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue return_eval)
    · exact ⟨rfl,by simp [popScope]⟩
  have finished : Finish Header.layout Generated.f_ceilDiv s
      (.returned before (value (result a b))) (value (result a b)) s := by
    change castValue Header.layout before 100 "static U" (value (result a b)) = some (value (result a b)) ∧
      s = popScope s before
    exact ⟨cast_word before fit,(pop_frame s a b).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=1) installed
    (fun _ _ _ _ _ h => CallEvents.one_closed event h) (WordFrames.bind s ha hb) statement finished

end SynergyC.CeilDivBody
