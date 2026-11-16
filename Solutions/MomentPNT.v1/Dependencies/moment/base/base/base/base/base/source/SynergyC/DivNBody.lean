/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.DivNExpr

namespace SynergyC.DivNBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def guard : Expr := .binary "==" (.var "n") (.nat 0)
def declaration : Decl := {type:="I",name:="r",value:=some DivNExpr.initializer,arrayExtent:=none}
def result (al ah n : Int) : Value := interval (al/n) (CeilDivBody.result ah n)
def resultFrame (s : State) (al ah n : Int) : State :=
  allocate (DivNFrames.frame s al ah n) "I" "r" (some (result al ah n))

theorem declared {s : State} (maxCtx : MaxContext s)
    {al ah n : Int} (hal : Range al) (hah : Range ah) (hn : SmallWord.Range n) (hn0 : 0 < n) :
    declarations Header.layout ArithmeticService.call [declaration] (DivNFrames.frame s al ah n) =
      some (resultFrame s al ah n) := by
  simp only [declarations,declaration,List.foldlM,
    DivNExpr.eval_initializer maxCtx hal hah hn hn0,
    Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 (quotient_range hal hn0)
    (CeilDivBody.result_range hah hn0)]
  rfl

theorem source_divN (code : List Function) (installed : Generated.f_divN ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code) (checked : ArithmeticService.parameters code = true)
    {s : State} (maxCtx : MaxContext s)
    {al ah n : Int} (hal : Range al) (hah : Range ah) (hn : SmallWord.Range n) (hn0 : 0 < n) :
    SourceCall Header.layout code 3 "divN" [interval al ah,SmallWord.value n] s (result al ah n) s := by
  let before := DivNFrames.frame s al ah n
  have beq : binaryValue Header.layout before "==" (SmallWord.value n) (.integer MulBody.intZero) =
      some (boolean Header.layout false) := by
    simp only [binaryValue,SmallWord.value,SmallWord.eq_zero hn,Option.bind_some]
    simp [Bind.bind,Option.bind,Scalar.boolean,Scalar.truth,ne_of_gt hn0]
  have guard_eval : Eval Header.layout ArithmeticService.call guard before before (boolean Header.layout false) := by
    refine ⟨5,?_⟩
    exact ExpressionTemplates.binary Header.layout ArithmeticService.call
      (by decide) (by decide) (by decide) (by decide)
      (DivNFrames.eval_n _ 3 s al ah n)
      (MulBody.literal_zero _ 3 before) beq
  have localEval : Eval Header.layout ArithmeticService.call (.var "r")
      (resultFrame s al ah n) (resultFrame s al ah n) (result al ah n) := by
    refine ⟨2,?_⟩
    exact TypedFrames.allocate_eval Header.layout ArithmeticService.call 1 before
      "I" "r" (result al ah n) (by rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have body : Run Header.layout ArithmeticService.call Generated.f_divN.body before
      (.returned before (result al ah n)) := by
    change Run Header.layout ArithmeticService.call
      (.sequence [.branch guard (.eval (.call (.var "fail") [])) .skip,
        .declare [declaration],.returnStmt (.var "r")])
      before (.returned before (result al ah n))
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · apply Loops.StmtRun.branch guard_eval
        exact Loops.StmtRun.skip _
      · exact Loops.SeqRun.next
          (Loops.StmtRun.declare (declared maxCtx hal hah hn hn0))
          (Loops.SeqRun.returned (Loops.StmtRun.returnValue localEval))
    · exact ⟨rfl,(TypedFrames.pop_allocate before "I" "r" (some (result al ah n))).symm⟩
  have finish : Finish Header.layout Generated.f_divN s
      (.returned before (result al ah n)) (result al ah n) s := by
    change castValue Header.layout before 100 "static I" (result al ah n) =
      some (result al ah n) ∧ s = popScope s before
    exact ⟨IntervalValues.cast_record _ 98 (quotient_range hal hn0)
      (CeilDivBody.result_range hah hn0),(DivNFrames.pop_frame s al ah n).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=2) installed
    (fun _ _ _ _ _ h=>ArithmeticService.closed code addInstalled mulInstalled ceilInstalled checked h)
    (DivNFrames.bind s hal hah hn) body finish

end SynergyC.DivNBody
