/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalDivExpr

namespace SynergyC.IntervalDivBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def guard : Expr := .binary "==" (.field "." (.var "b") "lo") (.nat 0)
def declaration : Decl := {type:="I",name:="r",value:=some IntervalDivExpr.initializer,arrayExtent:=none}
def result (al ah bl bh : Int) : Value := interval ((al*scale)/bh) (CeilDivBody.result (ah*scale) bl)
def resultFrame (s : State) (al ah bl bh : Int) : State :=
  allocate (IntervalValues.frame s al ah bl bh) "I" "r" (some (result al ah bl bh))

theorem declared {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (blPositive : 0 < bl) (bhPositive : 0 < bh)
    (hl : Range (al*scale)) (hh : Range (ah*scale)) :
    declarations Header.layout ArithmeticService.call [declaration] (IntervalValues.frame s al ah bl bh) =
      some (resultFrame s al ah bl bh) := by
  simp only [declarations,declaration,List.foldlM,
    IntervalDivExpr.eval_initializer maxCtx scaleCtx hal hah hbl hbh blPositive bhPositive hl hh,
    Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 (quotient_range hl bhPositive)
    (CeilDivBody.result_range hh blPositive)]
  rfl

theorem source_divI (code : List Function) (installed : Generated.f_divI ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code) (checked : ArithmeticService.parameters code = true)
    {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (blPositive : 0 < bl) (bhPositive : 0 < bh)
    (hl : Range (al*scale)) (hh : Range (ah*scale)) :
    SourceCall Header.layout code 3 "divI" [interval al ah,interval bl bh] s (result al ah bl bh) s := by
  let before := IntervalValues.frame s al ah bl bh
  have beq : binaryValue Header.layout before "==" (value bl) (.integer MulBody.intZero) =
      some (boolean Header.layout false) := by
    simp only [binaryValue,value,word_eq_zero hbl,Option.bind_some]
    simp [Bind.bind,Option.bind,Scalar.boolean,Scalar.truth,ne_of_gt blPositive]
  have guard_eval : Eval Header.layout ArithmeticService.call guard before before (boolean Header.layout false) := by
    refine ⟨5,?_⟩
    exact ExpressionTemplates.binary Header.layout ArithmeticService.call
      (by decide) (by decide) (by decide) (by decide)
      (IntervalValues.eval_b_lo _ 2 s al ah bl bh)
      (MulBody.literal_zero _ 3 before) beq
  have localEval : Eval Header.layout ArithmeticService.call (.var "r")
      (resultFrame s al ah bl bh) (resultFrame s al ah bl bh) (result al ah bl bh) := by
    refine ⟨2,?_⟩
    exact TypedFrames.allocate_eval Header.layout ArithmeticService.call 1 before
      "I" "r" (result al ah bl bh) (by rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have body : Run Header.layout ArithmeticService.call Generated.f_divI.body before
      (.returned before (result al ah bl bh)) := by
    change Run Header.layout ArithmeticService.call
      (.sequence [.branch guard (.eval (.call (.var "fail") [])) .skip,
        .declare [declaration],.returnStmt (.var "r")])
      before (.returned before (result al ah bl bh))
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · apply Loops.StmtRun.branch guard_eval
        exact Loops.StmtRun.skip _
      · exact Loops.SeqRun.next
          (Loops.StmtRun.declare (declared maxCtx scaleCtx hal hah hbl hbh blPositive bhPositive hl hh))
          (Loops.SeqRun.returned (Loops.StmtRun.returnValue localEval))
    · exact ⟨rfl,(TypedFrames.pop_allocate before "I" "r" (some (result al ah bl bh))).symm⟩
  have finish : Finish Header.layout Generated.f_divI s
      (.returned before (result al ah bl bh)) (result al ah bl bh) s := by
    change castValue Header.layout before 100 "static I" (result al ah bl bh) =
      some (result al ah bl bh) ∧ s = popScope s before
    exact ⟨IntervalValues.cast_record _ 98 (quotient_range hl bhPositive)
      (CeilDivBody.result_range hh blPositive),(IntervalValues.pop_frame s al ah bl bh).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=2) installed
    (fun _ _ _ _ _ h=>ArithmeticService.closed code addInstalled mulInstalled ceilInstalled checked h)
    (IntervalValues.bind s hal hah hbl hbh) body finish

end SynergyC.IntervalDivBody
