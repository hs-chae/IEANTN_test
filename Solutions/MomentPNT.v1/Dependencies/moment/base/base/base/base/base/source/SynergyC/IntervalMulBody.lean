/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalMulExpr

namespace SynergyC.IntervalMulBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def declaration : Decl := {type:="I",name:="r",value:=some IntervalMulExpr.initializer,arrayExtent:=none}
def result (al ah bl bh : Int) : Value := interval ((al*bl)/scale) (CeilDivBody.result (ah*bh) scale)
def resultFrame (s : State) (al ah bl bh : Int) : State :=
  allocate (IntervalValues.frame s al ah bl bh) "I" "r" (some (result al ah bl bh))

theorem declared {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al*bl)) (hh : Range (ah*bh)) :
    declarations Header.layout ArithmeticService.call [declaration] (IntervalValues.frame s al ah bl bh) =
      some (resultFrame s al ah bl bh) := by
  simp only [declarations,declaration,List.foldlM,
    IntervalMulExpr.eval_initializer maxCtx scaleCtx hal hah hbl hbh hl hh,Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 (quotient_range hl IntervalMulExpr.scale_positive)
    (CeilDivBody.result_range hh IntervalMulExpr.scale_positive)]
  rfl

theorem source_mul (code : List Function) (installed : Generated.f_mul ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code) (checked : ArithmeticService.parameters code = true)
    {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al*bl)) (hh : Range (ah*bh)) :
    SourceCall Header.layout code 3 "mul" [interval al ah,interval bl bh] s (result al ah bl bh) s := by
  have localEval : Eval Header.layout ArithmeticService.call (.var "r")
      (resultFrame s al ah bl bh) (resultFrame s al ah bl bh) (result al ah bl bh) := by
    refine ⟨2,?_⟩
    exact TypedFrames.allocate_eval Header.layout ArithmeticService.call 1 (IntervalValues.frame s al ah bl bh)
      "I" "r" (result al ah bl bh) (by rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have body : Run Header.layout ArithmeticService.call Generated.f_mul.body (IntervalValues.frame s al ah bl bh)
      (.returned (IntervalValues.frame s al ah bl bh) (result al ah bl bh)) := by
    change Run Header.layout ArithmeticService.call (.sequence [.declare [declaration],.returnStmt (.var "r")])
      (IntervalValues.frame s al ah bl bh) (.returned (IntervalValues.frame s al ah bl bh) (result al ah bl bh))
    apply Loops.StmtRun.sequence
    · exact Loops.SeqRun.next (Loops.StmtRun.declare (declared maxCtx scaleCtx hal hah hbl hbh hl hh))
        (Loops.SeqRun.returned (Loops.StmtRun.returnValue localEval))
    · exact ⟨rfl,(TypedFrames.pop_allocate (IntervalValues.frame s al ah bl bh) "I" "r"
        (some (result al ah bl bh))).symm⟩
  have finish : Finish Header.layout Generated.f_mul s
      (.returned (IntervalValues.frame s al ah bl bh) (result al ah bl bh)) (result al ah bl bh) s := by
    change castValue Header.layout (IntervalValues.frame s al ah bl bh) 100 "static I" (result al ah bl bh) =
      some (result al ah bl bh) ∧ s = popScope s (IntervalValues.frame s al ah bl bh)
    exact ⟨IntervalValues.cast_record _ 98 (quotient_range hl IntervalMulExpr.scale_positive)
      (CeilDivBody.result_range hh IntervalMulExpr.scale_positive),(IntervalValues.pop_frame s al ah bl bh).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=2) installed
    (fun _ _ _ _ _ h=>ArithmeticService.closed code addInstalled mulInstalled ceilInstalled checked h)
    (IntervalValues.bind s hal hah hbl hbh) body finish

end SynergyC.IntervalMulBody
