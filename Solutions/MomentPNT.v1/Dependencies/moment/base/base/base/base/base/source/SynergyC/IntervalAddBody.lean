/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.WordService

namespace SynergyC.IntervalAddBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def initializer : Expr := .record [
  .call (.var "addU") [.field "." (.var "a") "lo",.field "." (.var "b") "lo"],
  .call (.var "addU") [.field "." (.var "a") "hi",.field "." (.var "b") "hi"]]
def declaration : Decl := {type:="I",name:="r",value:=some initializer,arrayExtent:=none}
def resultFrame (s : State) (al ah bl bh : Int) : State :=
  allocate (IntervalValues.frame s al ah bl bh) "I" "r" (some (interval (al+bl) (ah+bh)))

theorem eval_initializer {s : State} (ctx : MaxContext s) {al ah bl bh : Int}
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al+bl)) (hh : Range (ah+bh)) :
    evalExpr Header.layout WordService.add 1000 (IntervalValues.frame s al ah bl bh) initializer =
      some (.aggregate [value (al+bl),value (ah+bh)],IntervalValues.frame s al ah bl bh) := by
  have hc := WordService.intervalFrameContext ctx al ah bl bh
  have low := ExpressionTemplates.call_two Header.layout WordService.add
    (IntervalValues.eval_a_lo _ 996 s al ah bl bh)
    (IntervalValues.eval_b_lo _ 996 s al ah bl bh) (WordService.add_complete hc hal hbl hl)
  have high := ExpressionTemplates.call_two Header.layout WordService.add
    (IntervalValues.eval_a_hi _ 996 s al ah bl bh)
    (IntervalValues.eval_b_hi _ 996 s al ah bl bh) (WordService.add_complete hc hah hbh hh)
  exact ExpressionTemplates.record_two Header.layout WordService.add low high

theorem declared {s : State} (ctx : MaxContext s) {al ah bl bh : Int}
    (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al+bl)) (hh : Range (ah+bh)) :
    declarations Header.layout WordService.add [declaration] (IntervalValues.frame s al ah bl bh) =
      some (resultFrame s al ah bl bh) := by
  simp only [declarations,declaration,List.foldlM,eval_initializer ctx hal hah hbl hbh hl hh,
    Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 hl hh]
  rfl

theorem eval_local (s : State) (al ah bl bh : Int) :
    Eval Header.layout WordService.add (.var "r") (resultFrame s al ah bl bh)
      (resultFrame s al ah bl bh) (interval (al+bl) (ah+bh)) := by
  refine ⟨2,?_⟩
  exact TypedFrames.allocate_eval Header.layout WordService.add 1
    (IntervalValues.frame s al ah bl bh) "I" "r" (interval (al+bl) (ah+bh))
    (by rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Source execution of the actual interval-add body, composed from both
actual checked-add bodies. No complete application output is a premise. -/
theorem source_add (code : List Function) (installed : Generated.f_add ∈ code)
    (addInstalled : Generated.f_addU ∈ code) {s : State} (ctx : MaxContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al+bl)) (hh : Range (ah+bh)) :
    SourceCall Header.layout code 2 "add" [interval al ah,interval bl bh] s
      (interval (al+bl) (ah+bh)) s := by
  have statement : Run Header.layout WordService.add Generated.f_add.body (IntervalValues.frame s al ah bl bh)
      (.returned (IntervalValues.frame s al ah bl bh) (interval (al+bl) (ah+bh))) := by
    change Run Header.layout WordService.add
      (.sequence [.declare [declaration],.returnStmt (.var "r")]) _ _
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · exact Loops.StmtRun.declare (declared ctx hal hah hbl hbh hl hh)
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue (eval_local s al ah bl bh))
    · exact ⟨rfl,(TypedFrames.pop_allocate (IntervalValues.frame s al ah bl bh) "I" "r"
        (some (interval (al+bl) (ah+bh)))).symm⟩
  have finished : Finish Header.layout Generated.f_add s
      (.returned (IntervalValues.frame s al ah bl bh) (interval (al+bl) (ah+bh)))
      (interval (al+bl) (ah+bh)) s := by
    change castValue Header.layout _ 100 "static I" (interval (al+bl) (ah+bh)) =
      some (interval (al+bl) (ah+bh)) ∧ s = popScope s (IntervalValues.frame s al ah bl bh)
    exact ⟨IntervalValues.cast_record _ 98 hl hh,(IntervalValues.pop_frame s al ah bl bh).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=1) installed
    (fun _ _ _ _ _ h => WordService.add_closed code addInstalled h)
    (IntervalValues.bind s hal hah hbl hbh) statement finished

end SynergyC.IntervalAddBody
