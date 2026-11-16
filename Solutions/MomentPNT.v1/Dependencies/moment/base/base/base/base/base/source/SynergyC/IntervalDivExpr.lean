/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalMulExpr

namespace SynergyC.IntervalDivExpr
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def initializer : Expr := .record [
  .binary "/" (.call (.var "mulU") [.field "." (.var "a") "lo",.var "S"])
    (.field "." (.var "b") "hi"),
  .call (.var "ceilDiv") [
    .call (.var "mulU") [.field "." (.var "a") "hi",.var "S"],
    .field "." (.var "b") "lo"]]

theorem eval_initializer {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (blPositive : 0 < bl) (bhPositive : 0 < bh)
    (hl : Range (al*scale)) (hh : Range (ah*scale)) :
    evalExpr Header.layout ArithmeticService.call 1000 (IntervalValues.frame s al ah bl bh) initializer =
      some (.aggregate [value ((al*scale)/bh),value (CeilDivBody.result (ah*scale) bl)],
        IntervalValues.frame s al ah bl bh) := by
  let before := IntervalValues.frame s al ah bl bh
  have hc := WordService.intervalFrameContext maxCtx al ah bl bh
  have lowCall : ArithmeticService.call "mulU" [value al,value scale] before = some (value (al*scale),before) := by
    exact ArithmeticService.complete (op:=.mul) (word al) (word scale) ⟨hal,scale_range,⟨hc⟩,hl⟩
  have highCall : ArithmeticService.call "mulU" [value ah,value scale] before = some (value (ah*scale),before) := by
    exact ArithmeticService.complete (op:=.mul) (word ah) (word scale) ⟨hah,scale_range,⟨hc⟩,hh⟩
  have lowProduct : evalExpr Header.layout ArithmeticService.call 998 before
      (.call (.var "mulU") [.field "." (.var "a") "lo",.var "S"]) =
      some (value (al*scale),before) :=
    ExpressionTemplates.call_two Header.layout ArithmeticService.call
      (IntervalValues.eval_a_lo _ 995 s al ah bl bh)
      (ScaleFrames.eval_scale_interval_frame _ 996 scaleCtx al ah bl bh) lowCall
  have highProduct : evalExpr Header.layout ArithmeticService.call 998 before
      (.call (.var "mulU") [.field "." (.var "a") "hi",.var "S"]) =
      some (value (ah*scale),before) :=
    ExpressionTemplates.call_two Header.layout ArithmeticService.call
      (IntervalValues.eval_a_hi _ 995 s al ah bl bh)
      (ScaleFrames.eval_scale_interval_frame _ 996 scaleCtx al ah bl bh) highCall
  have divide : binaryValue Header.layout before "/" (value (al*scale)) (value bh) =
      some (value ((al*scale)/bh)) := by
    simp only [binaryValue,value,word_div hl hbh bhPositive,Option.bind_some]
    rfl
  have lowExpr := ExpressionTemplates.binary Header.layout ArithmeticService.call
    (by decide) (by decide) (by decide) (by decide) lowProduct
    (IntervalValues.eval_b_hi _ 996 s al ah bl bh) divide
  have ceilCall : ArithmeticService.call "ceilDiv" [value (ah*scale),value bl] before =
      some (value (CeilDivBody.result (ah*scale) bl),before) := by
    exact ArithmeticService.complete (op:=.ceil) (word (ah*scale)) (word bl)
      ⟨hh,hbl,⟨hc⟩,blPositive⟩
  have highExpr := ExpressionTemplates.call_two Header.layout ArithmeticService.call highProduct
    (IntervalValues.eval_b_lo _ 996 s al ah bl bh) ceilCall
  exact ExpressionTemplates.record_two Header.layout ArithmeticService.call lowExpr highExpr

end SynergyC.IntervalDivExpr
