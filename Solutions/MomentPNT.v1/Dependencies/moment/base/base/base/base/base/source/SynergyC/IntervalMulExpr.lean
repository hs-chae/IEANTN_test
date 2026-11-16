/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ArithmeticService
import SynergyC.ScaleFrames
import ScopedC.ExpressionBinary

namespace SynergyC.IntervalMulExpr
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def initializer : Expr := .record [
  .binary "/" (.call (.var "mulU") [.field "." (.var "a") "lo",.field "." (.var "b") "lo"]) (.var "S"),
  .call (.var "ceilDiv") [
    .call (.var "mulU") [.field "." (.var "a") "hi",.field "." (.var "b") "hi"],.var "S"]]

theorem scale_positive : 0 < scale := by change (0:Int) < 2^128; positivity

theorem eval_initializer {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {al ah bl bh : Int} (hal : Range al) (hah : Range ah) (hbl : Range bl) (hbh : Range bh)
    (hl : Range (al*bl)) (hh : Range (ah*bh)) :
    evalExpr Header.layout ArithmeticService.call 1000 (IntervalValues.frame s al ah bl bh) initializer =
      some (.aggregate [value ((al*bl)/scale),value (CeilDivBody.result (ah*bh) scale)],
        IntervalValues.frame s al ah bl bh) := by
  let before := IntervalValues.frame s al ah bl bh
  have hc := WordService.intervalFrameContext maxCtx al ah bl bh
  have lowCall : ArithmeticService.call "mulU" [value al,value bl] before = some (value (al*bl),before) := by
    exact ArithmeticService.complete (op:=.mul) (word al) (word bl) ⟨hal,hbl,⟨hc⟩,hl⟩
  have highCall : ArithmeticService.call "mulU" [value ah,value bh] before = some (value (ah*bh),before) := by
    exact ArithmeticService.complete (op:=.mul) (word ah) (word bh) ⟨hah,hbh,⟨hc⟩,hh⟩
  have lowProduct : evalExpr Header.layout ArithmeticService.call 998 before
      (.call (.var "mulU") [.field "." (.var "a") "lo",.field "." (.var "b") "lo"]) =
      some (value (al*bl),before) :=
    ExpressionTemplates.call_two Header.layout ArithmeticService.call
      (IntervalValues.eval_a_lo _ 995 s al ah bl bh) (IntervalValues.eval_b_lo _ 995 s al ah bl bh) lowCall
  have highProduct : evalExpr Header.layout ArithmeticService.call 998 before
      (.call (.var "mulU") [.field "." (.var "a") "hi",.field "." (.var "b") "hi"]) =
      some (value (ah*bh),before) :=
    ExpressionTemplates.call_two Header.layout ArithmeticService.call
      (IntervalValues.eval_a_hi _ 995 s al ah bl bh) (IntervalValues.eval_b_hi _ 995 s al ah bl bh) highCall
  have divide : binaryValue Header.layout before "/" (value (al*bl)) (value scale) =
      some (value ((al*bl)/scale)) := by
    simp only [binaryValue,value,word_div hl scale_range scale_positive,Option.bind_some]
    rfl
  have lowExpr := ExpressionTemplates.binary Header.layout ArithmeticService.call
    (by decide) (by decide) (by decide) (by decide) lowProduct
    (ScaleFrames.eval_scale_interval_frame _ 997 scaleCtx al ah bl bh) divide
  have ceilCall : ArithmeticService.call "ceilDiv" [value (ah*bh),value scale] before =
      some (value (CeilDivBody.result (ah*bh) scale),before) := by
    exact ArithmeticService.complete (op:=.ceil) (word (ah*bh)) (word scale)
      ⟨hh,scale_range,⟨hc⟩,scale_positive⟩
  have highExpr := ExpressionTemplates.call_two Header.layout ArithmeticService.call highProduct
    (ScaleFrames.eval_scale_interval_frame _ 997 scaleCtx al ah bl bh) ceilCall
  exact ExpressionTemplates.record_two Header.layout ArithmeticService.call lowExpr highExpr

end SynergyC.IntervalMulExpr
