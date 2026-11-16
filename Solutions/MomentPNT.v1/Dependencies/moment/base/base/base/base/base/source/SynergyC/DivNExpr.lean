/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.DivNFrames

namespace SynergyC.DivNExpr
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0

def initializer : Expr := .record [
  .binary "/" (.field "." (.var "a") "lo") (.var "n"),
  .call (.var "ceilDiv") [.field "." (.var "a") "hi",.var "n"]]

theorem eval_initializer {s : State} (ctx : MaxContext s)
    {al ah n : Int} (hal : Range al) (hah : Range ah) (hn : SmallWord.Range n) (hn0 : 0 < n) :
    evalExpr Header.layout ArithmeticService.call 1000 (DivNFrames.frame s al ah n) initializer =
      some (.aggregate [value (al/n),value (CeilDivBody.result ah n)],DivNFrames.frame s al ah n) := by
  let before := DivNFrames.frame s al ah n
  have divide : binaryValue Header.layout before "/" (value al) (SmallWord.value n) =
      some (value (al/n)) := by
    simp only [binaryValue,value,SmallWord.value,SmallWord.wide_div hal hn hn0,Option.bind_some]
    rfl
  have low := ExpressionTemplates.binary Header.layout ArithmeticService.call
    (by decide) (by decide) (by decide) (by decide)
    (DivNFrames.eval_lo _ 996 s al ah n) (DivNFrames.eval_n _ 997 s al ah n) divide
  have call : ArithmeticService.call "ceilDiv" [value ah,SmallWord.value n] before =
      some (value (CeilDivBody.result ah n),before) := by
    exact ArithmeticService.complete (op:=.ceil) (word ah) (SmallWord.scalar n)
      ⟨hah,SmallWord.wide_range hn,⟨DivNFrames.maxContext ctx al ah n⟩,hn0⟩
  have high := ExpressionTemplates.call_two Header.layout ArithmeticService.call
    (DivNFrames.eval_hi _ 996 s al ah n) (DivNFrames.eval_n _ 997 s al ah n) call
  exact ExpressionTemplates.record_two Header.layout ArithmeticService.call low high

end SynergyC.DivNExpr
