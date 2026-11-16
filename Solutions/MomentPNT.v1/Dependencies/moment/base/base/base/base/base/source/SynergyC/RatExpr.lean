/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.RatFrames

namespace SynergyC.RatExpr
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def product : Expr := .call (.var "mulU") [.var "n",.var "S"]
def productDeclaration : Decl := {type:="U",name:="a",value:=some product,arrayExtent:=none}
def initializer : Expr := .record [
  .binary "/" (.var "a") (.var "d"),.call (.var "ceilDiv") [.var "a",.var "d"]]

theorem eval_product {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {n d : Int} (hn : Range n) (fit : Range (n*scale)) :
    evalExpr Header.layout ArithmeticService.call 1000 (RatFrames.frame s n d) product =
      some (value (n*scale),RatFrames.frame s n d) := by
  have call : ArithmeticService.call "mulU" [value n,value scale] (RatFrames.frame s n d) =
      some (value (n*scale),RatFrames.frame s n d) := by
    exact ArithmeticService.complete (op:=.mul) (word n) (word scale)
      ⟨hn,scale_range,⟨RatFrames.maxContext maxCtx n d⟩,fit⟩
  exact ExpressionTemplates.call_two Header.layout ArithmeticService.call
    (RatFrames.eval_n _ 998 s n d) (RatFrames.eval_scale _ 998 scaleCtx n d) call

theorem declared_product {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {n d : Int} (hn : Range n) (fit : Range (n*scale)) :
    declarations Header.layout ArithmeticService.call [productDeclaration] (RatFrames.frame s n d) =
      some (RatFrames.withProduct s n d) := by
  simp only [declarations,productDeclaration,List.foldlM,eval_product maxCtx scaleCtx hn fit,
    Bind.bind,Option.bind]
  rw [cast_word _ fit]
  rfl

theorem eval_initializer {s : State} (maxCtx : MaxContext s)
    {n d : Int} (hd : Range d) (hdPositive : 0 < d) (fit : Range (n*scale)) :
    evalExpr Header.layout ArithmeticService.call 1000 (RatFrames.withProduct s n d) initializer =
      some (.aggregate [value ((n*scale)/d),value (CeilDivBody.result (n*scale) d)],
        RatFrames.withProduct s n d) := by
  let before := RatFrames.withProduct s n d
  have divide : binaryValue Header.layout before "/" (value (n*scale)) (value d) =
      some (value ((n*scale)/d)) := by
    simp only [binaryValue,value,word_div fit hd hdPositive,Option.bind_some]
    rfl
  have low := ExpressionTemplates.binary Header.layout ArithmeticService.call
    (by decide) (by decide) (by decide) (by decide)
    (RatFrames.eval_a _ 997 s n d) (RatFrames.eval_d _ 997 s n d) divide
  have call : ArithmeticService.call "ceilDiv" [value (n*scale),value d] before =
      some (value (CeilDivBody.result (n*scale) d),before) := by
    exact ArithmeticService.complete (op:=.ceil) (word (n*scale)) (word d)
      ⟨fit,hd,⟨RatFrames.productMaxContext maxCtx n d⟩,hdPositive⟩
  have high := ExpressionTemplates.call_two Header.layout ArithmeticService.call
    (RatFrames.eval_a _ 997 s n d) (RatFrames.eval_d _ 997 s n d) call
  exact ExpressionTemplates.record_two Header.layout ArithmeticService.call low high

end SynergyC.RatExpr
