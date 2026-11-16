/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.RatExpr

namespace SynergyC.RatBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def declaration : Decl := {type:="I",name:="r",value:=some RatExpr.initializer,arrayExtent:=none}
def result (n d : Int) : Value := interval ((n*scale)/d) (CeilDivBody.result (n*scale) d)
def resultFrame (s : State) (n d : Int) : State :=
  allocate (RatFrames.withProduct s n d) "I" "r" (some (result n d))

theorem declared {s : State} (maxCtx : MaxContext s)
    {n d : Int} (hd : Range d) (hdPositive : 0 < d) (fit : Range (n*scale)) :
    declarations Header.layout ArithmeticService.call [declaration] (RatFrames.withProduct s n d) =
      some (resultFrame s n d) := by
  simp only [declarations,declaration,List.foldlM,RatExpr.eval_initializer maxCtx hd hdPositive fit,
    Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 (quotient_range fit hdPositive)
    (CeilDivBody.result_range fit hdPositive)]
  rfl

theorem source_rat (code : List Function) (installed : Generated.f_rat ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (mulInstalled : Generated.f_mulU ∈ code)
    (ceilInstalled : Generated.f_ceilDiv ∈ code) (checked : ArithmeticService.parameters code = true)
    {s : State} (maxCtx : MaxContext s) (scaleCtx : ScaleContext s)
    {n d : Int} (hn : Range n) (hd : Range d) (hdPositive : 0 < d) (fit : Range (n*scale)) :
    SourceCall Header.layout code 3 "rat" [value n,value d] s (result n d) s := by
  let before := RatFrames.frame s n d
  have localEval : Eval Header.layout ArithmeticService.call (.var "r")
      (resultFrame s n d) (resultFrame s n d) (result n d) := by
    refine ⟨2,?_⟩
    exact TypedFrames.allocate_eval Header.layout ArithmeticService.call 1 (RatFrames.withProduct s n d)
      "I" "r" (result n d) (by rfl) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have body : Run Header.layout ArithmeticService.call Generated.f_rat.body before
      (.returned before (result n d)) := by
    change Run Header.layout ArithmeticService.call
      (.sequence [.declare [RatExpr.productDeclaration],.declare [declaration],.returnStmt (.var "r")])
      before (.returned before (result n d))
    apply Loops.StmtRun.sequence
    · exact Loops.SeqRun.next
        (Loops.StmtRun.declare (RatExpr.declared_product maxCtx scaleCtx hn fit))
        (Loops.SeqRun.next (Loops.StmtRun.declare (declared maxCtx hd hdPositive fit))
          (Loops.SeqRun.returned (Loops.StmtRun.returnValue localEval)))
    · constructor
      · rfl
      · simp [before,popScope,resultFrame,RatFrames.withProduct,allocate,List.take_append]
  have finish : Finish Header.layout Generated.f_rat s
      (.returned before (result n d)) (result n d) s := by
    change castValue Header.layout before 100 "static I" (result n d) =
      some (result n d) ∧ s = popScope s before
    exact ⟨IntervalValues.cast_record _ 98 (quotient_range fit hdPositive)
      (CeilDivBody.result_range fit hdPositive),(RatFrames.pop_frame s n d).symm⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=2) installed
    (fun _ _ _ _ _ h=>ArithmeticService.closed code addInstalled mulInstalled ceilInstalled checked h)
    (RatFrames.bind s hn hd) body finish

end SynergyC.RatBody
