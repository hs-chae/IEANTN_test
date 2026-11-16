/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalValues
import SynergyC.Initialization

namespace SynergyC.UnitBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.ZeroBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- An ordinary source-memory precondition, discharged from the actual
global initialization below. No initial application representation is trusted. -/
structure ScaleContext (s : State) where
  address : Address
  located : s.globals.lookup "S" = some address
  allocated : address.object < s.heap.length
  object : Object
  heap_entry : s.heap[address.object]? = some object
  scalar : object.isArray = false
  contents : read Header.layout s address = some (value (2^128))

def scale : Int := 2^128
def result : Value := interval scale scale
def initializer : Expr := .record [.var "S",.var "S"]
def declaration : Decl := {type:="I",name:="r",value:=some initializer,arrayExtent:=none}
def resultFrame (s : State) : State := allocate (ZeroBody.frame s) "I" "r" (some result)

theorem scale_range : Range scale := by
  change (0:Int) ≤ 2^128 ∧ (2:Int)^128 < 2^512
  decide +kernel

theorem eval_scale (service : Call) (fuel : Nat) {s : State} (ctx : ScaleContext s) :
    evalExpr Header.layout service (fuel+1) (ZeroBody.frame s) (.var "S") =
      some (value scale,ZeroBody.frame s) := by
  have get : getVar (ZeroBody.frame s) "S" = some ctx.address := by
    simp [getVar,ZeroBody.frame,ctx.located]
  have hp : (ZeroBody.frame s).heap[ctx.address.object]? = some ctx.object := ctx.heap_entry
  have hr : read Header.layout (ZeroBody.frame s) ctx.address = some (value scale) := ctx.contents
  rw [evalExpr]
  simp [get,hp,ctx.scalar,hr]

theorem eval_initializer {s : State} (ctx : ScaleContext s) :
    evalExpr Header.layout RuntimeCore.call 1000 (ZeroBody.frame s) initializer =
      some (.aggregate [value scale,value scale],ZeroBody.frame s) := by
  exact ExpressionTemplates.record_two Header.layout RuntimeCore.call
    (eval_scale _ 998 ctx) (eval_scale _ 998 ctx)

theorem declared {s : State} (ctx : ScaleContext s) :
    declarations Header.layout RuntimeCore.call [declaration] (ZeroBody.frame s) = some (resultFrame s) := by
  simp only [declarations,declaration,List.foldlM,eval_initializer ctx,Bind.bind,Option.bind]
  rw [IntervalValues.cast_aggregate _ 98 scale_range scale_range]
  rfl

theorem eval_local (s : State) :
    Eval Header.layout RuntimeCore.call (.var "r") (resultFrame s) (resultFrame s) result := by
  refine ⟨2,?_⟩
  exact TypedFrames.allocate_eval Header.layout RuntimeCore.call 1 (ZeroBody.frame s) "I" "r" result
    (by rfl) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem source_unit (code : List Function) (installed : Generated.f_unit ∈ code)
    {s : State} (ctx : ScaleContext s) :
    SourceCall Header.layout code 1 "unit" [] s result s := by
  have statement : Run Header.layout RuntimeCore.call Generated.f_unit.body (ZeroBody.frame s)
      (.returned (ZeroBody.frame s) result) := by
    change Run Header.layout RuntimeCore.call
      (.sequence [.declare [declaration],.returnStmt (.var "r")])
      (ZeroBody.frame s) (.returned (ZeroBody.frame s) result)
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · exact Loops.StmtRun.declare (declared ctx)
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue (eval_local s))
    · exact ⟨rfl,(TypedFrames.pop_allocate (ZeroBody.frame s) "I" "r" (some result)).symm⟩
  have finished : Finish Header.layout Generated.f_unit s
      (.returned (ZeroBody.frame s) result) result s := by
    change castValue Header.layout (ZeroBody.frame s) 100 "static I" result = some result ∧
      s = popScope s (ZeroBody.frame s)
    exact ⟨IntervalValues.cast_record _ 98 scale_range scale_range,by simp [popScope,ZeroBody.frame]⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=0) installed
    (fun _ _ _ _ _ h=>h) (by simp [bindArgs,ZeroBody.frame,Generated.f_unit]) statement finished

def initialized_scale_context : ScaleContext Initialization.state := {
  address:=⟨0,0,[]⟩
  located:=by rfl
  allocated:=by decide +kernel
  object:={type:="const U",cells:=[some (value (2^128))]}
  heap_entry:=by rfl
  scalar:=by rfl
  contents:=by rfl}

end SynergyC.UnitBody
