/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.MulBody

namespace SynergyC.ZeroBody
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def interval (lo hi : Int) : Value := .record "I" [value lo,value hi]
def zeros : Value := interval 0 0
def initializer : Expr := .record [.nat 0,.nat 0]
def declaration : Decl := {type:="I",name:="r",value:=some initializer,arrayExtent:=none}
def frame (s : State) : State := {s with env:=[]}
def resultFrame (s : State) : State := allocate (frame s) "I" "r" (some zeros)

theorem cast_word_positive (s : State) (fuel : Nat) {n : Int} (hn : Range n) :
    castValue Header.layout s (fuel+1) "U" (value n) = some (value n) := by
  change (do let x ← Scalar.cast type (word n); pure (Value.integer x)) = _
  rw [cast_scalar hn]
  rfl

theorem cast_zeros (s : State) :
    castValue Header.layout s 100 "I" zeros = some zeros := by
  rfl

theorem cast_initial_zeros (s : State) :
    castValue Header.layout s 100 "I"
      (.aggregate [.integer MulBody.intZero,.integer MulBody.intZero]) = some zeros := by
  have h0 : Range 0 := by norm_num [Range]
  have hc : Scalar.cast type MulBody.intZero = some (word 0) := by
    exact Scalar.make_exact (range_scalar h0)
  change (do
    let x ← (do let z ← Scalar.cast type MulBody.intZero; pure (Value.integer z))
    let y ← (do let z ← Scalar.cast type MulBody.intZero; pure (Value.integer z))
    pure (Value.record "I" [x,y])) = _
  rw [hc]
  rfl

theorem eval_initializer (s : State) :
    evalExpr Header.layout RuntimeCore.call 1000 s initializer =
      some (.aggregate [.integer MulBody.intZero,.integer MulBody.intZero],s) := by
  rfl

theorem declared (s : State) :
    declarations Header.layout RuntimeCore.call [declaration] (frame s) = some (resultFrame s) := by
  change (do
    let (v,next) ← evalExpr Header.layout RuntimeCore.call 1000 (frame s) initializer
    let represented ← castValue Header.layout next 100 "I" v
    pure (allocate next "I" "r" (some represented))) = _
  rw [eval_initializer]
  simp only [Bind.bind,Option.bind]
  rw [cast_initial_zeros]
  rfl

theorem eval_local (s : State) :
    Eval Header.layout RuntimeCore.call (.var "r") (resultFrame s) (resultFrame s) zeros := by
  refine ⟨2,?_⟩
  exact TypedFrames.allocate_eval Header.layout RuntimeCore.call 1 (frame s) "I" "r" zeros
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem source_zero (code : List Function) (installed : Generated.f_zero ∈ code) (s : State) :
    SourceCall Header.layout code 1 "zero" [] s zeros s := by
  have statement : Run Header.layout RuntimeCore.call Generated.f_zero.body (frame s)
      (.returned (frame s) zeros) := by
    change Run Header.layout RuntimeCore.call
      (.sequence [.declare [declaration],.returnStmt (.var "r")]) (frame s) (.returned (frame s) zeros)
    apply Loops.StmtRun.sequence
    · apply Loops.SeqRun.next
      · exact Loops.StmtRun.declare (declared s)
      · exact Loops.SeqRun.returned (Loops.StmtRun.returnValue (eval_local s))
    · exact ⟨rfl,(TypedFrames.pop_allocate (frame s) "I" "r" (some zeros)).symm⟩
  have h0 : Range 0 := by norm_num [Range]
  have finished : Finish Header.layout Generated.f_zero s (.returned (frame s) zeros) zeros s := by
    change castValue Header.layout (frame s) 100 "static I" zeros = some zeros ∧ s = popScope s (frame s)
    exact ⟨cast_zeros (frame s),by simp [popScope,frame]⟩
  exact installed_body (cfg:=Header.layout) (code:=code) (rank:=0) installed
    (fun _ _ _ _ _ h=>h) (by simp [bindArgs,frame,Generated.f_zero]) statement finished

end SynergyC.ZeroBody
