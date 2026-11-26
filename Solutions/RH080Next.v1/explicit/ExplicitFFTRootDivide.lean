/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTRootMultiply
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open IncrementSource (base)
open FFT.Limbs

private theorem signed_divide_nonnegative (negative : Bool) (m d : Nat)
    (nonnegative : 0≤ signed negative m) : signed negative (m/d)=(signed negative m)/(d:Int) := by
  cases negative with
  | false=>exact Int.natCast_ediv m d
  | true=>
    have zero : m=0:=by change 0≤-(m:Int) at nonnegative;omega
    subst m;simp [signed]

theorem divided_fixed {data : Nat → Nat} {start : Nat} {value : Int} (h : FixedValue data start value)
    (d : Nat) (positive : 0< d) (nonnegative : 0≤ value) :
    FixedValue (DivideSource.roundedData data start 5 d 0) start (value/(d:Int)) := by
  have signSame : DivideSource.roundedData data start 5 d 0 (start+5)=data (start+5):=
    DivideSource.roundedData_outside _ _ _ _ _ _ (by omega)
  have magnitudeSame:=DivideSource.roundedData_value data start 5 d 0 positive h.digits
  have rawNonnegative : 0≤ CanonicalSource.represented data start:=by rw [h.represented];exact nonnegative
  refine ⟨DivideSource.roundedData_digits _ _ _ _ _ positive h.digits,by rw [signSame];exact h.sign,?_⟩
  have norm : magnitude 1000000000 5 (fun k=>DivideSource.roundedData data start 5 d 0 (start+k))=
      magnitude 1000000000 5 (fun k=>data (start+k))/d:=by simpa only [not_lt_zero,ite_false,base] using magnitudeSame
  unfold CanonicalSource.represented
  rw [signSame,norm,signed_divide_nonnegative _ _ _ rawNonnegative]
  exact congrArg (fun v=>v/(d:Int)) h.represented

def floorDivideStatement (p : Param) (offset : Nat) (divisor : Expr) : Stmt:=.expression
  (.call "divide_small" [pointerExpr p offset,.literal (.integer 5 "ULL"),divisor,.literal (.integer 0 "ULL")])

/-- The source's divide_small floor instruction, restricted to the actual
nonnegative Taylor terms. Negative signed floor is not silently inferred from
unsigned magnitude division. -/
theorem floor_divide_execution {F : Type} (context : Context F)
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    {before : State F} {input : Input} {owner statusId : Nat} {ids : Param → Nat} {data : Nat → Nat}
    (h : ScaleView before input owner statusId ids data) (scope : owner≤ before.scope)
    (p : Param) (hp : PointerParam p) (offset d : Nat) (expression : Expr)
    (read : Eval context before expression (.integer (integer64 d)) before)
    (expressionPure : SourcePure.CallFree expression)
    (value : Int) (fixed : FixedValue data (pointerStart input p+offset) value)
    (nonnegative : 0≤ value) (positive : 0< d) (small : d< base)
    (bound : pointerStart input p+offset+6≤ input.layout.size) (offset64 : offset<2^64) :
    ∃after,Exec context before (floorDivideStatement p offset expression) .normal after ∧
      Every context before (floorDivideStatement p offset expression) .normal after ∧
      ScaleView after input owner statusId ids (DivideSource.roundedData data (pointerStart input p+offset) 5 d 0) ∧
      FixedValue (DivideSource.roundedData data (pointerStart input p+offset) 5 d 0) (pointerStart input p+offset) (value/(d:Int)) ∧
      IncrementSource.FullCallerFrame before after input.layout.object := by
  obtain ⟨after,called,post,frame⟩:=DivideSource.divide_small_call context selected incrementSelected before
    input.layout.object input.layout.size (pointerStart input p+offset) 5 d 0 data h.params.well h.params.array
    (by omega) (by omega) fixed.digits positive small (by omega)
  have args : Args context before [pointerExpr p offset,.literal (.integer 5 "ULL"),expression,.literal (.integer 0 "ULL")]
      [.pointer (wordPointer input.layout.object (pointerStart input p+offset)),.integer (integer64 5),.integer (integer64 d),.integer (integer64 0)] before:=by
    apply Args.ordered (order:=[(0,pointerExpr p offset),(1,.literal (.integer 5 "ULL")),(2,expression),(3,.literal (.integer 0 "ULL"))])
      (evaluated:=[(0,.pointer (wordPointer input.layout.object (pointerStart input p+offset))),(1,.integer (integer64 5)),(2,.integer (integer64 d)),(3,.integer (integer64 0))])
    · exact List.Perm.refl _
    · exact .cons (pointer_eval context h.params p hp offset (by omega) offset64)
        (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl))
          (.cons read (.cons (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) .nil)))
    · change List.Forall₂ _ [0,1,2,3] _;exact .cons rfl (.cons rfl (.cons rfl (.cons rfl .nil)))
  have everyStep : Every context before (floorDivideStatement p offset expression) .normal after:=by
    apply every_expression_call (args:=args) (callee:=fun state output actual=>DivideSource.returned_call_unique selected incrementSelected called actual)
    intro e member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl|rfl|rfl
    · exact pointer_expr_pure _ _
    · trivial
    · exact expressionPure
    · trivial
  exact ⟨after,.expression (.call args called),everyStep,h.reframe post frame.environment scope frame.scope frame.well frame.objects,
    divided_fixed fixed d positive nonnegative,frame⟩

#print axioms divided_fixed
#print axioms floor_divide_execution
end RH080Next.FFTPV.RootSource
